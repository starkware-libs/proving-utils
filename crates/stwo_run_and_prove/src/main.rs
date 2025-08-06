use cairo_air::PreProcessedTraceVariant;
use cairo_air::utils::ProofFormat;
use cairo_air::verifier::verify_cairo;
use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_cairo_run_config, get_program, get_program_input};
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use clap::Parser;
#[cfg(test)]
use mockall::automock;
use serde::Serialize;
use std::env;
use std::io::Write;
use std::path::PathBuf;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_adapter::adapter::adapter;
use stwo_cairo_adapter::vm_import::VmImportError;
use stwo_cairo_prover::prover::{
    ChannelHash, ProverParameters, default_prod_prover_parameters, prove_cairo,
};
use stwo_cairo_prover::stwo_prover::core::backend::BackendForChannel;
use stwo_cairo_prover::stwo_prover::core::backend::simd::SimdBackend;
use stwo_cairo_prover::stwo_prover::core::channel::MerkleChannel;
use stwo_cairo_prover::stwo_prover::core::pcs::PcsConfig;
use stwo_cairo_prover::stwo_prover::core::prover::ProvingError;
use stwo_cairo_prover::stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo_cairo_prover::stwo_prover::core::vcs::ops::MerkleHasher;
use stwo_cairo_prover::stwo_prover::core::vcs::poseidon252_merkle::Poseidon252MerkleChannel;
use stwo_cairo_serialize::CairoSerialize;
use stwo_cairo_utils::file_utils::{IoErrorWithPath, create_file, read_to_string};
use thiserror::Error;
use tracing::{error, info, warn};

type OutputVec = Vec<[u32; 8]>;

fn parse_usize_ge1(s: &str) -> Result<usize, String> {
    let v: usize = s.parse().map_err(|_| "must be a number".to_string())?;
    if v >= 1 {
        Ok(v)
    } else {
        Err("must be >= 1".into())
    }
}

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "program", help = "Absolute path to the compiled program.")]
    program: PathBuf,
    #[clap(
        long = "program_input",
        help = "Absolute path to the program input file."
    )]
    program_input: Option<PathBuf>,
    // The path to the JSON file containing the prover parameters (optional).
    // The expected file format is:
    //     {
    //         "channel_hash":"blake2s",
    //         "pcs_config": {
    //             "pow_bits": 26,
    //             "fri_config": {
    //                 "log_last_layer_degree_bound": 0,
    //                 "log_blowup_factor": 1,
    //                 "n_queries": 70
    //             }
    //         },
    //         "preprocessed_trace": "canonical_without_pedersen"
    //     }
    //
    // Default parameters are chosen to ensure 96 bits of security.
    #[clap(
        long = "prover_params_json",
        help = "Absolute path to the JSON file containing the prover parameters."
    )]
    prover_params_json: Option<PathBuf>,
    #[clap(
        long = "proofs_dir",
        help = "Absolute path to the output directory where the generated proofs will be saved (may include
    multiple proofs from repeated attempts)."
    )]
    proofs_dir: PathBuf,
    #[clap(long, value_enum, default_value_t = ProofFormat::CairoSerde, help = "Json or cairo-serde.")]
    proof_format: ProofFormat,
    #[clap(
        long = "n_proof_attempts",
        help = "Number of attempts for proving, in case the proof verification fails.",
        default_value_t = 1usize,
        requires = "verify",
        value_parser = parse_usize_ge1
    )]
    n_proof_attempts: usize,
    #[clap(long = "verify", help = "Should verify the generated proof.")]
    verify: bool,
    #[clap(
        long = "program_output",
        help = "Optional absolute path for the program output."
    )]
    program_output: Option<PathBuf>,
}

#[derive(Debug, Error)]
enum StwoRunAndProveError {
    #[error(transparent)]
    Cli(#[from] clap::Error),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    VmImport(#[from] VmImportError),
    #[error(transparent)]
    CairoRun(Box<CairoRunError>),
    #[error(transparent)]
    Program(#[from] ProgramError),
    #[error(transparent)]
    Runner(#[from] RunnerError),
    #[error(transparent)]
    File(#[from] IoErrorWithPath),
    #[error(transparent)]
    Serializing(#[from] sonic_rs::error::Error),
    #[error(transparent)]
    Proving(#[from] ProvingError),
    #[error("cairo verification failed.")]
    Verification,
}

// Implement From<Box<CairoRunError>> manually
impl From<CairoRunError> for StwoRunAndProveError {
    fn from(err: CairoRunError) -> Self {
        StwoRunAndProveError::CairoRun(Box::new(err))
    }
}

struct ProveConfig {
    proofs_dir: PathBuf,
    proof_format: ProofFormat,
    verify: bool,
    n_proof_attempts: usize,
    prover_params_json: Option<PathBuf>,
}

struct CairoProverInputs {
    prover_input: ProverInput,
    pcs_config: PcsConfig,
    preprocessed_trace: PreProcessedTraceVariant,
}

fn main() -> Result<(), StwoRunAndProveError> {
    let args = match Args::try_parse_from(env::args()) {
        Ok(args) => args,
        Err(err) => err.exit(),
    };
    let prove_config = ProveConfig {
        verify: args.verify,
        proofs_dir: args.proofs_dir,
        proof_format: args.proof_format,
        n_proof_attempts: args.n_proof_attempts,
        prover_params_json: args.prover_params_json,
    };

    let stwo_prover = Box::new(StwoProverEntryPoint);
    stwo_run_and_prove(
        args.program,
        args.program_input,
        args.program_output,
        prove_config,
        stwo_prover,
    )?;
    Ok(())
}

/// Runs the program and generates a proof for it.
/// Saves the proof to the specified output dir (may include multiple proofs from repeated
/// attempts). If `program_output` is provided, saves the program output to that path.
fn stwo_run_and_prove(
    program: PathBuf,
    program_input: Option<PathBuf>,
    program_output: Option<PathBuf>,
    prove_config: ProveConfig,
    prover: Box<dyn ProverTrait>,
) -> Result<usize, StwoRunAndProveError> {
    let cairo_run_config = get_cairo_run_config(
        // we don't use dynamic layout in stwo
        &None,
        LayoutName::all_cairo_stwo,
        true,
        // in stwo when proof_mode==true, trace padding is redundant work
        true,
        // we allow missing builtins because all_cairo_stwo doesn't include all builtins, and
        // the bootloader will simulate the missing builtins.
        true,
        // we don't need to relocate memory in the VM because we later call the adapter that does
        // relocation.
        false,
    )?;

    let program = get_program(program.as_path())?;
    let program_input = get_program_input(&program_input)?;
    info!("Running cairo run program.");
    let runner = cairo_run_program(&program, program_input, cairo_run_config)?;
    let mut prover_input_info = runner.get_prover_input_info()?;
    info!("Adapting prover input.");
    let prover_input = adapter(&mut prover_input_info)?;
    let (successful_proof_attempt, output_vec) =
        prove_with_retries(prover_input, prove_config, prover)?;

    if let Some(output_path) = program_output {
        save_output_to_file(output_vec, output_path)?;
    }

    Ok(successful_proof_attempt)
}

/// Prepares the prover parameters and generates proof given the prover input and parameters.
/// Verifies the proof in case the respective flag is set.
/// In case the proof verification fails, it retries up to `n_proof_attempts` times.
/// Returns the program utput.
fn prove_with_retries(
    prover_input: ProverInput,
    prove_config: ProveConfig,
    prover: Box<dyn ProverTrait>,
) -> Result<(usize, OutputVec), StwoRunAndProveError> {
    let ProverParameters {
        channel_hash,
        pcs_config,
        preprocessed_trace,
    } = match prove_config.prover_params_json {
        Some(ref path) => sonic_rs::from_str(&read_to_string(path)?)?,
        None => default_prod_prover_parameters(),
    };

    let cairo_prover_inputs = CairoProverInputs {
        prover_input: prover_input.clone(),
        pcs_config,
        preprocessed_trace,
    };

    // create the directory if it doesn't exist
    std::fs::create_dir_all(&prove_config.proofs_dir)?;
    let proof_format = prove_config.proof_format;

    for i in 1..prove_config.n_proof_attempts + 1 {
        info!(
            "Attempting to generate proof {}/{}.",
            i, prove_config.n_proof_attempts
        );
        let proof_file_path = prove_config.proofs_dir.join(format!("proof_{}", i));

        match prover.choose_channel_and_prove(
            &cairo_prover_inputs,
            proof_file_path,
            &proof_format,
            channel_hash,
            prove_config.verify,
        ) {
            Ok(output_values) => {
                info!(
                    "Proof generated and verified successfully on attempt {}/{}",
                    i, prove_config.n_proof_attempts
                );
                return Ok((i, output_values));
            }

            Err(StwoRunAndProveError::Verification) => {
                if i < prove_config.n_proof_attempts {
                    warn!(
                        "Proof verification failed on attempt {}/{}. Retrying.",
                        i, prove_config.n_proof_attempts
                    );
                    continue;
                }
                error!(
                    "Proof verification failed on last attempt - {}/{}.",
                    i, prove_config.n_proof_attempts
                );
                return Err(StwoRunAndProveError::Verification);
            }

            Err(e) => return Err(e),
        }
    }

    panic!("Should not reach here, n_proof_attempts should be at least 1.");
}

/// Chooses the appropriate channel based on the `channel_hash` and generates a proof.
fn choose_channel_and_prove(
    cairo_prover_inputs: &CairoProverInputs,
    proof_file_path: PathBuf,
    proof_format: &ProofFormat,
    channel_hash: ChannelHash,
    verify: bool,
) -> Result<OutputVec, StwoRunAndProveError> {
    match channel_hash {
        ChannelHash::Blake2s => prove::<Blake2sMerkleChannel>(
            cairo_prover_inputs,
            proof_file_path,
            proof_format,
            verify,
        ),
        ChannelHash::Poseidon252 => prove::<Poseidon252MerkleChannel>(
            cairo_prover_inputs,
            proof_file_path,
            proof_format,
            verify,
        ),
    }
}

#[cfg_attr(test, automock)]
trait ProverTrait {
    fn choose_channel_and_prove(
        &self,
        cairo_prover_inputs: &CairoProverInputs,
        proof_file_path: PathBuf,
        proof_format: &ProofFormat,
        channel_hash: ChannelHash,
        verify: bool,
    ) -> Result<OutputVec, StwoRunAndProveError>;
}

struct StwoProverEntryPoint;

impl ProverTrait for StwoProverEntryPoint {
    fn choose_channel_and_prove(
        &self,
        cairo_prover_inputs: &CairoProverInputs,
        proof_file_path: PathBuf,
        proof_format: &ProofFormat,
        channel_hash: ChannelHash,
        verify: bool,
    ) -> Result<OutputVec, StwoRunAndProveError> {
        choose_channel_and_prove(
            cairo_prover_inputs,
            proof_file_path,
            proof_format,
            channel_hash,
            verify,
        )
    }
}

/// Generates a proof for the given prover input and parameters, using the specified Merkle channel.
/// Serializes the proof as cairo-serde or JSON and write to the proof path.
/// Verifies the proof if the `verify` flag is set.
/// Returns the program output.
fn prove<MC: MerkleChannel>(
    cairo_prover_inputs: &CairoProverInputs,
    proof_file_path: PathBuf,
    proof_format: &ProofFormat,
    verify: bool,
) -> Result<OutputVec, StwoRunAndProveError>
where
    SimdBackend: BackendForChannel<MC>,
    MC::H: Serialize,
    <MC::H as MerkleHasher>::Hash: CairoSerialize,
{
    let proof = prove_cairo::<MC>(
        cairo_prover_inputs.prover_input.clone(),
        cairo_prover_inputs.pcs_config,
        cairo_prover_inputs.preprocessed_trace,
    )?;

    let mut proof_file = create_file(&proof_file_path)?;

    match proof_format {
        ProofFormat::Json => {
            let serialized = sonic_rs::to_string_pretty(&proof)?;
            proof_file.write_all(serialized.as_bytes())?;
        }
        ProofFormat::CairoSerde => {
            let mut serialized: Vec<starknet_ff::FieldElement> = Vec::new();
            CairoSerialize::serialize(&proof, &mut serialized);
            let hex_strings: Vec<String> = serialized
                .into_iter()
                .map(|felt| format!("0x{:x}", felt))
                .collect();
            let serialized_hex = sonic_rs::to_string_pretty(&hex_strings)?;
            proof_file.write_all(serialized_hex.as_bytes())?;
        }
    }

    let output_addresses_and_values = proof.claim.public_data.public_memory.output.clone();

    if verify {
        // We want to map this error to `StwoRunAndProveError::Verification` because we intend to
        // retry the proof generation in case of a verification failure. In the calling function we
        // assume this specific error type, so if we don't map it, and the error type returned by
        // `verify_cairo` changes, it will break the retry logic.
        verify_cairo::<MC>(proof, cairo_prover_inputs.preprocessed_trace)
            .map_err(|_| StwoRunAndProveError::Verification)?;
    }

    let output_values = output_addresses_and_values
        .into_iter()
        .map(|(_, value)| value)
        .collect();

    Ok(output_values)
}

/// Saves the program output to the specified output path as [u32; 8] values,
/// that will be converted to [u256] in the Prover service.
fn save_output_to_file(
    output_vec: OutputVec,
    output_path: PathBuf,
) -> Result<(), StwoRunAndProveError> {
    info!("Saving program output to: {:?}", output_path);
    let serialized_output = sonic_rs::to_string(&output_vec)?;
    std::fs::write(output_path, serialized_output)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::{NamedTempFile, TempDir, TempPath};

    const ARRAY_SUM_EXPECTED_OUTPUT: [u32; 8] = [50, 0, 0, 0, 0, 0, 0, 0];
    const RESOURCES_PATH: &str = "resources";
    const PROGRAM_FILE_NAME: &str = "array_sum.json";
    const PROVER_PARAMS_FILE_NAME: &str = "prover_params.json";
    const EXPECTED_PROOF_FILE_NAME: &str = "array_sum_proof";
    const FIRST_PROOF_FILE_NAME: &str = "proof_1";

    fn get_path(file_name: &str) -> PathBuf {
        let current_path = env::current_dir().expect("failed to get current directory");
        current_path.join(RESOURCES_PATH).join(file_name)
    }

    fn is_file_empty(path: &PathBuf) -> std::io::Result<bool> {
        let metadata = fs::metadata(path)?;
        Ok(metadata.len() == 0)
    }

    fn prepare_args(n_proof_attempts: usize) -> (Args, TempPath, TempDir) {
        let program_output_tempfile = NamedTempFile::new()
            .expect("Failed to create temp file for program output")
            .into_temp_path();
        let proofs_tempdir = TempDir::new().expect("Failed to create temp directory for proofs");
        let args = Args {
            program: get_path(PROGRAM_FILE_NAME),
            program_input: None,
            program_output: Some(program_output_tempfile.to_path_buf()),
            prover_params_json: Some(get_path(PROVER_PARAMS_FILE_NAME)),
            proofs_dir: proofs_tempdir.path().to_path_buf(),
            proof_format: ProofFormat::CairoSerde,
            n_proof_attempts,
            verify: true,
        };

        (args, program_output_tempfile, proofs_tempdir)
    }

    fn run_stwo_run_and_prove(
        args: Args,
        prover: Box<dyn ProverTrait>,
    ) -> Result<usize, StwoRunAndProveError> {
        let prove_config = ProveConfig {
            verify: args.verify,
            proofs_dir: args.proofs_dir,
            proof_format: args.proof_format,
            n_proof_attempts: args.n_proof_attempts,
            prover_params_json: args.prover_params_json,
        };

        stwo_run_and_prove(
            args.program,
            args.program_input,
            args.program_output.clone(),
            prove_config,
            prover,
        )
    }

    fn run_with_successful_mock_prover(n_proof_attempts: usize) -> (TempPath, TempDir) {
        let (args, program_output_tempfile, proofs_tempdir) = prepare_args(n_proof_attempts);

        let mut mock_prover = Box::new(MockProverTrait::new());
        mock_prover
            .expect_choose_channel_and_prove()
            .times(1)
            .returning(move |_, proof_file, _, _, _| {
                let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
                fs::copy(&expected_proof_file, &proof_file).expect("Failed to copy proof file.");
                Ok(vec![ARRAY_SUM_EXPECTED_OUTPUT])
            });

        let successful_proof_attempt =
            run_stwo_run_and_prove(args, mock_prover).expect("failed to run stwo_run_and_prove");

        assert_eq!(
            successful_proof_attempt, 1,
            "successful proof attempt should be 1, but got {:?}",
            successful_proof_attempt
        );

        (program_output_tempfile, proofs_tempdir)
    }

    fn run_with_verification_error_mock_prover(n_proof_attempts: usize) -> (TempPath, TempDir) {
        let (args, program_output_tempfile, proofs_tempdir) = prepare_args(n_proof_attempts);

        let mut mock_prover = Box::new(MockProverTrait::new());
        mock_prover
            .expect_choose_channel_and_prove()
            .times(n_proof_attempts)
            .returning(move |_, proof_file, _, _, _| {
                let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
                fs::copy(&expected_proof_file, &proof_file).expect("Failed to copy proof file.");
                Err(StwoRunAndProveError::Verification)
            });

        let result = run_stwo_run_and_prove(args, mock_prover);
        assert!(
            matches!(result, Err(StwoRunAndProveError::Verification)),
            "run and prove should return StwoRunAndProveError::Verification error but got: {:?}",
            result,
        );

        (program_output_tempfile, proofs_tempdir)
    }

    #[test]
    fn test_stwo_run_and_prove() {
        let (output_temp_file, proofs_temp_dir) = run_with_successful_mock_prover(1);

        // Verifying the proof content.
        let proof_file = proofs_temp_dir
            .path()
            .to_path_buf()
            .join(FIRST_PROOF_FILE_NAME);
        let proof_content = std::fs::read_to_string(proof_file).expect("Failed to read proof file");
        let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
        let expected_proof_content = std::fs::read_to_string(expected_proof_file)
            .expect("Failed to read expected proof file");
        assert_eq!(
            proof_content, expected_proof_content,
            "Proof content does not match expected proof content"
        );

        // Verifying the proof output.
        let output_content =
            std::fs::read_to_string(output_temp_file).expect("Failed to read output file");
        let output_vec: OutputVec =
            sonic_rs::from_str(&output_content).expect("Failed to parse output");
        assert_eq!(
            output_vec[0], ARRAY_SUM_EXPECTED_OUTPUT,
            "Expected output to be {:?}",
            ARRAY_SUM_EXPECTED_OUTPUT
        );
    }

    #[test]
    fn test_stwo_run_and_prove_retries() {
        let n_proof_attempts = 3;
        let (output_temp_file, proofs_temp_dir) =
            run_with_verification_error_mock_prover(n_proof_attempts);
        let proofs_dir = proofs_temp_dir.path().to_path_buf();

        for i in 1..n_proof_attempts + 1 {
            let proof_file = proofs_dir.join(format!("proof_{}", i));
            assert!(
                proof_file.exists(),
                "Proof file {:?} should exist after running with verifier failures",
                i,
            );
        }
        assert!(
            is_file_empty(&output_temp_file.to_path_buf()).unwrap(),
            "Output file should be empty after running with verifier failures",
        );
    }
}

// TODO(nitsan): Tests -
// add an inner test to choose_channel_and_prove
