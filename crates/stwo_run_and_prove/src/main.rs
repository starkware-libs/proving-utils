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
use serde::Serialize;
use std::env;
use std::fs::File;
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

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    // cairo run args:
    #[clap(long = "program", help = "Path to the compiled program")]
    program: PathBuf,
    #[clap(long = "program_input", help = "Path to the program input file.")]
    program_input: Option<PathBuf>,

    // prove args:

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
        help = "The path to the JSON file containing the prover parameters."
    )]
    prover_params_json: Option<PathBuf>,
    #[clap(
        long = "proofs_dir",
        help = "Path to the output directory where the generated proofs will be saved (may include
    multiple proofs from repeated attempts)."
    )]
    proofs_dir: PathBuf,
    #[clap(long, value_enum, default_value_t = ProofFormat::Json, help = "Json or cairo-serde.")]
    proof_format: ProofFormat,
    #[clap(
        long = "n_proof_attempts",
        help = "Number of attempts for proving, in case the proof verification fails.",
        default_value_t = 1,
        requires = "verify",
        value_parser = clap::value_parser!(u16).range(1..)
    )]
    n_proof_attempts: u16,
    #[clap(long = "verify", help = "Should verify the generated proof.")]
    verify: bool,
    #[clap(
        long = "program_output",
        help = "An optional output file path for the program output."
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
// TODO(Nitsan): check why this error is so big and if it can be boxed where it was
// created.
impl From<CairoRunError> for StwoRunAndProveError {
    fn from(err: CairoRunError) -> Self {
        StwoRunAndProveError::CairoRun(Box::new(err))
    }
}

struct ProveConfig {
    proofs_dir: PathBuf,
    proof_format: ProofFormat,
    verify: bool,
    n_proof_attempts: u16,
    prover_params_json: Option<PathBuf>,
}

struct CairoProverInputs {
    prover_input: ProverInput,
    pcs_config: PcsConfig,
    preprocessed_trace: PreProcessedTraceVariant,
}

fn main() -> Result<(), StwoRunAndProveError> {
    let args = Args::try_parse_from(env::args())?;
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
        args.program_output,
        prove_config,
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
) -> Result<(), StwoRunAndProveError> {
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
    let output_vec = prove_with_retries(prover_input, prove_config)?;

    if let Some(output_path) = program_output {
        save_output_to_file(output_vec, output_path)?;
    }

    Ok(())
}

/// Prepares the prover parameters and generates proof given the prover input and parameters.
/// Verifies the proof in case the respective flag is set.
/// In case the proof verification fails, it retries up to `n_proof_attempts` times.
/// Returns the program output.
fn prove_with_retries(
    prover_input: ProverInput,
    prove_config: ProveConfig,
) -> Result<OutputVec, StwoRunAndProveError> {
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

    for i in 0..prove_config.n_proof_attempts {
        info!(
            "Attempting to generate proof {}/{}.",
            i + 1,
            prove_config.n_proof_attempts
        );
        let proof_file_path = prove_config.proofs_dir.join(format!("proof_{}", i));
        let proof_file = create_file(&proof_file_path)?;

        match choose_channel_and_prove(
            &cairo_prover_inputs,
            proof_file,
            &proof_format,
            channel_hash,
            prove_config.verify,
        ) {
            Ok(output_values) => {
                info!(
                    "Proof generated and verified successfully on attempt {}/{}",
                    i + 1,
                    prove_config.n_proof_attempts
                );
                return Ok(output_values);
            }

            Err(StwoRunAndProveError::Verification) => {
                if i < prove_config.n_proof_attempts - 1 {
                    warn!(
                        "Proof verification failed on attempt {}/{}. Retrying.",
                        i + 1,
                        prove_config.n_proof_attempts
                    );
                    continue;
                }
                error!(
                    "Proof verification failed on last attempt - {}/{}.",
                    i + 1,
                    prove_config.n_proof_attempts
                );
            }

            Err(e) => return Err(e),
        }
    }

    panic!("Should not reach here, n_proof_attempts should be at least 1.");
}

/// Chooses the appropriate channel based on the `channel_hash` and generates a proof.
fn choose_channel_and_prove(
    cairo_prover_inputs: &CairoProverInputs,
    proof_file: File,
    proof_format: &ProofFormat,
    channel_hash: ChannelHash,
    verify: bool,
) -> Result<OutputVec, StwoRunAndProveError> {
    match channel_hash {
        ChannelHash::Blake2s => {
            prove::<Blake2sMerkleChannel>(cairo_prover_inputs, proof_file, proof_format, verify)
        }
        ChannelHash::Poseidon252 => {
            prove::<Poseidon252MerkleChannel>(cairo_prover_inputs, proof_file, proof_format, verify)
        }
    }
}

/// Generates a proof for the given prover input and parameters, using the specified Merkle channel.
/// Serializes the proof as cairo-serde or JSON and write to the proof path.
/// Verifies the proof if the `verify` flag is set.
/// Returns the program output.
fn prove<MC: MerkleChannel>(
    cairo_prover_inputs: &CairoProverInputs,
    mut proof_file: File,
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

// TODO(nitsan): add tests for the proof, the output and the retry logic.
// TODO(nitsan): add logs
