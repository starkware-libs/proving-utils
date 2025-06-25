use cairo_air::utils::ProofFormat;
use cairo_air::verifier::{verify_cairo, CairoVerificationError};
use cairo_air::{CairoProof, PreProcessedTraceVariant};
use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_cairo_run_config, get_program, get_program_input};
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
use clap::Parser;
use serde::Serialize;
use std::env;
use std::io::Write;
use std::path::PathBuf;
use std::thread::sleep;
use stwo_cairo_adapter::adapter::adapter;
use stwo_cairo_adapter::vm_import::VmImportError;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_prover::prover::{
    default_prod_prover_parameters, prove_cairo, ChannelHash, ProverParameters,
};
use stwo_cairo_prover::stwo_prover::core::backend::simd::SimdBackend;
use stwo_cairo_prover::stwo_prover::core::backend::BackendForChannel;
use stwo_cairo_prover::stwo_prover::core::channel::MerkleChannel;
use stwo_cairo_prover::stwo_prover::core::pcs::PcsConfig;
use stwo_cairo_prover::stwo_prover::core::prover::ProvingError;
use stwo_cairo_prover::stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo_cairo_prover::stwo_prover::core::vcs::ops::MerkleHasher;
use stwo_cairo_prover::stwo_prover::core::vcs::poseidon252_merkle::Poseidon252MerkleChannel;
use stwo_cairo_serialize::CairoSerialize;
use stwo_cairo_utils::file_utils::{create_file, read_to_string, IoErrorWithPath};
use thiserror::Error;
use tracing::{span, Level};

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// cairo run args: ///

    #[clap(long = "program", help = "Path to the compiled program")]
    program: PathBuf,
    #[clap(long = "program_input", help = "Path to the program input file.")]
    program_input: Option<PathBuf>,
    #[clap(
        long = "disable_trace_padding",
        help = "Disable padding of the execution trace at the end of the run."
    )]
    disable_trace_padding: bool,
    #[clap(
        long = "allow_missing_builtins",
        default_missing_value = "true",
        help = "Allow initializing the runner with builtins in the program that are not present in
        the layout."
    )]
    allow_missing_builtins: bool,
    #[clap(
        long = "n_cairo_run_attempts",
        help = "Number of attempts for cairo run.",
        default_value_t = 1
    )]
    n_cairo_run_attempts: u16,

    /// prove args: ///

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
        long = "params_json",
        help = "The path to the JSON file containing the prover parameters."
    )]
    params_json: Option<PathBuf>,
    #[clap(long = "proof_path", help = "The output file path for the proof.")]
    proof_path: PathBuf,
    #[clap(long, value_enum, default_value_t = ProofFormat::Json, help = "Json or cairo-serde.")]
    proof_format: ProofFormat,
    #[clap(long = "verify", help = "Should verify the generated proof.")]
    verify: bool,
    #[clap(
        long = "n_proof_attempts",
        help = "Number of attempts for proving.",
        default_value_t = 1
    )]
    n_proof_attempts: u16,
}

#[derive(Debug, Error)]
enum Error {
    #[error("Invalid arguments: {0}")]
    Cli(#[from] clap::Error),
    #[error("IO failed: {0}")]
    IO(#[from] std::io::Error),
    #[error("Proving failed: {0}")]
    Proving(#[from] ProvingError),
    #[error("Serialization failed: {0}")]
    Serializing(#[from] sonic_rs::error::Error),
    #[error("Verification failed: {0}")]
    Verification(#[from] CairoVerificationError),
    #[error("VM import failed: {0}")]
    VmImport(#[from] VmImportError),
    #[error("File IO failed: {0}")]
    File(#[from] IoErrorWithPath),
    #[error("Failed executing the program: {0}")]
    CairoRun(Box<CairoRunError>),
    #[error("Program error: {0}")]
    Program(#[from] ProgramError),
    #[error("Runner error: {0}")]
    Runner(#[from] RunnerError),
    #[error("Missing runner after all cairo run attempts - should not get here because in case of failure in all attempts, the program returns with CairoRunError.")]
    MissingRunner,
    #[error("Missing proof after all prove attempts - should not get here because in case of failure in all attempts, the program returns with ProvingError.")]
    MissingProof,
}

// Implement From<Box<CairoRunError>> manually
impl From<CairoRunError> for Error {
    fn from(err: CairoRunError) -> Self {
        Error::CairoRun(Box::new(err))
    }
}

#[derive(Debug)]
struct RunAndProveResult {
    success_cairo_runner_attempt: u16,
    success_proof_attempt: u16,
}

/// When main function returns a RunAndProveResult, Rust calls this method.
impl std::process::Termination for RunAndProveResult {
    fn report(self) -> std::process::ExitCode {
        println!("Run success: {:?}", self);
        std::process::ExitCode::SUCCESS
    }
}

fn main() -> Result<RunAndProveResult, Error> {
    let args = Args::try_parse_from(env::args()).map_err(Error::Cli)?;
    let program = get_program(args.program.as_path())?;

    let program_input_contents = get_program_input(&args.program_input)?;
    let cairo_run_config = get_cairo_run_config(
        &None, // we don't use dynamic layout in stwo
        LayoutName::all_cairo_stwo,
        true,
        args.disable_trace_padding,
        args.allow_missing_builtins,
        false,
    )?;

    let mut runner: Option<CairoRunner> = None;
    let mut success_cairo_runner_attempt = 0;

    for i in 0..args.n_cairo_run_attempts {
        match cairo_run_program(&program, program_input_contents.clone(), &cairo_run_config) {
            Ok(r) => {
                runner = Some(r);
                success_cairo_runner_attempt = i + 1;
                log::info!(
                    "Cairo run attempt {}/{} succeeded",
                    success_cairo_runner_attempt,
                    args.n_cairo_run_attempts
                );
                break;
            }
            Err(e) => {
                log::warn!(
                    "Cairo run attempt {}/{} failed: {}",
                    i + 1,
                    args.n_cairo_run_attempts,
                    e
                );
                if i == args.n_cairo_run_attempts - 1 {
                    return Err(e.into());
                }
                sleep(std::time::Duration::from_secs(15));
            }
        }
    }

    let runner = runner.ok_or(Error::MissingRunner)?;
    let mut prover_input_info = runner.get_prover_input_info()?;
    let prover_input = adapter(&mut prover_input_info)?;

    let ProverParameters {
        channel_hash,
        pcs_config,
        preprocessed_trace,
    } = match args.params_json {
        Some(path) => sonic_rs::from_str(&read_to_string(&path)?)?,
        None => default_prod_prover_parameters(),
    };

    let prove_and_verify_fn = match channel_hash {
        ChannelHash::Blake2s => prove_and_verify::<Blake2sMerkleChannel>,
        ChannelHash::Poseidon252 => prove_and_verify::<Poseidon252MerkleChannel>,
    };

    let success_proof_attempt = prove_and_verify_fn(
        prover_input,
        pcs_config,
        preprocessed_trace,
        args.verify,
        args.proof_path,
        args.proof_format,
        args.n_proof_attempts,
    )?;

    Ok(RunAndProveResult {
        success_cairo_runner_attempt,
        success_proof_attempt,
    })
}

/// Generates proof given the Cairo VM output and prover parameters.
/// Serializes the proof as cairo-serde or JSON and write to the output path.
/// Verifies the proof in case the respective flag is set.
fn prove_and_verify<MC: MerkleChannel>(
    vm_output: ProverInput,
    pcs_config: PcsConfig,
    preprocessed_trace: PreProcessedTraceVariant,
    verify: bool,
    proof_path: PathBuf,
    proof_format: ProofFormat,
    n_proof_attempts: u16,
) -> Result<u16, Error>
where
    SimdBackend: BackendForChannel<MC>,
    MC::H: Serialize,
    <MC::H as MerkleHasher>::Hash: CairoSerialize,
{
    let mut proof: Option<CairoProof<MC::H>> = None;
    let mut success_proof_attempt = 0;

    for i in 0..n_proof_attempts {
        match prove_cairo::<MC>(vm_output.clone(), pcs_config, preprocessed_trace) {
            Ok(p) => {
                proof = Some(p);
                success_proof_attempt = i + 1;
                log::info!(
                    "Proof attempt {}/{} succeeded",
                    success_proof_attempt,
                    n_proof_attempts
                );
                break;
            }
            Err(e) => {
                log::warn!("Proof attempt {}/{} failed: {}", i + 1, n_proof_attempts, e);
                if i == n_proof_attempts - 1 {
                    return Err(Error::Proving(e));
                }
            }
        }
    }

    let proof = proof.ok_or(Error::MissingProof)?;
    let mut proof_file = create_file(&proof_path).map_err(Error::File)?;

    let span = span!(Level::INFO, "Serialize proof").entered();
    match proof_format {
        ProofFormat::Json => {
            let serialized = sonic_rs::to_string_pretty(&proof)?;
            proof_file
                .write_all(serialized.as_bytes())
                .map_err(Error::IO)?;
        }
        ProofFormat::CairoSerde => {
            let mut serialized: Vec<starknet_ff::FieldElement> = Vec::new();
            CairoSerialize::serialize(&proof, &mut serialized);

            let hex_strings: Vec<String> = serialized
                .into_iter()
                .map(|felt| format!("0x{:x}", felt))
                .collect();

            let serialized_hex = sonic_rs::to_string_pretty(&hex_strings)?;
            proof_file
                .write_all(serialized_hex.as_bytes())
                .map_err(Error::IO)?;
        }
    }

    span.exit();

    if verify {
        verify_cairo::<MC>(proof, preprocessed_trace)?;
    }

    Ok(success_proof_attempt)
}
