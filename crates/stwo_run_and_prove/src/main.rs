use cairo_air::PreProcessedTraceVariant;
use cairo_air::utils::ProofFormat;
use cairo_air::verifier::{CairoVerificationError, verify_cairo};
use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_cairo_run_config, get_program, get_program_input};
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use clap::Parser;
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
use stwo_cairo_serialize::CairoSerialize;
use stwo_cairo_utils::file_utils::{IoErrorWithPath, create_file, read_to_string};
use stwo_prover::core::backend::BackendForChannel;
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::channel::MerkleChannel;
use stwo_prover::core::pcs::PcsConfig;
use stwo_prover::core::prover::ProvingError;
use stwo_prover::core::vcs::blake2_merkle::Blake2sMerkleChannel;
use stwo_prover::core::vcs::ops::MerkleHasher;
use stwo_prover::core::vcs::poseidon252_merkle::Poseidon252MerkleChannel;
use thiserror::Error;

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
    #[error(transparent)]
    Verification(#[from] CairoVerificationError),
}

// Implement From<Box<CairoRunError>> manually
// TODO(Nitsan): check why this error is so big and if it can be boxed where it was
// created.
impl From<CairoRunError> for StwoRunAndProveError {
    fn from(err: CairoRunError) -> Self {
        StwoRunAndProveError::CairoRun(Box::new(err))
    }
}

fn main() -> Result<(), StwoRunAndProveError> {
    let args = Args::try_parse_from(env::args())?;

    stwo_run_and_prove(
        args.program,
        args.program_input,
        args.program_output,
        args.params_json,
        args.verify,
        args.proof_path,
        args.proof_format,
    )?;
    Ok(())
}

fn stwo_run_and_prove(
    program: PathBuf,
    program_input: Option<PathBuf>,
    program_output: Option<PathBuf>,
    params_json: Option<PathBuf>,
    verify: bool,
    proof_path: PathBuf,
    proof_format: ProofFormat,
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
    let runner = cairo_run_program(&program, program_input, cairo_run_config)?;
    let mut prover_input_info = runner.get_prover_input_info()?;
    let prover_input = adapter(&mut prover_input_info)?;

    let output_vec = prove(params_json, prover_input, verify, proof_path, proof_format)?;

    if let Some(output_path) = program_output {
        save_output_to_file(output_vec, output_path)?;
    }

    Ok(())
}

/// Prepares the prover parameters, chooses the merkle channel based on the channel hash,
/// and calls the `prove_with_channel` function to generate the proof.
fn prove(
    prover_params_json: Option<PathBuf>,
    prover_input: ProverInput,
    verify: bool,
    proof_path: PathBuf,
    proof_format: ProofFormat,
) -> Result<OutputVec, StwoRunAndProveError> {
    let ProverParameters {
        channel_hash,
        pcs_config,
        preprocessed_trace,
    } = match prover_params_json {
        Some(path) => sonic_rs::from_str(&read_to_string(&path)?)?,
        None => default_prod_prover_parameters(),
    };

    let prove_with_channel_fn = match channel_hash {
        ChannelHash::Blake2s => prove_with_channel::<Blake2sMerkleChannel>,
        ChannelHash::Poseidon252 => prove_with_channel::<Poseidon252MerkleChannel>,
    };

    prove_with_channel_fn(
        prover_input,
        pcs_config,
        preprocessed_trace,
        verify,
        proof_path,
        proof_format,
    )
}

/// Generates proof given the prover input and prover parameters, using the specified merkel
/// channel. Serializes the proof as cairo-serde or JSON and write to the proof path.
/// Verifies the proof in case the respective flag is set.
/// Returns the program output in case the respective flag is set.
fn prove_with_channel<MC: MerkleChannel>(
    prover_input: ProverInput,
    pcs_config: PcsConfig,
    preprocessed_trace: PreProcessedTraceVariant,
    verify: bool,
    proof_path: PathBuf,
    proof_format: ProofFormat,
) -> Result<OutputVec, StwoRunAndProveError>
where
    SimdBackend: BackendForChannel<MC>,
    MC::H: Serialize,
    <MC::H as MerkleHasher>::Hash: CairoSerialize,
{
    let proof = prove_cairo::<MC>(prover_input, pcs_config, preprocessed_trace)?;
    let mut proof_file = create_file(&proof_path)?;

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
    let output_values = output_addresses_and_values
        .into_iter()
        .map(|(_, value)| value)
        .collect();

    if verify {
        verify_cairo::<MC>(proof, preprocessed_trace)?;
    }

    Ok(output_values)
}

/// Saves the program output to the specified output path as [u32; 8] values,
/// that will be converted to [u256] in the Prover service.
fn save_output_to_file(
    output_vec: OutputVec,
    output_path: PathBuf,
) -> Result<(), StwoRunAndProveError> {
    let serialized_output = sonic_rs::to_string(&output_vec)?;
    std::fs::write(output_path, serialized_output)?;
    Ok(())
}

// TODO(nitsan): add a test for the main function that runs the program and checks the output.
