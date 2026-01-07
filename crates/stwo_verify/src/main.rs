use std::path::PathBuf;
use std::process::ExitCode;

use cairo_air::utils::{deserialize_proof_from_file, get_verification_output, ProofFormat};
use cairo_air::verifier::verify_cairo;
use cairo_air::{CairoProof, PreProcessedTraceVariant};
use clap::Parser;
use stwo_cairo_prover::prover::ChannelHash;
use stwo_cairo_prover::stwo::core::vcs::blake2_merkle::{
    Blake2sMerkleChannel, Blake2sMerkleHasher,
};
use stwo_cairo_prover::stwo::core::vcs::poseidon252_merkle::{
    Poseidon252MerkleChannel, Poseidon252MerkleHasher,
};
use stwo_cairo_utils::binary_utils::run_binary;
use thiserror::Error;
use tracing::{info, span, Level};

/// This binary verifies a Stwo Cairo proof.
///
/// Exit codes:
/// - 0: Proof is valid.
/// - 1: Proof is invalid or verification failed.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "proof_path", help = "Absolute path to the serialized proof file.")]
    proof_path: PathBuf,
    #[clap(
        long,
        value_enum,
        default_value_t = ProofFormat::CairoSerde,
        help = "Proof format: Json, CairoSerde, or Binary."
    )]
    proof_format: ProofFormat,
    #[clap(
        long = "channel_hash",
        default_value = "blake2s",
        help = "Hash variant for the Merkle channel: blake2s or poseidon252."
    )]
    channel_hash: String,
    #[clap(
        long = "program_output",
        help = "Optional absolute path where the program's output will be saved."
    )]
    program_output: Option<PathBuf>,
    #[clap(
        long = "program_hash_output",
        help = "Optional absolute path where the program hash will be saved."
    )]
    program_hash_output: Option<PathBuf>,
    #[clap(
        long = "preprocessed_trace",
        default_value = "canonical",
        help = "Preprocessed trace variant: canonical or canonical_without_pedersen."
    )]
    preprocessed_trace: String,
}

#[derive(Debug, Error)]
enum StwoVerifyError {
    #[error("IO error on file '{1:?}': {0}")]
    PathIO(std::io::Error, PathBuf),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    Serializing(#[from] sonic_rs::error::Error),
    #[error(transparent)]
    Anyhow(#[from] anyhow::Error),
    #[error("Verification failed: {0}")]
    Verification(String),
}

fn main() -> ExitCode {
    run_binary(run, "stwo_verify")
}

fn run() -> Result<(), StwoVerifyError> {
    let _span = span!(Level::INFO, "run").entered();
    let args = Args::parse();

    let preprocessed_trace = parse_preprocessed_trace(&args.preprocessed_trace);
    let channel_hash = parse_channel_hash(&args.channel_hash)?;

    verify_proof(
        args.proof_path,
        args.proof_format,
        channel_hash,
        args.program_output,
        args.program_hash_output,
        preprocessed_trace,
    )?;

    info!("✅ Proof verified successfully!");
    Ok(())
}

fn parse_preprocessed_trace(preprocessed_trace: &str) -> PreProcessedTraceVariant {
    match preprocessed_trace {
        "canonical" => PreProcessedTraceVariant::Canonical,
        "canonical_without_pedersen" | "no_pedersen" => {
            PreProcessedTraceVariant::CanonicalWithoutPedersen
        }
        _ => panic!(
            "Invalid preprocessed trace: {preprocessed_trace}, must be 'canonical' or \
             'canonical_without_pedersen'"
        ),
    }
}

fn parse_channel_hash(channel_hash: &str) -> Result<ChannelHash, StwoVerifyError> {
    match channel_hash.to_lowercase().as_str() {
        "blake2s" => Ok(ChannelHash::Blake2s),
        "poseidon252" => Ok(ChannelHash::Poseidon252),
        _ => Err(StwoVerifyError::Anyhow(anyhow::anyhow!(
            "Invalid channel hash: {channel_hash}. Must be 'blake2s' or 'poseidon252'"
        ))),
    }
}

/// Verifies a proof from a file, writes the program output and program hash if paths are provided.
/// Returns Ok(()) if verification succeeded, Err otherwise.
fn verify_proof(
    proof_path: PathBuf,
    proof_format: ProofFormat,
    channel_hash: ChannelHash,
    program_output_path: Option<PathBuf>,
    program_hash_path: Option<PathBuf>,
    preprocessed_trace: PreProcessedTraceVariant,
) -> Result<(), StwoVerifyError> {
    let _span = span!(Level::INFO, "verify_proof").entered();

    info!("Verifying a {:?} proof", channel_hash);
    info!("Deserializing proof from: {:?}", proof_path);

    match channel_hash {
        ChannelHash::Blake2s => verify_blake2s_proof(
            proof_path,
            proof_format,
            program_output_path,
            program_hash_path,
            preprocessed_trace,
        ),
        ChannelHash::Poseidon252 => verify_poseidon252_proof(
            proof_path,
            proof_format,
            program_output_path,
            program_hash_path,
            preprocessed_trace,
        ),
    }
}

fn verify_blake2s_proof(
    proof_path: PathBuf,
    proof_format: ProofFormat,
    program_output_path: Option<PathBuf>,
    program_hash_path: Option<PathBuf>,
    preprocessed_trace: PreProcessedTraceVariant,
) -> Result<(), StwoVerifyError> {
    // Deserialize the proof.
    let proof: CairoProof<Blake2sMerkleHasher> =
        deserialize_proof_from_file(&proof_path, proof_format)
            .map_err(|e| StwoVerifyError::PathIO(e, proof_path.clone()))?;

    // Extract and write verification output.
    write_verification_output(&proof.claim.public_data.public_memory, program_output_path, program_hash_path)?;

    // Verify the proof.
    info!("Verifying proof...");
    verify_cairo::<Blake2sMerkleChannel>(proof, preprocessed_trace)
        .map_err(|e| StwoVerifyError::Verification(e.to_string()))
}

fn verify_poseidon252_proof(
    proof_path: PathBuf,
    proof_format: ProofFormat,
    program_output_path: Option<PathBuf>,
    program_hash_path: Option<PathBuf>,
    preprocessed_trace: PreProcessedTraceVariant,
) -> Result<(), StwoVerifyError> {
    // Deserialize the proof.
    let proof: CairoProof<Poseidon252MerkleHasher> =
        deserialize_proof_from_file(&proof_path, proof_format)
            .map_err(|e| StwoVerifyError::PathIO(e, proof_path.clone()))?;

    // Extract and write verification output.
    write_verification_output(&proof.claim.public_data.public_memory, program_output_path, program_hash_path)?;

    // Verify the proof.
    info!("Verifying proof...");
    verify_cairo::<Poseidon252MerkleChannel>(proof, preprocessed_trace)
        .map_err(|e| StwoVerifyError::Verification(e.to_string()))
}

fn write_verification_output(
    public_memory: &cairo_air::air::PublicMemory,
    program_output_path: Option<PathBuf>,
    program_hash_path: Option<PathBuf>,
) -> Result<(), StwoVerifyError> {
    let verification_output = get_verification_output(public_memory);

    // Write program output if path is provided.
    if let Some(output_path) = program_output_path {
        info!("Saving program output to: {:?}", output_path);
        let output_hex: Vec<String> = verification_output
            .output
            .iter()
            .map(|felt| format!("0x{felt:x}"))
            .collect();
        std::fs::write(&output_path, sonic_rs::to_string_pretty(&output_hex)?)
            .map_err(|e| StwoVerifyError::PathIO(e, output_path))?;
    }

    // Write program hash if path is provided.
    if let Some(hash_path) = program_hash_path {
        info!("Saving program hash to: {:?}", hash_path);
        let hash_hex = format!("0x{:x}", verification_output.program_hash);
        std::fs::write(&hash_path, hash_hex)
            .map_err(|e| StwoVerifyError::PathIO(e, hash_path))?;
    }

    Ok(())
}
