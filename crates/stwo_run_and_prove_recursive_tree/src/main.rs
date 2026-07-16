//! CLI entry point for the recursive circuit-proof tree binary.
//!
//! See `lib.rs` for the algorithm. The CLI takes the leaves list and the three root output paths;
//! all proving configuration is fixed by the canonical circuit shape (see `canonical`), so there
//! are no prover-params / verifier-program / bootloader-program arguments anymore.

use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use stwo_cairo_utils::binary_utils::run_binary;
use stwo_run_and_prove_recursive_tree::{
    RecursiveTreeError, load_leaves, stwo_run_and_prove_recursive_tree,
};
use tracing::{Level, info, span};

/// CLI arguments. Names use `snake_case` to match the existing pipeline convention of
/// `--<file_name>=<path>`.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// JSON manifest `{"leaves": ["<path>", ...]}` listing one leaf input file per leaf, in fold
    /// order: a `leaf_prover` output with the backend-injected fields flattened in (see
    /// `LeafInput`). Named `--program_input` to match the sibling binaries' CLI convention.
    #[clap(long = "program_input")]
    program_input: PathBuf,

    /// Output path for the root circuit proof. For a multi-leaf tree this is the Cairo circuit
    /// verifier's felt252 arguments stream (a JSON array of hex-string felts); a single-leaf tree
    /// copies the leaf's serialized proof through unchanged.
    #[clap(long = "proof_path")]
    proof_path: PathBuf,

    /// Output path for the root node's output values (JSON array of `[u32; 4]` QM31 limbs).
    #[clap(long = "program_output")]
    program_output: PathBuf,

    /// Output path for the nested `PackedNode` JSON tree consumed by a future per-leaf unpacker.
    #[clap(long = "packed_output_path")]
    packed_output_path: PathBuf,
}

fn main() -> ExitCode {
    run_binary(run, "stwo_run_and_prove_recursive_tree")
}

fn run() -> Result<(), RecursiveTreeError> {
    let _span = span!(Level::INFO, "stwo_run_and_prove_recursive_tree::run").entered();
    let args = Args::parse();
    let leaves = load_leaves(&args.program_input)?;
    info!(
        n_leaves = leaves.len(),
        "Starting in-binary recursive circuit-proof tree reduction."
    );
    let stats = stwo_run_and_prove_recursive_tree(
        leaves,
        &args.proof_path,
        &args.program_output,
        &args.packed_output_path,
    )?;
    info!(
        n_layers = stats.n_layers,
        n_pair_reductions = stats.n_pair_reductions,
        "Recursive tree reduction complete."
    );
    Ok(())
}
