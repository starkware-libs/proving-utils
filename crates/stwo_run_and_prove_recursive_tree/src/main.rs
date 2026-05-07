//! CLI entry point for the recursive-tree binary.
//!
//! See `lib.rs` for the algorithm. CLI surface mirrors `stwo_run_and_prove` (same prover params,
//! proof format, debug data flags) and adds the recursive-tree-specific input/output paths:
//!   `--program_input` (in, the leaves list), `--verifier_program` (in), `--bootloader_program`
//! (in),   `--proof_path` / `--program_output` / `--fact_topologies_path` / `--packed_output_path`
//!   (out, all describing the root layer).

use std::path::PathBuf;
use std::process::ExitCode;

use cairo_air::utils::ProofFormat;
use clap::Parser;
use stwo_cairo_utils::binary_utils::run_binary;
use stwo_run_and_prove_recursive_tree::{
    RecursiveTreeConfig, RecursiveTreeError, StwoProverEntryPoint, load_leaves,
    stwo_run_and_prove_recursive_tree,
};
use tracing::{Level, info, span};

/// CLI arguments. Names use `snake_case` to match the existing
/// `services.gps.prover_utils.core.stwo_prover.StwoProver` convention of `--<file_name>=<path>`.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// JSON file containing `{"leaves": [LeafInput, ...]}`. Each entry references a leaf's
    /// decompressed proof path, fact topology, and outputs. Named `--program_input` to match
    /// the sibling `stwo_run_and_prove` binary's CLI; the content is just a leaves list, not a
    /// Cairo program input.
    #[clap(long = "program_input")]
    program_input: PathBuf,

    /// Path to the verifier program (e.g. stwo_full_cairo_verifier_with_blake_packing) invoked
    /// by each pair-bootloader's two Cairo1Executable user_args tasks.
    #[clap(long = "verifier_program")]
    verifier_program: PathBuf,

    /// Path to the simple-bootloader program executed at every layer of the reduction. The
    /// caller is expected to pass the same program Python's
    /// `choose_bootloader_program_path_from_train` would (the no-builtin-simulation variant for
    /// offchain recursive trains).
    #[clap(long = "bootloader_program")]
    bootloader_program: PathBuf,

    /// Optional prover parameters JSON; same semantics as `stwo_run_and_prove
    /// --prover_params_json`.
    #[clap(long = "prover_params_json")]
    prover_params_json: Option<PathBuf>,

    /// Output path for the root layer's proof.
    #[clap(long = "proof_path")]
    proof_path: PathBuf,

    /// Output path for the root layer's `flatten_task_outputs` (JSON array of hex-encoded
    /// Felt252 values, identical format to `stwo_run_and_prove --program_output`).
    #[clap(long = "program_output")]
    program_output: PathBuf,

    /// Output path for the root layer's `FactTopologiesFile` (JSON `{"fact_topologies": [...]}`
    /// with exactly one element).
    #[clap(long = "fact_topologies_path")]
    fact_topologies_path: PathBuf,

    /// Output path for the nested `NestedPackedOutput` JSON consumed by Python's
    /// `get_applicative_program` (mirrors `PackedOutputSchema`).
    #[clap(long = "packed_output_path")]
    packed_output_path: PathBuf,

    #[clap(long, value_enum, default_value_t = ProofFormat::CairoSerde, help = "Json or cairo-serde.")]
    proof_format: ProofFormat,

    #[clap(long = "verify", help = "Should verify each generated layer proof.")]
    verify: bool,

    #[clap(long = "save_debug_data")]
    save_debug_data: bool,

    #[clap(long = "debug_data_dir")]
    debug_data_dir: Option<PathBuf>,
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
        verifier_program = ?args.verifier_program,
        bootloader_program = ?args.bootloader_program,
        "Starting in-binary recursive-tree reduction.",
    );
    let config = RecursiveTreeConfig {
        leaves,
        verifier_program: args.verifier_program,
        bootloader_program: args.bootloader_program,
        prover_params_json: args.prover_params_json,
        proof_format: args.proof_format,
        verify: args.verify,
        proof_path: args.proof_path,
        program_output: args.program_output,
        fact_topologies_path: args.fact_topologies_path,
        packed_output_path: args.packed_output_path,
        save_debug_data: args.save_debug_data,
        debug_data_dir: args.debug_data_dir,
    };
    let recursive_job_data = stwo_run_and_prove_recursive_tree(config, &StwoProverEntryPoint)?;
    info!(
        n_non_recursive_jobs = recursive_job_data.counters.n_non_recursive_jobs,
        total_n_pages = recursive_job_data.counters.total_n_pages,
        "Recursive tree reduction complete.",
    );
    Ok(())
}
