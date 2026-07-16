//! A binary used to convert Cairo programs to circuit proofs
//!
//! Operates in two steps:
//!     1. Runs the given Cairo program and proves it (like stwo_run_and_prove)
//!     2. Uses a circuit to verify the proof from (1)
//!     3. Proves the execution of the circuit from (2)
//!
//! Outputs a file with the output of the Cairo program, the output and preprocessed
//! root of the verifier circuit, and the final proof.

use clap::Parser;
use leaf_prover::prove_leaf::prove_leaf_from_files;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;
use stwo_cairo_utils::binary_utils::run_binary;

#[derive(Parser)]
struct Args {
    #[clap(long, help = "Absolute path to the compiled program.")]
    program: PathBuf,
    #[clap(long, help = "Absolute path to the program input file.")]
    program_input: Option<PathBuf>,
    #[clap(long, help = "JSON file containing the Cairo prover parameters.")]
    cairo_prover_params_json: PathBuf,
    #[clap(long, help = "JSON file containing the circuit prover parameters.")]
    circuit_prover_params_json: PathBuf,
    #[clap(long, help = "Path to write the output file")]
    output_path: PathBuf,
}

fn main() -> ExitCode {
    run_binary(run, "leaf_prover")
}

fn run() -> Result<(), String> {
    let args = Args::parse();
    let output = prove_leaf_from_files(
        &args.program,
        &args.program_input,
        &args.cairo_prover_params_json,
        &args.circuit_prover_params_json,
    );

    fs::write(
        &args.output_path,
        serde_json::to_string_pretty(&output).unwrap(),
    )
    .unwrap_or_else(|err| {
        panic!(
            "Cannot write output to {}: {err}",
            args.output_path.display()
        )
    });

    Ok(())
}
