//! A binary used to convert Cairo programs to circuit proofs
//!
//! Operates in two steps:
//!     1. Runs the given Cairo program and proves it (like stwo_run_and_prove)
//!     2. Uses a circuit to verify the proof from (1)
//!     3. Proves the execution of the circuit from (2)
//!
//! Outputs a file with the output of the Cairo program, the output and preprocessed
//! root of the verifier circuit, and the final proof.

use cairo_program_runner_lib::utils::{get_program, get_program_input_from_path};
use clap::Parser;
use leaf_prover::consts::CIRCUIT_PCS_CONFIG;
use leaf_prover::prove_leaf;
use std::fs::{self, read_to_string};
use std::path::PathBuf;
use std::process::ExitCode;
use stwo_cairo_utils::binary_utils::run_binary;

#[derive(Parser)]
struct Args {
    #[clap(long, help = "Absolute path to the compiled program.")]
    program: PathBuf,
    #[clap(long, help = "Absolute path to the program input file.")]
    program_input: Option<PathBuf>,
    #[clap(
        long,
        help = "Absolute path to the JSON file containing the prover parameters."
    )]
    prover_params_json: PathBuf,
    #[clap(long, help = "Path to write the output file")]
    output_path: PathBuf,
}

fn main() -> ExitCode {
    run_binary(run, "leaf_prover")
}

fn run() -> Result<(), String> {
    let args = Args::parse();
    let program = get_program(&args.program).unwrap();
    let program_input = get_program_input_from_path(&args.program_input).unwrap();
    let prover_parameters =
        sonic_rs::from_str(&read_to_string(&args.prover_params_json).unwrap()).unwrap();
    let output = prove_leaf(&program, program_input, prover_parameters, CIRCUIT_PCS_CONFIG);

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
