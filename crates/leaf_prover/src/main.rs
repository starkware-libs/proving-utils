//! A binary used to convert Cairo programs to circuit proofs
//!
//! Operates in two steps:
//!     1. Runs the given Cairo program and proves it (like stwo_run_and_prove)
//!     2. Uses a circuit to verify the proof from (1)
//!     3. Proves the execution of the circuit from (2)

use cairo_program_runner_lib::utils::{get_program, get_program_input_from_path};
use clap::Parser;
use leaf_prover::prove_leaf;
use std::fs::read_to_string;
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
    #[clap(long, help = "Path to store the final proof")]
    proof_path: PathBuf,
    #[clap(long, help = "Path to store the output of the program")]
    output_path: Option<PathBuf>,
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
    prove_leaf(
        &program,
        program_input,
        prover_parameters,
        args.proof_path,
        args.output_path,
    );

    Ok(())
}
