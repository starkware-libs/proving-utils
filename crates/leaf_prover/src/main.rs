//! A binary used to convert Cairo programs to circuit proofs
//!
//! Operates in two steps:
//!     1. Runs the given Cairo program and proves it (like stwo_run_and_prove)
//!     2. Uses a circuit to verify the proof from (1)
//!     3. Proves the execution of the circuit from (2)
//!
//! Outputs a file with the final proof and the preprocessed root of the verifier
//! circuit. It is assumed that the user knows the output of the program (required
//! to verify the proof) by some other means.

use cairo_program_runner_lib::utils::{get_program, get_program_input_from_path};
use clap::Parser;
use leaf_prover::prove_leaf::prove_leaf;
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
    let program = get_program(&args.program)
        .unwrap_or_else(|err| panic!("Cannot get program from {}: {err}", args.program.display()));
    let program_input = get_program_input_from_path(&args.program_input).unwrap_or_else(|err| {
        panic!(
            "Cannot get program input from {:?}: {err}",
            args.program_input.as_ref().map(|x| x.display())
        )
    });

    let cairo_prover_parameters =
        read_to_string(&args.cairo_prover_params_json).unwrap_or_else(|err| {
            panic!(
                "Cannot get Cairo prover parameters from {}: {err}",
                args.cairo_prover_params_json.display()
            )
        });
    let cairo_prover_parameters = sonic_rs::from_str(&cairo_prover_parameters).unwrap();

    let circuit_prover_pcs_config = read_to_string(&args.circuit_prover_params_json)
        .unwrap_or_else(|err| {
            panic!(
                "Cannot get circuit prover parameters from {}: {err}",
                args.circuit_prover_params_json.display()
            )
        });
    let circuit_prover_pcs_config = sonic_rs::from_str(&circuit_prover_pcs_config).unwrap();

    let output = prove_leaf(
        &program,
        program_input,
        cairo_prover_parameters,
        circuit_prover_pcs_config,
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
