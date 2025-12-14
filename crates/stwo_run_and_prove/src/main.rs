use cairo_air::utils::ProofFormat;
use clap::Parser;
use std::path::PathBuf;
use std::process::ExitCode;
use stwo_cairo_utils::binary_utils::run_binary;
use stwo_run_and_prove::{
    ProveConfig, StwoProverEntryPoint, StwoRunAndProveError, stwo_run_and_prove,
};
use tracing::{Level, span};

/// This binary runs a cairo program and generates a Stwo proof for it.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "program", help = "Absolute path to the compiled program.")]
    program: PathBuf,
    #[clap(
        long = "program_input",
        help = "Absolute path to the program input file."
    )]
    program_input: Option<PathBuf>,
    #[clap(
        long = "prover_params_json",
        help = "Absolute path to the JSON file containing the prover parameters."
    )]
    prover_params_json: Option<PathBuf>,
    #[clap(
        long = "proof_path",
        help = "Absolute path where the generated proof will be saved."
    )]
    proof_path: PathBuf,
    #[clap(long, value_enum, default_value_t = ProofFormat::CairoSerde, help = "Json or cairo-serde.")]
    proof_format: ProofFormat,
    #[clap(long = "verify", help = "Should verify the generated proof.")]
    verify: bool,
    #[clap(
        long = "program_output",
        help = "Optional absolute path for the program output."
    )]
    program_output: Option<PathBuf>,
}

fn main() -> ExitCode {
    run_binary(run, "stwo_run_and_prove")
}

fn run() -> Result<(), StwoRunAndProveError> {
    let _span = span!(Level::INFO, "run").entered();
    let args = Args::parse();
    let prove_config = ProveConfig {
        verify: args.verify,
        proof_path: args.proof_path,
        proof_format: args.proof_format,
        prover_params_json: args.prover_params_json,
    };

    let stwo_prover = Box::new(StwoProverEntryPoint);
    stwo_run_and_prove(
        args.program,
        args.program_input,
        args.program_output,
        prove_config,
        stwo_prover,
    )?;
    Ok(())
}
