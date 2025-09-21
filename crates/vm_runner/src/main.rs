use std::path::PathBuf;
use std::process::ExitCode;

use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_program, get_program_input};
use cairo_vm::cairo_run;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use clap::Parser;
use stwo_cairo_adapter::adapter::adapter;
use stwo_cairo_adapter::vm_import::VmImportError;
use stwo_cairo_adapter::{ExecutionResources, ProverInput};
use stwo_cairo_utils::binary_utils::run_binary;
use thiserror::Error;
use tracing::{span, Level};

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
    #[clap(long = "layout", help = "Layout name.")]
    layout: LayoutName,
    #[structopt(
        long = "output_execution_resources_path",
        help = "Abosolute path to the program's execution resources (output file)."
    )]
    output_execution_resources_path: PathBuf,
}

#[derive(Debug, Error)]
enum Error {
    #[error("Invalid arguments")]
    Cli(#[from] clap::Error),
    #[error("Failed to interact with the file system")]
    IO(#[from] std::io::Error),
    #[error("Serialization failed: {0}")]
    Serde(#[from] serde_json::Error),
    #[error("VM import failed: {0}")]
    VmImport(#[from] VmImportError),
    #[error("ProgramRunner error: {0}")]
    ProgramRunner(#[from] ProgramError),
    #[error("Failed executing the program: {0}")]
    Runner(#[from] CairoRunError),
}

fn main() -> ExitCode {
    run_binary(run, "stwo_vm_runner")
}

#[allow(clippy::result_large_err)]
fn run(args: impl Iterator<Item = String>) -> Result<ProverInput, Error> {
    let _span = span!(Level::INFO, "run").entered();
    let args = match Args::try_parse_from(args) {
        Ok(args) => args,
        Err(err) => err.exit(),
    };

    let program = get_program(args.program.as_path())?;
    let program_input_contents = get_program_input(&args.program_input)?;
    let cairo_run_config = cairo_run::CairoRunConfig {
        entrypoint: "main",
        trace_enabled: true,
        // we don't need to relocate memory in the VM because we later call the adapter that does
        // relocation.
        relocate_mem: false,
        relocate_trace: false,
        layout: args.layout,
        proof_mode: true,
        fill_holes: true,
        secure_run: None,
        disable_trace_padding: true,
        allow_missing_builtins: None,
        dynamic_layout_params: None,
    };
    let cairo_runner = cairo_run_program(&program, program_input_contents, cairo_run_config)?;
    let prover_input = adapter(&cairo_runner);

    let execution_resources = ExecutionResources::from_prover_input(&prover_input);
    log::info!("Execution resources: {execution_resources:#?}");
    std::fs::write(
        args.output_execution_resources_path,
        serde_json::to_string(&execution_resources)?,
    )?;
    Ok(prover_input)
}
