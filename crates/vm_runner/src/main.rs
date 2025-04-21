use std::path::PathBuf;
use std::process::ExitCode;

use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_program, get_program_input};
use cairo_vm::cairo_run;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use clap::Parser;
use stwo_cairo_adapter::plain::adapt_finished_runner;
use stwo_cairo_adapter::vm_import::VmImportError;
use stwo_cairo_adapter::{ExecutionResources, ProverInput};
use stwo_cairo_utils::binary_utils::run_binary;
use thiserror::Error;
use tracing::{span, Level};

/// Command line arguments for stwo_vm_runner.
/// Example command line (use absolute paths):
///     ```
///     cargo run -r --bin stwo_vm_runner -- --program path/to/program --program_input
///     path/to/input --layout <LayoutName> --output_execution_resources_path path/to/output
///     ```
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "program", help = "Path to the compiled program")]
    program: PathBuf,
    #[clap(long = "program_input", help = "Path to the program input file.")]
    program_input: Option<PathBuf>,
    #[clap(long = "layout")]
    layout: LayoutName,
    #[structopt(long = "output_execution_resources_path")]
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
    let args = Args::try_parse_from(args)?;

    let program = get_program(args.program.as_path())?;
    let program_input_contents = get_program_input(&args.program_input)?;
    let cairo_run_config = cairo_run::CairoRunConfig {
        entrypoint: "main",
        trace_enabled: true,
        relocate_mem: true,
        layout: args.layout,
        proof_mode: true,
        secure_run: None,
        disable_trace_padding: true,
        allow_missing_builtins: None,
        dynamic_layout_params: None,
    };
    let cairo_runner = cairo_run_program(&program, program_input_contents, cairo_run_config)?;
    let cairo_input = adapt_finished_runner(cairo_runner)?;

    // Soundness checks that will be verified by the verifier.
    assert_eq!(cairo_input.state_transitions.initial_state.pc.0, 1);
    assert!(
        cairo_input.state_transitions.initial_state.pc.0 < cairo_input.state_transitions.initial_state.ap.0 - 2,
        "Initial pc must be less than initial ap - 2, but got initial_pc: {}, initial_ap: {}",
        cairo_input.state_transitions.initial_state.pc.0,
        cairo_input.state_transitions.initial_state.ap.0 - 2
    );
    assert_eq!(
        cairo_input.state_transitions.initial_state.fp.0,
        cairo_input.state_transitions.final_state.fp.0
    );
    assert_eq!(
        cairo_input.state_transitions.initial_state.fp.0,
        cairo_input.state_transitions.initial_state.ap.0
    );
    assert_eq!(cairo_input.state_transitions.final_state.pc.0, 5);
    assert!(cairo_input.state_transitions.initial_state.ap.0 <= cairo_input.state_transitions.final_state.ap.0);
    assert!(
        cairo_input.state_transitions.final_state.ap.0 < 1 << 31,
        "final_ap must be less than 2^31, but got {}",
        cairo_input.state_transitions.final_state.ap.0
    );

    let execution_resources = ExecutionResources::from_prover_input(&cairo_input);
    log::info!("Execution resources: {:#?}", execution_resources);
    std::fs::write(
        args.output_execution_resources_path,
        serde_json::to_string(&execution_resources)?,
    )?;
    Ok(cairo_input)
}
