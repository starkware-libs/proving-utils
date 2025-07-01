use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_cairo_run_config, get_program, get_program_input};
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use clap::Parser;
use std::env;
use std::path::PathBuf;
use stwo_cairo_adapter::adapter::adapter;
use stwo_cairo_adapter::vm_import::VmImportError;
use thiserror::Error;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// cairo run args: ///

    #[clap(long = "program", help = "Path to the compiled program")]
    program: PathBuf,
    #[clap(long = "program_input", help = "Path to the program input file.")]
    program_input: Option<PathBuf>,
    #[clap(
        long = "disable_trace_padding",
        help = "Disable padding of the execution trace at the end of the run."
    )]
    disable_trace_padding: bool,
    #[clap(
        long = "allow_missing_builtins",
        default_missing_value = "true",
        help = "Allow initializing the runner with builtins in the program that are not present in
        the layout."
    )]
    allow_missing_builtins: bool,
}

#[derive(Debug, Error)]
enum Error {
    #[error("Invalid arguments: {0}")]
    Cli(#[from] clap::Error),
    #[error("IO failed: {0}")]
    IO(#[from] std::io::Error),
    #[error("VM import failed: {0}")]
    VmImport(#[from] VmImportError),
    #[error("Failed executing the program: {0}")]
    CairoRun(Box<CairoRunError>),
    #[error("Program error: {0}")]
    Program(#[from] ProgramError),
    #[error("Runner error: {0}")]
    Runner(#[from] RunnerError),
}

// Implement From<Box<CairoRunError>> manually
impl From<CairoRunError> for Error {
    fn from(err: CairoRunError) -> Self {
        Error::CairoRun(Box::new(err))
    }
}

#[allow(unused_variables)] // The prove part is not implemented yet, so we keep this unused variable to avoid warnings.
fn main() -> Result<(), Error> {
    let args = Args::try_parse_from(env::args()).map_err(Error::Cli)?;
    let program = get_program(args.program.as_path())?;

    let program_input_contents = get_program_input(&args.program_input)?;
    let cairo_run_config = get_cairo_run_config(
        &None, // we don't use dynamic layout in stwo
        LayoutName::all_cairo_stwo,
        true,
        args.disable_trace_padding,
        args.allow_missing_builtins,
        false,
    )?;

    let runner = cairo_run_program(&program, program_input_contents.clone(), cairo_run_config)?;
    let mut prover_input_info = runner.get_prover_input_info()?;
    let prover_input = adapter(&mut prover_input_info)?;

    // prove will be implemented in next PR

    Ok(())
}
