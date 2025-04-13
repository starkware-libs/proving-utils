use std::env;
use std::path::PathBuf;
use std::process::ExitCode;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use tracing_subscriber::fmt::format::FmtSpan;

use clap::Parser;
use stwo_cairo_adapter::plain::adapt_finished_runner;
use stwo_cairo_adapter::vm_import::VmImportError;
use stwo_cairo_adapter::{ExecutionResources, ProverInput};
use stwo_cairo_utils::vm_utils::{run_vm, VmArgs, VmError};
use cairo_program_runner_lib::utils::{get_program, get_program_input};
use cairo_program_runner_lib::cairo_run_program;
use thiserror::Error;
use tracing::{span, Level};
use cairo_vm::cairo_run;
use cairo_vm::types::layout_name::LayoutName;



/// Command line arguments for stwo_vm_runner.
/// Example command line (use absolute paths):
///     ```
///     cargo run -r --bin bin1 -- --run_from_cairo_pie
///     --output_path path/to/output --secure_run=true path/to/cairo/pie
///     
///     cargo run -r --bin bin1 -- --program path/to/program --program_input path/to/input
///     --output_execution_resources_path path/to/output
///     ```
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct ArgsForPie {
    #[command(flatten)]
    vm_args: VmArgs,
    /// The file path for the output (the adapted execution resources of the VM run).
    #[structopt(long = "output_path")]
    output_path: PathBuf,
}

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct ArgsForProgram {
    #[clap(long = "program", help = "Path to the compiled program")]
    program: PathBuf,
    #[clap(long = "program_input", help = "Path to the program input file.")]
    program_input: Option<PathBuf>,
    #[structopt(long = "output_execution_resources_path")]
    output_execution_resources_path: PathBuf,
}

#[derive(Debug, Error)]
enum Error {
    #[error("Invalid arguments")]
    Cli(#[from] clap::Error),
    #[error("Failed to interact with the file system")]
    IO(#[from] std::io::Error),
    #[error("VM run failed: {0}")]
    Vm(#[from] VmError),
    #[error("Serialization failed: {0}")]
    Serde(#[from] serde_json::Error),
    #[error("VM import failed: {0}")]
    VmImport(#[from] VmImportError),
    #[error("ProgramRunner error: {0}")]
    ProgramRunner(#[from] ProgramError),
    #[error("Failed executing the program: {0}")]
    Runner(#[from] CairoRunError),
}


/// Initializes env_logger.
/// The format is:
/// `<level>  /path/to/file:<line_number>  <time>  <log_message>`
pub fn tmp_init_logging(log_level: log::LevelFilter) {
    env_logger::Builder::new().filter_level(log_level).init();

    let subscriber = tracing_subscriber::fmt()
        .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
        .finish();
    tracing::subscriber::set_global_default(subscriber).expect("Setting tracing default failed")
}

fn run_from_cairo_pie(args: impl Iterator<Item = String>) -> Result<ProverInput, Error> {
    let _span = span!(Level::INFO, "run").entered();
    let args = ArgsForPie::try_parse_from(args)?;
    println!("{:#?}", args);
    
    // When running the VM in proof mode, disable trace padding.
    let disable_trace_padding = args.vm_args.proof_mode;
    let cairo_runner = run_vm(&args.vm_args, disable_trace_padding)?;
    let cairo_input = adapt_finished_runner(cairo_runner)?;

    let execution_resources = ExecutionResources::from_prover_input(&cairo_input);
    log::info!("Execution resources: {:#?}", execution_resources);
    std::fs::write(
        args.output_path,
        serde_json::to_string(&execution_resources)?,
    )?;
    Ok(cairo_input)
}

fn run_from_program(args: impl Iterator<Item = String>) -> Result<ProverInput, Error> {
    let _span = span!(Level::INFO, "run").entered();
    let args = ArgsForProgram::try_parse_from(args)?;

    let program = get_program(args.program.as_path())?;
    let program_input_contents = get_program_input(&args.program_input)?;
    let cairo_run_config = cairo_run::CairoRunConfig {
        entrypoint: "main",
        trace_enabled: true,
        relocate_mem: true,
        layout: LayoutName::all_cairo,
        proof_mode: false,
        secure_run: None,
        disable_trace_padding: false,
        allow_missing_builtins: None,
        dynamic_layout_params: None,
    };
    let cairo_runner = cairo_run_program(&program, program_input_contents, cairo_run_config)?;
    let cairo_input = adapt_finished_runner(cairo_runner)?;

    let execution_resources = ExecutionResources::from_prover_input(&cairo_input);
    log::info!("Execution resources: {:#?}", execution_resources);
    std::fs::write(
        args.output_execution_resources_path,
        serde_json::to_string(&execution_resources)?,
    )?;
    Ok(cairo_input)
}



fn main() -> ExitCode {
    tmp_init_logging(log::LevelFilter::Info);
    
    let _tmp_args: Vec<String> = env::args().collect();
    let mode =_tmp_args.get(1);
    let args_iter = env::args();

    let result = match mode {
        None => {
            eprintln!("Error: program must be called with command line arguments");
            return ExitCode::FAILURE;
        }
        Some(s) if s == "--run_from_cairo_pie" => run_from_cairo_pie(args_iter),
        Some(s) if s == "--program" => run_from_program(args_iter),
        _ => {
                eprintln!("Error: The first argument must be either '--run_from_cairo_pie' or '--program'");
                return ExitCode::FAILURE;
        }
    };

    match result {
        Ok(_) => {
            log::info!("stwo_vm_runner succeeded");
            ExitCode::SUCCESS
        }
        Err(error) => {
            log::info!("stwo_vm_runner failed: {}", error);
            ExitCode::FAILURE
        }
    }
}
