///! Runs the simple bootloader on input tasks.
///!
///! Example:
///!     run_simple_bootloader --air_public_input /tmp/pub_inp --air_private_input /tmp/priv_inp --cairo_pies /tmp/pie0.zip,/tmp/pie1.zip --layout all_cairo
use std::env;
use std::error::Error;
use std::path::PathBuf;

use cairo_vm::cairo_run::{cairo_run_program_with_initial_scope, CairoRunConfig};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;

use cairo_bootloader::bootloaders::load_simple_bootloader;
use cairo_bootloader::tasks::make_bootloader_tasks;
use cairo_bootloader::{
    insert_simple_bootloader_input, BootloaderHintProcessor, SimpleBootloaderInput, TaskSpec,
};
use clap::Parser;

#[derive(Parser, Debug)]
#[clap()]
struct Args {
    #[clap(
        long = "air_public_input",
        help = "The AIR public input, an output of the simple bootloader run.",
        required = true
    )]
    air_public_input: PathBuf,
    #[clap(
        long = "air_private_input",
        help = "The AIR private input, an output of the simple bootloader run.",
        required = true
    )]
    air_private_input: PathBuf,
    #[clap(
        long = "cairo_pies",
        num_args = 1..,
        value_delimiter = ',',
        help = "A comma separated list of CairoPIEs to run.",
        required = true
    )]
    cairo_pies: Vec<PathBuf>,
    #[clap(long = "layout", default_value = "plain", value_enum)]
    layout: LayoutName,
}

/// Runs the simple bootloader program given tasks.
fn cairo_run_simple_bootloader_in_proof_mode(
    simple_bootloader_program: &Program,
    tasks: Vec<TaskSpec>,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let cairo_run_config = CairoRunConfig {
        entrypoint: "main",
        trace_enabled: false,
        relocate_mem: false,
        layout: LayoutName::all_cairo,
        proof_mode: true,
        secure_run: None,
        disable_trace_padding: false,
        allow_missing_builtins: None,
    };

    // Build the input for the simple bootloader.
    let simple_bootloader_input = SimpleBootloaderInput {
        fact_topologies_path: None,
        single_page: true,
        tasks,
    };

    let mut exec_scopes = ExecutionScopes::new();
    insert_simple_bootloader_input(&mut exec_scopes, simple_bootloader_input);

    // Run the simple bootloader.
    cairo_run_program_with_initial_scope(
        simple_bootloader_program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = match Args::try_parse_from(env::args()) {
        Ok(args) => args,
        Err(err) => err.exit(),
    };

    let simple_bootloader_program = load_simple_bootloader()?;

    let tasks = make_bootloader_tasks(
        // programs
        &[],
        // pies
        &args
            .cairo_pies
            .iter()
            .map(std::fs::read)
            .collect::<Result<Vec<_>, _>>()?
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>()[..],
    )?;

    let mut _runner = cairo_run_simple_bootloader_in_proof_mode(&simple_bootloader_program, tasks)?;

    Ok(())
}
