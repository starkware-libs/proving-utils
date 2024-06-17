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
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "air_public_input")]
    air_public_input: PathBuf,
    #[clap(long = "air_private_input")]
    air_private_input: PathBuf,
    #[clap(long = "cairo_pies", num_args = 1.., value_delimiter = ',')]
    cairo_pies: Vec<PathBuf>,
    #[clap(
        long = "use_poseidon",
        num_args = 1..,
        value_delimiter = ',',
        help = "A comma separated list of booleans corresponding to whether \
               each CairoPie should use the poseidon or pedersen hash. Must be \
               the same length as cairo_pies.",
        required = true,
    )]
    use_poseidon: Vec<bool>,
    #[clap(long = "layout", default_value = "plain", value_enum)]
    layout: LayoutName,
}

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

    // Build the bootloader input
    let simple_bootloader_input = SimpleBootloaderInput {
        fact_topologies_path: None,
        single_page: false,
        tasks,
    };

    // Note: the method used to set the bootloader input depends on
    // https://github.com/lambdaclass/cairo-vm/pull/1772 and may change depending on review.
    let mut exec_scopes = ExecutionScopes::new();
    insert_simple_bootloader_input(&mut exec_scopes, simple_bootloader_input);

    // Run the bootloader
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
        &[],
        &args
            .cairo_pies
            .iter()
            .map(std::fs::read)
            .collect::<Result<Vec<_>, _>>()?
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>()[..],
        args.use_poseidon,
    )?;

    let mut _runner = cairo_run_simple_bootloader_in_proof_mode(&simple_bootloader_program, tasks)?;

    Ok(())
}
