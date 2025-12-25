use anyhow::Result;
use std::path::PathBuf;
use std::process::ExitCode;

use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_program, get_program_input};
use cairo_vm::cairo_run;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
use clap::Parser;
use stwo_cairo_adapter::adapter::adapt;
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

    #[clap(
        long = "output_execution_resources_path",
        help = "Abosolute path to the program's execution resources (output file)."
    )]
    output_execution_resources_path: PathBuf,

    #[clap(
        long = "output_prover_input_path",
        help = "Abosolute path to the prover input (output file)."
    )]
    output_prover_input_path: Option<PathBuf>,

    #[clap(long = "secure_run", help = "Enable secure_run mode in the Cairo VM.")]
    secure_run: bool,
}

#[derive(Debug, Error)]
enum Error {
    #[error("Invalid arguments")]
    Cli(#[from] clap::Error),
    #[error("Failed to interact with the file system")]
    IO(#[from] std::io::Error),
    #[error("Serialization failed: {0}")]
    Serde(#[from] serde_json::Error),
    #[error("ProgramRunner error: {0}")]
    ProgramRunner(#[from] ProgramError),
    #[error("Failed executing the program: {0}")]
    Runner(#[from] CairoRunError),
    #[error(transparent)]
    Anyhow(#[from] anyhow::Error),
}

/// Calculate approximate heap memory usage for a Vec
fn vec_heap_size<T>(vec: &Vec<T>) -> usize {
    vec.capacity() * std::mem::size_of::<T>()
}

/// Calculate approximate heap memory usage for an Option<Vec<T>>
fn option_vec_heap_size<T>(opt_vec: &Option<Vec<T>>) -> usize {
    opt_vec.as_ref().map(|v| vec_heap_size(v)).unwrap_or(0)
}

/// Estimate the total memory usage of CairoRunner by summing accessible components.
/// This is an approximation and may not capture all memory.
fn estimate_cairo_runner_total_size(runner: &CairoRunner) -> usize {
    let mut total = std::mem::size_of_val(runner); // Stack size

    // Add relocated_trace if present.
    total += option_vec_heap_size(&runner.relocated_trace);

    // Add VM memory segments - this is the big one!
    // The memory is stored as a Vec of Option<Felt252> in segments.memory
    // We'll try to estimate based on segment sizes.
    for (_segment_idx, size) in &runner.vm.segments.segment_sizes {
        // Each memory cell is roughly 32 bytes (Felt252) when Some, plus Option overhead.
        total += size * 40; // Rough estimate: 32 bytes + Option + padding
    }

    // Add program data.
    let program = runner.get_program();
    total += program.data_len() * std::mem::size_of::<cairo_vm::types::relocatable::MaybeRelocatable>();

    // Add public_memory_offsets HashMap overhead (rough estimate).
    total += runner.vm.segments.public_memory_offsets.len() * 64;

    total
}

fn main() -> ExitCode {
    run_binary(run, "stwo_vm_runner")
}

#[allow(clippy::result_large_err)]
fn run() -> Result<ProverInput, Error> {
    let _span = span!(Level::INFO, "run").entered();
    let args = Args::parse();

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
        secure_run: args.secure_run.then_some(true),
        disable_trace_padding: true,
        allow_missing_builtins: None,
        dynamic_layout_params: None,
    };

    let cairo_runner = cairo_run_program(&program, program_input_contents, cairo_run_config)?;

    // Log total estimated memory (approximation).
    let estimated_total = estimate_cairo_runner_total_size(&cairo_runner);
    log::info!("=== TOTAL ESTIMATED SIZE ===");
    log::info!("cairo_runner TOTAL (estimated): {} bytes ({} MB, {:.2} GB)",
        estimated_total,
        estimated_total / 1_048_576,
        estimated_total as f64 / 1_073_741_824.0);

    // Log stack sizes (struct sizes).
    log::info!("=== Stack Sizes (struct metadata only) ===");
    log::info!("cairo_runner stack: {} bytes", std::mem::size_of_val(&cairo_runner));
    log::info!("cairo_runner.vm stack: {} bytes", std::mem::size_of_val(&cairo_runner.vm));
    log::info!("cairo_runner.get_program() stack: {} bytes", std::mem::size_of_val(cairo_runner.get_program()));
    log::info!("cairo_runner.exec_scopes stack: {} bytes", std::mem::size_of_val(&cairo_runner.exec_scopes));
    log::info!("cairo_runner.relocated_trace stack: {} bytes", std::mem::size_of_val(&cairo_runner.relocated_trace));

    // Log heap sizes (actual allocated data).
    log::info!("=== Heap Sizes (actual memory consumption) ===");
    log::info!("cairo_runner.relocated_trace heap: {} bytes ({} MB)",
        option_vec_heap_size(&cairo_runner.relocated_trace),
        option_vec_heap_size(&cairo_runner.relocated_trace) / 1_048_576);
    log::info!("cairo_runner.vm.segments (estimated): {} segments",
        cairo_runner.vm.segments.segment_sizes.len());

    // VM segments memory is complex, log the HashMap size.
    log::info!("cairo_runner.vm.segments.public_memory_offsets entries: {}",
        cairo_runner.vm.segments.public_memory_offsets.len());

    let prover_input = adapt(&cairo_runner)?;

    log::info!("=== After Adaptation ===");
    log::info!("prover_input stack: {} bytes", std::mem::size_of_val(&prover_input));
    log::info!("prover_input.public_memory_addresses heap: {} bytes ({} MB)",
        vec_heap_size(&prover_input.public_memory_addresses),
        vec_heap_size(&prover_input.public_memory_addresses) / 1_048_576);

    // Note: prover_input doesn't implement DeepSizeOf, so we can't get total size easily.
    // The memory component is the largest but is opaque to us here.

    if let Some(prover_input_path) = args.output_prover_input_path {
        std::fs::write(prover_input_path, serde_json::to_string(&prover_input)?)?;
    }

    let execution_resources = ExecutionResources::from_prover_input(&prover_input);
    log::info!("Execution resources: {execution_resources:#?}");
    std::fs::write(
        args.output_execution_resources_path,
        serde_json::to_string(&execution_resources)?,
    )?;

    Ok(prover_input)
}
