use std::path::PathBuf;

use cairo_vm::cairo_run::{cairo_run_program_with_initial_scope, CairoRunConfig};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout::CairoLayoutParams;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;

pub use hints::*;

pub mod bootloaders;
mod hints;
pub mod tasks;

/// Inserts the bootloader input in the execution scopes.
pub fn insert_bootloader_input(
    exec_scopes: &mut ExecutionScopes,
    bootloader_input: BootloaderInput,
) {
    exec_scopes.insert_value(BOOTLOADER_INPUT, bootloader_input);
}

pub fn insert_simple_bootloader_input(
    exec_scopes: &mut ExecutionScopes,
    simple_bootloader_input: SimpleBootloaderInput,
) {
    exec_scopes.insert_value(SIMPLE_BOOTLOADER_INPUT, simple_bootloader_input);
}

pub fn cairo_run_simple_bootloader_in_proof_mode(
    simple_bootloader_program: &Program,
    tasks: Vec<TaskSpec>,
    fact_topologies_path: Option<PathBuf>,
    layout: LayoutName,
    dynamic_layout_params: Option<CairoLayoutParams>,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let cairo_run_config = CairoRunConfig {
        entrypoint: "main",
        trace_enabled: true,
        relocate_mem: true,
        layout,
        proof_mode: true,
        secure_run: None,
        disable_trace_padding: false,
        allow_missing_builtins: None,
        dynamic_layout_params,
    };

    // Build the bootloader input
    let simple_bootloader_input = SimpleBootloaderInput {
        fact_topologies_path,
        single_page: true,
        tasks,
    };

    // Note: the method used to set the bootloader input depends on
    // https://github.com/lambdaclass/cairo-vm/pull/1772 and may change depending on review.
    let mut exec_scopes = ExecutionScopes::new();
    insert_simple_bootloader_input(&mut exec_scopes, simple_bootloader_input);
    exec_scopes.insert_value(
        BOOTLOADER_PROGRAM_IDENTIFIERS,
        simple_bootloader_program.clone(),
    );

    // Run the bootloader
    cairo_run_program_with_initial_scope(
        simple_bootloader_program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}
