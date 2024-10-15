use cairo_vm::cairo_run::{cairo_run_program_with_initial_scope, CairoRunConfig};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout::CairoLayoutParams;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;

pub use hints::*;

mod hints;
pub mod tasks;

pub fn cairo_run_program_in_proof_mode(
    program: &Program,
    program_name: &str,
    program_input_contents: String,
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

    let mut exec_scopes = ExecutionScopes::new();

    if program_name.contains("simple_bootloader") {
        let simple_bootloader_input: SimpleBootloaderInput =
            serde_json::from_str(&program_input_contents).unwrap();

        // Note: the method used to set the bootloader input depends on
        // https://github.com/lambdaclass/cairo-vm/pull/1772 and may change depending on review.
        exec_scopes.insert_value(SIMPLE_BOOTLOADER_INPUT, simple_bootloader_input);
        exec_scopes.insert_value(BOOTLOADER_PROGRAM_IDENTIFIERS, program.clone());
    } else if program_name.contains("applicative_bootloader") {
        // Handle the applicative bootloader case.
    } else if program_name.contains("bootloader") {
        // Handle the unpacker bootloader case.
    } else if program_name.contains("cairo_verifier") {
        // Handle the verifier case.
    } else {
        // For other programs, throw CairoRunError
    }

    // Run the program with the configured execution scopes
    cairo_run_program_with_initial_scope(
        program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}
