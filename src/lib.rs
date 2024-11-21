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
enum RunMode {
    Proof {
        layout: LayoutName,
        dynamic_layout_params: Option<CairoLayoutParams>,
    },
    Validation,
}

impl RunMode {
    fn create_config(self) -> CairoRunConfig<'static> {
        match self {
            RunMode::Proof {
                layout,
                dynamic_layout_params,
            } => CairoRunConfig {
                entrypoint: "main",
                trace_enabled: true,
                relocate_mem: true,
                layout,
                proof_mode: true,
                secure_run: None,
                disable_trace_padding: false,
                allow_missing_builtins: None,
                dynamic_layout_params,
            },
            RunMode::Validation => CairoRunConfig {
                entrypoint: "main",
                trace_enabled: false,
                relocate_mem: false,
                layout: LayoutName::all_cairo,
                proof_mode: false,
                secure_run: None,
                disable_trace_padding: false,
                allow_missing_builtins: None,
                dynamic_layout_params: None,
            },
        }
    }
}

/// Executes a Cairo program with the given configuration, optionally handling program input and
/// proof mode.
///
/// # Arguments
/// - `program`: A reference to a `Program` object that represents the compiled Cairo program to
///   run.
/// - `program_input_contents`: An optional `String` containing the program's input data in JSON
///   format. If `Some`, the input is injected into the execution scope under the key
///   `"program_input"`.
/// - `layout`: A `LayoutName` specifying the Cairo layout to use in the VM (e.g., `plain`,
///   `all_cairo`).
/// - `dynamic_layout_params`: An optional `CairoLayoutParams` providing dynamic parameters for the
///   layout. This is used only if the `dynamic` layout is selected.
/// - `proof_mode`: A `bool` indicating whether to run the program in proof mode (`true`) or
///   validation mode (`false`).
///
/// # Returns
/// - `Ok(CairoRunner)`: If the program runs successfully, returns the `CairoRunner` instance
///   containing the execution state.
/// - `Err(CairoRunError)`: If an error occurs during execution, returns a `CairoRunError`
///   describing the problem.
pub fn cairo_run_program(
    program: &Program,
    program_input_contents: Option<String>,
    layout: LayoutName,
    dynamic_layout_params: Option<CairoLayoutParams>,
    proof_mode: bool,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let mut exec_scopes = ExecutionScopes::new();

    let cairo_run_config = if proof_mode {
        RunMode::Proof {
            layout,
            dynamic_layout_params,
        }
        .create_config()
    } else {
        RunMode::Validation.create_config()
    };

    if let Some(program_input_contents) = program_input_contents {
        // Insert the program input into the execution scopes if exists
        exec_scopes.insert_value(PROGRAM_INPUT, program_input_contents);
    }

    // Insert the program object into the execution scopes
    exec_scopes.insert_value(PROGRAM_OBJECT, program.clone());

    // Run the program with the configured execution scopes and cairo_run_config
    let runner = cairo_run_program_with_initial_scope(
        program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )?;

    Ok(runner)
}
