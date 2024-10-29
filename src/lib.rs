use cairo_vm::cairo_run::{cairo_run_program_with_initial_scope, CairoRunConfig};
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout::CairoLayoutParams;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
pub use hints::*;
use std::io::{self, ErrorKind};

mod hints;
pub mod tasks;
enum RunMode {
    CairoRunner {
        layout: LayoutName,
        dynamic_layout_params: Option<CairoLayoutParams>,
    },
    Validator,
}

impl RunMode {
    fn create_config(self) -> CairoRunConfig<'static> {
        match self {
            RunMode::CairoRunner {
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
            RunMode::Validator => CairoRunConfig {
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

/// Executes a specified Cairo program based on its name and configuration, with conditional
/// handling of input types depending on the program variant.
///
/// # Arguments
/// - `program`: A reference to a `Program` object that will be run.
/// - `program_name`: A string slice representing the name of the program, used to determine the
///   appropriate execution behavior.
/// - `program_input_contents`: A `String` containing the program's input data (JSON format).
/// - `layout`: A `LayoutName` specifying the Cairo layout to use in the vm.
/// - `dynamic_layout_params`: Optional `CairoLayoutParams` that can specify additional dynamic
///   parameters for the layout. Used with dynamic layouts only.
///
/// # Returns
/// - `Ok(CairoRunner)`: If the program is successfully run, returns the `CairoRunner` object.
/// - `Err(CairoRunError)`: If an error occurs, returns a `CairoRunError` describing the problem.
pub fn cairo_run_program(
    program: &Program,
    program_name: &str,
    program_input_contents: String,
    layout: LayoutName,
    dynamic_layout_params: Option<CairoLayoutParams>,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let mut exec_scopes = ExecutionScopes::new();

    let cairo_run_config = if program_name.contains("applicative_bootloader")
        || program_name.contains("cairo_verifier")
    {
        RunMode::Validator.create_config()
    } else {
        RunMode::CairoRunner {
            layout,
            dynamic_layout_params,
        }
        .create_config()
    };

    // The following attribute is used to make clippy ignore the repeated if-else block. Should be
    // removed all blocks are implemented.
    #[allow(clippy::if_same_then_else)]
    if program_name.contains("simple_bootloader") {
        let simple_bootloader_input: SimpleBootloaderInput =
            serde_json::from_str(&program_input_contents).unwrap();

        // Note: the method used to set the bootloader input depends on
        // https://github.com/lambdaclass/cairo-vm/pull/1772 and may change depending on review.
        exec_scopes.insert_value(SIMPLE_BOOTLOADER_INPUT, simple_bootloader_input);
    } else if program_name.contains("applicative_bootloader") {
        let io_error = io::Error::new(
            ErrorKind::Other,
            format!("Unimplemented program variant: {}", program_name),
        );
        return Err(CairoRunError::Program(ProgramError::IO(io_error)));
    } else if program_name.contains("bootloader") {
        let io_error = io::Error::new(
            ErrorKind::Other,
            format!("Unimplemented program variant: {}", program_name),
        );
        return Err(CairoRunError::Program(ProgramError::IO(io_error)));
    } else if program_name.contains("cairo_verifier") {
        let cairo_verifier_input: CairoVerifierInput =
            serde_json::from_str(&program_input_contents).unwrap();
        exec_scopes.insert_value(VERIFIER_PROOF_INPUT, cairo_verifier_input.proof.clone());
    } else {
        let io_error = io::Error::new(
            ErrorKind::Other,
            format!("Unrecognized program variant: {}", program_name),
        );
        return Err(CairoRunError::Program(ProgramError::IO(io_error)));
    }

    // Insert the program object into the execution scopes
    exec_scopes.insert_value(PROGRAM_OBJECT, program.clone());
    // Run the program with the configured execution scopes and cairo_run_config
    cairo_run_program_with_initial_scope(
        program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}
