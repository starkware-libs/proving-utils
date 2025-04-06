use std::{
    io,
    path::{Path, PathBuf},
};

use cairo_vm::{
    cairo_run::CairoRunConfig,
    types::{
        errors::program_errors::ProgramError, layout::CairoLayoutParams, layout_name::LayoutName,
        program::Program,
    },
};

use crate::types::RunMode;

/// Loads a Cairo program from a file.
///
/// This function reads a Cairo program from the specified file path, expecting
/// an entry point named `"main"`. It returns a `Program` instance on success or a
/// `ProgramError` if the file cannot be read or parsed as a valid Cairo program.
///
/// # Arguments
///
/// * `program` - A reference to the file path containing the Cairo program.
///
/// # Errors
///
/// Returns a `ProgramError` if the program file cannot be read or is invalid.
pub fn get_program(program: &Path) -> Result<Program, ProgramError> {
    Program::from_file(program, Some("main"))
}

/// Reads the input for a Cairo program from a file.
///
/// This function checks if an input file is provided. If so, it reads the entire
/// content of the file into a `String` and returns it wrapped in `Some`.
/// If no input file is provided, it returns `Ok(None)`.
///
/// # Arguments
///
/// * `program_input` - An optional file path to the input file.
///
/// # Errors
///
/// Returns an `io::Error` if there is an issue reading the input file.
pub fn get_program_input(program_input: &Option<PathBuf>) -> io::Result<Option<String>> {
    let Some(ref input_path) = program_input else {
        return Ok(None);
    };
    Ok(Some(std::fs::read_to_string(input_path)?))
}

/// Creates a Cairo run configuration based on the provided parameters.
///
/// Depending on the `proof_mode` flag, this function creates a run configuration
/// for either proof or validation. If a dynamic parameters file is provided,
/// the layout must be `LayoutName::dynamic`, and the dynamic layout parameters are read
/// from the file.
///
/// # Arguments
///
/// * `dynamic_params_file` - An optional file path containing dynamic layout parameters.
/// * `layout` - The layout name to use for the run configuration.
/// * `proof_mode` - A boolean flag indicating whether to generate a proof (true) or run in
///   validation mode (false).
/// * `disable_trace_padding` - A boolean flag to disable trace padding (used in proof mode).
/// * `allow_missing_builtins` - A boolean flag to allow missing built-ins (used in validation
///   mode).
///
/// # Returns
///
/// Returns a `CairoRunConfig` instance configured according to the provided parameters.
///
/// # Errors
///
/// Returns an `io::Error` if there is an issue reading the dynamic layout parameters file.
///
/// # Panics
///
/// Panics if `dynamic_params_file` is provided but `layout` is not `LayoutName::dynamic`.
pub fn get_cairo_run_config(
    dynamic_params_file: &Option<PathBuf>,
    layout: LayoutName,
    proof_mode: bool,
    disable_trace_padding: bool,
    allow_missing_builtins: bool,
) -> std::io::Result<CairoRunConfig<'static>> {
    let dynamic_layout_params = match dynamic_params_file {
        Some(file) => {
            assert!(
                layout == LayoutName::dynamic,
                "dynamic_params_file should not be provided for layout {}.",
                layout
            );
            Some(CairoLayoutParams::from_file(file)?)
        }
        None => None,
    };

    Ok(if proof_mode {
        RunMode::Proof {
            layout,
            dynamic_layout_params,
            disable_trace_padding,
        }
        .create_config()
    } else {
        RunMode::Validation {
            layout,
            allow_missing_builtins,
        }
        .create_config()
    })
}
