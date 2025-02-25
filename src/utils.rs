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

// TODO(yg): doc
pub fn get_program(program: &Path) -> Result<Program, ProgramError> {
    Program::from_file(program, Some("main"))
}

// TODO(yg): doc
pub fn get_program_input(program_input: &Option<PathBuf>) -> io::Result<Option<String>> {
    let Some(ref input_path) = program_input else {
        return Ok(None);
    };
    Ok(Some(std::fs::read_to_string(input_path)?))
}

// TODO(yg): doc
pub fn get_cairo_run_config(
    dynamic_params_file: &Option<PathBuf>,
    layout: LayoutName,
    proof_mode: bool,
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
        }
        .create_config()
    } else {
        RunMode::Validation.create_config()
    })
}
