use std::path::Path;

use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::CairoPie;

use crate::{ProgramWithInput, Task};

#[derive(thiserror::Error, Debug)]
pub enum BootloaderTaskError {
    #[error("Failed to read program: {0}")]
    Program(#[from] ProgramError),

    #[error("Failed to read PIE: {0}")]
    Pie(#[from] std::io::Error),
}

/// Creates a `TaskSpec` for a program task by loading a program from a specified file path.
///
/// # Arguments
/// - `program_path`: A reference to a `Path` where the program file is located.
///
/// # Returns
/// - `Ok(Task)`: On success, returns a `Task` with the loaded program.
/// - `Err(BootloaderTaskError)`: On failure, returns a `BootloaderTaskError::Program` if there's an
///   issue with loading the program file.
pub fn create_program_task(
    program_path: &Path,
    program_input: Option<String>,
) -> Result<Task, BootloaderTaskError> {
    let program =
        Program::from_file(program_path, Some("main")).map_err(BootloaderTaskError::Program)?;
    Ok(Task::Program(ProgramWithInput {
        program,
        program_input,
    }))
}

/// Creates a `TaskSpec` for a Cairo PIE task by reading it from a zip file.
///
/// # Arguments
/// - `pie_path`: A reference to a `Path` where the Cairo PIE file is located.
///
/// # Returns
/// - `Ok(Task)`: On success, returns a `Task` with the loaded Cairo PIE.
/// - `Err(BootloaderTaskError)`: On failure, returns a `BootloaderTaskError::Pie` if there's an
///   issue with reading the Cairo PIE file.
pub fn create_pie_task(pie_path: &Path) -> Result<Task, BootloaderTaskError> {
    let pie = CairoPie::read_zip_file(pie_path).map_err(BootloaderTaskError::Pie)?;
    Ok(Task::Pie(pie))
}
