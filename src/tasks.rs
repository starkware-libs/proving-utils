use std::path::Path;

use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::CairoPie;

use crate::{Task, TaskSpec};

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
/// - `use_poseidon`: A boolean indicating if Poseidon hashing should be used.
///
/// # Returns
/// - `Ok(TaskSpec)`: On success, returns a `TaskSpec` with the loaded program task and the Poseidon option.
/// - `Err(BootloaderTaskError)`: On failure, returns a `BootloaderTaskError::Program` if there's an issue
///    with loading the program file.
pub fn create_program_task_spec(
    program_path: &Path,
    use_poseidon: bool,
) -> Result<TaskSpec, BootloaderTaskError> {
    let program =
        Program::from_file(program_path, Some("main")).map_err(BootloaderTaskError::Program)?;
    Ok(TaskSpec {
        task: Task::Program(program),
        use_poseidon,
    })
}

/// Creates a `TaskSpec` for a Cairo PIE task by reading it from a zip file.
///
/// # Arguments
/// - `pie_path`: A reference to a `Path` where the Cairo PIE file is located.
/// - `use_poseidon`: A boolean indicating if Poseidon hashing should be used.
///
/// # Returns
/// - `Ok(TaskSpec)`: On success, returns a `TaskSpec` with the loaded Cairo PIE task and the Poseidon option.
/// - `Err(BootloaderTaskError)`: On failure, returns a `BootloaderTaskError::Pie` if there's an issue
///    with reading the Cairo PIE file.
pub fn create_pie_task_spec(
    pie_path: &Path,
    use_poseidon: bool,
) -> Result<TaskSpec, BootloaderTaskError> {
    let pie = CairoPie::read_zip_file(pie_path).map_err(BootloaderTaskError::Pie)?;
    Ok(TaskSpec {
        task: Task::Pie(pie),
        use_poseidon,
    })
}
