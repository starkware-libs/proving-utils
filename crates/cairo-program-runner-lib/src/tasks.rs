use std::{
    path::{Path, PathBuf},
    str::FromStr,
};

use cairo_lang_executable::executable::EntryPointKind;
use cairo_lang_executable::executable::Executable;
use cairo_lang_execute_utils::{program_and_hints_from_executable, user_args_from_flags};
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::CairoPie;
use num_bigint::BigInt;
use serde_json::Value;

use crate::{types::Cairo1Executable, Cairo0Executable, Task};

#[derive(thiserror::Error, Debug)]
pub enum BootloaderTaskError {
    #[error("Failed to read program: {0}")]
    Program(#[from] ProgramError),

    #[error("Failed to read PIE: {0}")]
    Pie(#[from] std::io::Error),

    #[error("Cairo1 error: {0}")]
    Cairo1(String),
}

/// Creates a `TaskSpec` for a cairo0 program task by loading a program from a specified file path.
///
/// # Arguments
/// - `program_path`: A reference to a `Path` where the program file is located.
///
/// # Returns
/// - `Ok(Task)`: On success, returns a `Task` with the loaded program.
/// - `Err(BootloaderTaskError)`: On failure, returns a `BootloaderTaskError::Program` if there's an
///   issue with loading the program file.
pub fn create_cairo0_program_task(
    program_path: &Path,
    program_input: Option<String>,
) -> Result<Task, BootloaderTaskError> {
    let program =
        Program::from_file(program_path, Some("main")).map_err(BootloaderTaskError::Program)?;
    Ok(Task::Cairo0Program(Cairo0Executable {
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

pub fn create_cairo1_program_task(
    path: &PathBuf,
    user_args_list: Option<Vec<Value>>,
    user_args_file: Option<PathBuf>,
) -> Result<Task, BootloaderTaskError> {
    let file = std::fs::File::open(path)
        .map_err(|e| BootloaderTaskError::Cairo1(format!("Failed to open file: {e:?}")))?;
    let executable: Executable = serde_json::from_reader(file).map_err(|e| {
        BootloaderTaskError::Cairo1(format!("Failed reading prebuilt executable: {e:?}"))
    })?;
    let user_args_list: Vec<BigInt> = user_args_list
        .unwrap_or_default()
        .iter()
        .map(|n| BigInt::from_str(&n.to_string()).unwrap())
        .collect();

    executable
        .entrypoints
        .iter()
        .find(|e| matches!(e.kind, EntryPointKind::Bootloader))
        .ok_or_else(|| {
            BootloaderTaskError::Cairo1(format!(
                "{:?} entrypoint not found",
                EntryPointKind::Bootloader
            ))
        })?;
    let standalone = false;
    let (program, string_to_hint) = program_and_hints_from_executable(&executable, standalone)
        .map_err(|e| BootloaderTaskError::Cairo1(format!("Failed to parse executable: {e:?}")))?;
    let user_args = user_args_from_flags(user_args_file.as_ref(), &user_args_list)
        .map_err(|e| BootloaderTaskError::Cairo1(format!("Failed to parse user args: {e:?}")))?;
    Ok(Task::Cairo1Program(Cairo1Executable {
        program,
        user_args,
        string_to_hint,
    }))
}
