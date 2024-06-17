use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::program::Program;

pub use crate::hints::*;

// The 0.13.0 bootloader is used just for the example.
const BOOTLOADER_V0_13_0: &[u8] = include_bytes!("../resources/bootloader-0.13.0.json");
// The latest simple bootloader, compiled on sharp-6.0 and copied here.
const SIMPLE_BOOTLOADER_LATEST: &[u8] =
    include_bytes!("../resources/simple_bootloader-latest.json");

/// Loads the bootloader and returns it as a Cairo VM `Program` object.
pub fn load_bootloader() -> Result<Program, ProgramError> {
    Program::from_bytes(BOOTLOADER_V0_13_0, Some("main"))
}

/// Loads the simple bootloader and returns it as a Cairo VM `Program` object.
pub fn load_simple_bootloader() -> Result<Program, ProgramError> {
    Program::from_bytes(SIMPLE_BOOTLOADER_LATEST, Some("main"))
}
