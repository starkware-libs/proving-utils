use std::collections::VecDeque;

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

/// Return a vector of TaskSpecs from a list of programs and CairoPies.
/// `use_poseidon` should be a vector of bool corresponding to whether
/// each CairoPie should use the poseidon or pedersen hash function.
pub fn make_bootloader_tasks(
    programs: &[&[u8]],
    pies: &[&[u8]],
    use_poseidon: Vec<bool>,
) -> Result<Vec<TaskSpec>, BootloaderTaskError> {
    let mut use_poseidon_deque: VecDeque<bool> = use_poseidon.into();
    let program_tasks = programs.iter().map(|program_bytes| {
        let program = Program::from_bytes(program_bytes, Some("main"));
        program
            .map(|program| TaskSpec {
                task: Task::Program(program),
                use_poseidon: false,
            })
            .map_err(BootloaderTaskError::Program)
    });

    let cairo_pie_tasks = pies.iter().map(|pie_bytes| {
        let pie = CairoPie::from_bytes(pie_bytes);
        pie.map(|pie| TaskSpec {
            task: Task::Pie(pie),
            use_poseidon: use_poseidon_deque
                .pop_front()
                .expect("Every CairoPie must have a corresponding use_posiedon."),
        })
        .map_err(BootloaderTaskError::Pie)
    });

    program_tasks.chain(cairo_pie_tasks).collect()
}
