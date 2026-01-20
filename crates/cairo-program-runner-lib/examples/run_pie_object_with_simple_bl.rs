use std::error::Error;
use std::path::{Path, PathBuf};

use cairo_program_runner_lib::types::{HashFunc, RunMode};
use cairo_program_runner_lib::{
    cairo_run_program, ProgramInput, SimpleBootloaderInput, Task, TaskSpec,
};
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;

fn prepare_fibonnaci_pie_task_spec(project_dir: &Path) -> Result<TaskSpec, Box<dyn Error>> {
    let fibonacci_compiled_program_path = project_dir.join("examples/fibonacci.json");
    let fibonnaci_program =
        Program::from_file(fibonacci_compiled_program_path.as_path(), Some("main"))?;

    let cairo_run_config = RunMode::Validation {
        layout: LayoutName::small,
        allow_missing_builtins: false,
    }
    .create_config();
    let runner = cairo_run_program(&fibonnaci_program, None, cairo_run_config)?;
    let result_pie = runner.get_cairo_pie()?;
    let pie_task: Task = Task::Pie(result_pie);
    Ok(TaskSpec {
        task: pie_task.into(),
        program_hash_function: HashFunc::Blake,
    })
}

fn main() -> Result<(), Box<dyn Error>> {
    let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let pie_task_spec = prepare_fibonnaci_pie_task_spec(&project_dir)?;
    let simple_bootloader_input: SimpleBootloaderInput = SimpleBootloaderInput {
        fact_topologies_path: None,
        single_page: true,
        tasks: vec![pie_task_spec],
    };
    let simple_bootloader_compiled_path =
        project_dir.join("resources/compiled_programs/bootloaders/simple_bootloader_compiled.json");
    let simple_bootloader_program =
        Program::from_file(simple_bootloader_compiled_path.as_path(), Some("main"))?;
    let cairo_run_config = RunMode::Proof {
        layout: LayoutName::starknet_with_keccak,
        dynamic_layout_params: None,
        disable_trace_padding: false,
        relocate_mem: true,
    }
    .create_config();

    let mut runner = cairo_run_program(
        &simple_bootloader_program,
        Some(ProgramInput::Value(Box::new(simple_bootloader_input))),
        cairo_run_config,
    )?;

    let mut output_buffer = "Program Output:\n".to_string();
    runner.vm.write_output(&mut output_buffer)?;
    print!("{output_buffer}");

    Ok(())
}
