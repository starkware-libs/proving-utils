use std::error::Error;
use std::path::PathBuf;

use cairo_program_runner::cairo_run_program;
use cairo_program_runner::types::RunMode;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;

fn main() -> Result<(), Box<dyn Error>> {
    let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let simple_bootloader_compiled_path =
        project_dir.join("resources/compiled_programs/bootloaders/simple_bootloader_compiled.json");
    let simple_bootloader_program =
        Program::from_file(simple_bootloader_compiled_path.as_path(), Some("main"))?;
    let fibonacci_compiled_program_path = project_dir.join("examples/fibonacci.json");
    let program_input_contents = format!(
        r#"{{
            "tasks": [
              {{
                "path": "{}",
                "use_poseidon": false,
                "type": "RunProgramTask"
              }}
            ],
            "single_page": true
        }}"#,
        fibonacci_compiled_program_path.display()
    );

    let cairo_run_config = RunMode::Proof {
        layout: LayoutName::starknet_with_keccak,
        dynamic_layout_params: None,
    }
    .create_config();

    let mut runner = cairo_run_program(
        &simple_bootloader_program,
        Some(program_input_contents),
        cairo_run_config,
    )?;

    let mut output_buffer = "Program Output:\n".to_string();
    runner.vm.write_output(&mut output_buffer)?;
    print!("{output_buffer}");

    Ok(())
}
