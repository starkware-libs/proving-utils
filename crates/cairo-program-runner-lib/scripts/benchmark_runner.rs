//! Benchmark Runner for Cairo PIE Files
//!
//! This program measures the performance of loading and executing Cairo PIEs
//! wrapped in simple bootloader and ran by the Cairo Program Runner.
//!
//! Usage:
//!   cargo run --bin benchmark_runner <path_to_pie_file> [--show-output]
//!
//! Arguments:
//!   <path_to_pie_file>  Path to the Cairo PIE file (.zip) to benchmark
//!   --show-output       Optional flag to display program output
//!
//! Output:
//!   - Program load time
//!   - Program execution time
//!   - Total runtime
//!   - Execution resources (steps, memory holes, builtin counters)
//!
//! This binary is typically run through the run_all_pies.sh script, which provides
//! additional features:
//!   - Running multiple PIE files
//!   - Testing different Rust optimization levels
//!   - Aggregating results into a single file
//!
//! Example:
//!   Direct usage:
//!     cargo run --bin benchmark_runner path/to/program.zip
//!   Via script:
//!     ./scripts/run_all_pies.sh --opt-levels=3 --pie-dir=path/to/pies

use std::error::Error;
use std::path::PathBuf;
use std::time::Instant;

use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::types::RunMode;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::CairoPie;

fn main() -> Result<(), Box<dyn Error>> {
    let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let simple_bootloader_compiled_path =
        project_dir.join("resources/compiled_programs/bootloaders/simple_bootloader_compiled.json");

    // Parse command line args
    let args: Vec<String> = std::env::args().collect();
    let mut program_path = String::new();
    let mut show_output = false;

    // Simple arg parsing
    for (i, arg) in args.iter().enumerate() {
        if arg == "--show-output" {
            show_output = true;
        } else if i > 0 && !arg.starts_with("--") {
            program_path = arg.clone();
        }
    }

    if program_path.is_empty() {
        program_path = project_dir
            .join("examples/fibonacci.json")
            .display()
            .to_string();
    }

    println!("Loading program from: {}", program_path);

    // Try to load as a PIE first, if that fails, try as a regular program
    let start_load = Instant::now();
    let program_input_contents = if program_path.ends_with(".zip") {
        // Load as PIE - we just need to verify it loads
        // TODO(idanh): Add an option to configure the hash function
        let _cairo_pie = CairoPie::read_zip_file(&PathBuf::from(&program_path))?;
        format!(
            r#"{{
                "tasks": [
                  {{
                    "type": "CairoPiePath",
                    "path": "{}",
                    "program_hash_function": "pedersen"
                  }}
                ],
                "single_page": true
            }}"#,
            program_path
        )
    } else {
        // Load as regular program - we just need to verify it loads
        let _program = Program::from_file(PathBuf::from(&program_path).as_path(), Some("main"))?;
        format!(
            r#"{{
                "tasks": [
                  {{
                    "path": "{}",
                    "program_hash_function": "pedersen",
                    "type": "RunProgramTask"
                  }}
                ],
                "single_page": true
            }}"#,
            program_path
        )
    };
    let load_duration = start_load.elapsed();
    println!("Program loaded in: {:?}", load_duration);

    let simple_bootloader_program =
        Program::from_file(simple_bootloader_compiled_path.as_path(), Some("main"))?;

    let cairo_run_config = RunMode::Proof {
        layout: LayoutName::starknet_with_keccak,
        dynamic_layout_params: None,
        disable_trace_padding: false,
    }
    .create_config();

    println!("\nExecuting program...");
    let start_exec = Instant::now();
    let mut runner = cairo_run_program(
        &simple_bootloader_program,
        Some(program_input_contents),
        cairo_run_config,
    )?;
    let exec_duration = start_exec.elapsed();
    println!("Program executed in: {:?}", exec_duration);

    // Verify execution by checking outputs
    let mut output_buffer = String::new();
    runner.vm.write_output(&mut output_buffer)?;

    // Print execution verification info
    println!("\nProgram Execution Verification:");
    println!("Output size: {} bytes", output_buffer.len());

    if show_output {
        println!("Program output:\n{}", output_buffer);
    }

    // Print execution resources
    println!("\nExecution Resources:");
    let resources = runner.get_execution_resources()?;
    println!("n_steps: {}", resources.n_steps);
    println!("n_memory_holes: {}", resources.n_memory_holes);
    println!(
        "builtin_instance_counter: {:#?}",
        resources.builtin_instance_counter
    );

    // Check if output is empty - might indicate optimization skip
    if output_buffer.trim().is_empty() {
        println!("WARNING: Empty output might indicate optimization issues!");
    }

    println!("\nBenchmark Summary:");
    println!("Program load time: {:?}", load_duration);
    println!("Program execution time: {:?}", exec_duration);
    println!("Total time: {:?}", load_duration + exec_duration);

    Ok(())
}
