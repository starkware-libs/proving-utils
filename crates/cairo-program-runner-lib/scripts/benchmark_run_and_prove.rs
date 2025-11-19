// benchmark_run_and_prove.rs
// Usage: cargo run --bin benchmark_run_and_prove <path_to_pie_file> [--show-output]
//
// This program benchmarks proving a Cairo PIE file using the simple bootloader as the program
// and the PIE as the program input. It prints load/prove times and proof status.

use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::time::Instant;

fn main() -> Result<(), Box<dyn Error>> {
    let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let simple_bootloader_compiled_path =
        project_dir.join("resources/compiled_programs/bootloaders/simple_bootloader_compiled.json");

    // Print and check for simple_bootloader_compiled.json
    println!(
        "Looking for simple_bootloader_compiled.json at: {:?}",
        simple_bootloader_compiled_path
    );
    if !simple_bootloader_compiled_path.exists() {
        eprintln!(
            "ERROR: File does not exist: {:?}",
            simple_bootloader_compiled_path
        );
    }

    // Parse command line args
    let args: Vec<String> = std::env::args().collect();
    let mut pie_path = None;
    let mut show_output = false;
    for (i, arg) in args.iter().enumerate() {
        if arg == "--show-output" {
            show_output = true;
        } else if i > 0 && !arg.starts_with("--") {
            pie_path = Some(arg.clone());
        }
    }
    let pie_path = match pie_path {
        Some(p) => p,
        None => {
            eprintln!("Usage: {} <path_to_pie_file> [--show-output]", args[0]);
            std::process::exit(1);
        }
    };

    println!("Proving PIE: {}", pie_path);
    let start = Instant::now();

    // Build the correct program_input JSON for a PIE file
    let program_input_json = format!(
        r#"{{
            "tasks": [
                {{
                    "type": "CairoPiePath",
                    "path": "{}",
                    "program_hash_function": "blake"
                }}
            ],
            "single_page": true
        }}"#,
        pie_path
    );
    // Write the JSON to a temporary file
    let tmp_input_path = "temp_pie_input.json";
    let mut tmp_file = File::create(tmp_input_path)?;
    tmp_file.write_all(program_input_json.as_bytes())?;

    // Get absolute path to prover_params.json (use the one in the same directory as this script)
    let prover_params_path = project_dir.join("scripts/prover_params.json");
    println!(
        "Looking for prover_params.json at: {}",
        prover_params_path.display()
    );
    if !prover_params_path.exists() {
        eprintln!(
            "ERROR: File does not exist: {}",
            prover_params_path.display()
        );
    }

    // Use the full path to the stwo_run_and_prove binary in target/release (fix path: remove
    // 'crates/')
    let stwo_bin_path = project_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("target/release/stwo_run_and_prove");
    println!(
        "Using stwo_run_and_prove binary at: {}",
        stwo_bin_path.display()
    );
    if !stwo_bin_path.exists() {
        eprintln!(
            "ERROR: stwo_run_and_prove binary not found at {}",
            stwo_bin_path.display()
        );
        std::process::exit(1);
    }

    // Print the command being run for debugging (for display only)
    println!(
        "Running command: {} --program=\"{}\" --program_input=\"{}\" --proofs_dir=temp_proofs --proof-format=cairo-serde --verify --prover_params_json=\"{}\" --program_output=temp_outputs",
        stwo_bin_path.display(),
        simple_bootloader_compiled_path.display(),
        tmp_input_path,
        prover_params_path.display()
    );

    // Call stwo_run_and_prove binary with the bootloader as program and the PIE as program_input
    let output = Command::new(&stwo_bin_path)
        .arg(format!(
            "--program={}",
            simple_bootloader_compiled_path.display()
        ))
        .arg(format!("--program_input={}", tmp_input_path))
        .arg("--proofs_dir=temp_proofs")
        .arg("--proof-format=cairo-serde")
        .arg("--verify")
        .arg(format!(
            "--prover_params_json={}",
            prover_params_path.display()
        ))
        .arg("--program_output=temp_outputs")
        .output()?;
    let elapsed = start.elapsed();
    if output.status.success() {
        println!(
            "SUCCESS: Proved {} in {:.3} seconds",
            pie_path,
            elapsed.as_secs_f64()
        );
        if show_output {
            println!("stdout:\n{}", String::from_utf8_lossy(&output.stdout));
        }
    } else {
        println!(
            "ERROR: Failed to prove {} (exit code {:?})",
            pie_path,
            output.status.code()
        );
        println!("stderr:\n{}", String::from_utf8_lossy(&output.stderr));
    }
    Ok(())
}
