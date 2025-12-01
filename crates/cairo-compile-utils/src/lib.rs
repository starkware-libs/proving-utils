use std::process::Command;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use walkdir::WalkDir; // A useful crate for walking directories
use std::env; // Import the env module
use anyhow::{Result, Context};

use std::fs;

fn find_main_file(project_root: &PathBuf) -> anyhow::Result<PathBuf> {
    for entry in WalkDir::new(project_root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| e.file_type().is_file() && e.path().extension().map_or(false, |ext| ext == "cairo"))
    {
        let content = fs::read_to_string(entry.path())?;
        if content.contains("func main") {
            return Ok(entry.path().to_path_buf());
        }
    }

    Err(anyhow::anyhow!(
        "No Cairo 0 file with `func main` found under {:?}",
        project_root
    ))
}

/// Builds a shell-like string representation of a Command for logging/debugging.
/// This is a simplified representation and might not handle all edge cases (e.g., complex quoting).
fn format_command_for_display(cmd: &Command) -> String {
    let mut cmd_str = String::new();

    // Add the program name
    if let Some(program) = cmd.get_program().to_str() {
        cmd_str.push_str(program);
    }

    // Add arguments
    for arg in cmd.get_args() {
        if let Some(s) = arg.to_str() {
            cmd_str.push(' ');
            // Basic quoting for arguments that might contain spaces
            if s.contains(' ') || s.contains('"') || s.contains('\'') {
                cmd_str.push('"');
                cmd_str.push_str(&s.replace('"', "\\\"")); // Escape existing double quotes
                cmd_str.push('"');
            } else {
                cmd_str.push_str(s);
            }
        }
    }

    cmd_str
}

// current_dir should hold the relevant cairo code (only one main)
pub fn compile_cairo_code(current_dir: &PathBuf) -> anyhow::Result<()> {

    println!("Current working directory: {:?}", current_dir);

    // Define the output path for the compiled program (CASM)
    let output_casm_file = PathBuf::from("./target/my_combined_program.json");

    // Ensure the target directory exists
    std::fs::create_dir_all(output_casm_file.parent().unwrap())?;

    println!("Searching for Cairo 0 files in: {:?}", current_dir);

    // Define the main Cairo file to compile
    let main_cairo_file = find_main_file(&current_dir)?;
    println!("Detected main Cairo file: {:?}", main_cairo_file);

    // Check that it exists
    if !main_cairo_file.exists() {
        return Err(anyhow::anyhow!("Main Cairo file not found: {:?}", main_cairo_file));
    }

    println!("Attempting to compile Cairo 0 project to: {:?}", output_casm_file);

    // Build the `cairo-compile` command
    let mut command = Command::new("cairo-compile");

    // Add only the main file
    command.arg(&main_cairo_file);

    println!("Executing the following command: {}", format_command_for_display(&command));
    // Specify the output file
    command.arg("--output").arg(&output_casm_file);

    let cairo_project_root = current_dir.clone();
    // Add the --cairo_path argument using the determined project root
    // This is crucial for resolving 'from starkware.cairo...' imports if 'starkware'
    // is a top-level directory directly under your project root.
    command.arg("--cairo_path").arg(&cairo_project_root);

    // Execute the command
    let output = command.output()?;

    // Check if the command was successful
    if output.status.success() {
        println!("Cairo 0 compilation successful!");
        println!("Compiled program written to: {:?}", output_casm_file);
        io::stdout().write_all(&output.stdout)?;
    } else {
        eprintln!("Cairo 0 compilation failed!");
        eprintln!("Status: {:?}", output.status);
        eprintln!("Stderr:\n{}", String::from_utf8_lossy(&output.stderr));
        return Err(anyhow::anyhow!("Cairo 0 compilation failed: {}", String::from_utf8_lossy(&output.stderr)));
    }

    println!("\nTo run the compiled Cairo 0 program, you would typically use `cairo-run`:");
    println!("`cairo-run --program {}`", output_casm_file.display());
    println!("If `main` is an external function for a StarkNet contract, you'd deploy it.");

    Ok(())
}
