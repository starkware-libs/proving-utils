use std::path::{Path, PathBuf};
use std::process::Command;

use tempfile::TempDir;

const BINARY: &str = env!("CARGO_BIN_EXE_stwo-vm-runner");

fn resource_path(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("resources")
        .join(name)
}

#[test]
fn runs_with_all_optional_args() {
    let tempdir = TempDir::new().expect("failed to create tempdir");
    let exec_resources = tempdir.path().join("execution_resources.json");
    let prover_input = tempdir.path().join("prover_input.json");
    let vm_exec_resources = tempdir.path().join("vm_execution_resources.json");
    let output_preimage_dump = tempdir.path().join("output_preimage_dump.json");

    let program = resource_path("privacy_simple_bootloader_compiled.json");
    // The fixture input contains a `__OUTPUT_PREIMAGE_DUMP_PATH__` placeholder so the
    // hard-coded absolute path does not leak into CI; substitute a tempfile here.
    let program_input_template = std::fs::read_to_string(resource_path("bl_input.json"))
        .expect("failed to read bl_input.json fixture");
    let program_input_contents = program_input_template.replace(
        "__OUTPUT_PREIMAGE_DUMP_PATH__",
        &output_preimage_dump.to_string_lossy(),
    );
    let program_input = tempdir.path().join("bl_input.json");
    std::fs::write(&program_input, program_input_contents)
        .expect("failed to write resolved program input");

    let output = Command::new(BINARY)
        .args([
            "--program",
            program.to_str().unwrap(),
            "--program_input",
            program_input.to_str().unwrap(),
            "--layout",
            "all_cairo_stwo",
            "--output_execution_resources_path",
            exec_resources.to_str().unwrap(),
            "--output_prover_input_path",
            prover_input.to_str().unwrap(),
            "--output_vm_execution_resources_path",
            vm_exec_resources.to_str().unwrap(),
            "--secure_run",
        ])
        .output()
        .expect("failed to spawn vm-runner");

    assert!(
        output.status.success(),
        "vm-runner exited with {}:\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    for path in [&exec_resources, &prover_input, &vm_exec_resources] {
        let bytes = std::fs::read(path)
            .unwrap_or_else(|e| panic!("failed to read output file {path:?}: {e}"));
        serde_json::from_slice::<serde_json::Value>(&bytes)
            .unwrap_or_else(|e| panic!("output file {path:?} is not valid JSON: {e}"));
    }
}
