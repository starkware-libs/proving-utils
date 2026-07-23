#![cfg(feature = "slow-tests")]

use std::fs;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn run_leaf_prover_binary() {
    let tmp_dir = tempfile::tempdir().expect("Cannot create temporary directory");
    let tmp_dir_path = tmp_dir.path();
    let crate_root = PathBuf::from(
        std::env::var("CARGO_MANIFEST_DIR")
            .expect("Missing environment variable CARGO_MANIFEST_DIR"),
    );
    let test_data_dir = crate_root.join("tests/data");
    let binary_path = std::env::var("CARGO_BIN_EXE_leaf-prover")
        .expect("Missing environment variable CARGO_BIN_EXE_leaf-prover");

    let output_path = tmp_dir_path.join("leaf_prover_output.json");
    let status = Command::new(binary_path)
        .arg("--program")
        .arg(test_data_dir.join("use_all_opcodes_and_builtins_compiled.json"))
        .arg("--cairo-prover-params-json")
        .arg(test_data_dir.join("cairo_prover_params_canonical_small.json"))
        .arg("--circuit-prover-params-json")
        .arg(test_data_dir.join("circuit_prover_params_canonical_small.json"))
        .arg("--circuit-registry-json")
        .arg(test_data_dir.join("registry.json"))
        .arg("--output-path")
        .arg(&output_path)
        .status()
        .expect("Cannot get exit status");
    assert!(status.success(), "binary exited with status: {status}");

    let output = fs::read_to_string(output_path).unwrap();
    let expected_output_path = test_data_dir.join("expected_output.json");
    if std::env::var("FIX").is_ok() {
        fs::write(&expected_output_path, &output).unwrap_or_else(|err| {
            panic!("Error writing to {}: {err}", expected_output_path.display())
        });
    } else {
        let expected_output = fs::read_to_string(&expected_output_path)
            .unwrap_or_else(|err| panic!("Cannot read {}: {err}", expected_output_path.display()));
        assert!(
            output == expected_output,
            "Leaf prover output != expected. Run with FIX=1 to fix expected output."
        );
    }
}
