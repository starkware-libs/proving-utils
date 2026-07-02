//! Binary-level integration test for the `stwo_run_and_prove_recursive_tree` CLI.
//!
//! The happy path now requires real circuit-proof leaves (produced by `leaf_prover`) and builds the
//! canonical circuit shape, so it lives in the feature-gated `slow-tests` end-to-end test. Here we
//! only cover the cheap error arm: a malformed leaves file must make the binary exit non-zero.

use std::process::Command;

/// A malformed `--program_input` makes `load_leaves` fail (before any expensive setup); the binary
/// must exit non-zero (the `run_binary` error arm) rather than panicking or silently succeeding.
#[test]
fn invalid_program_input_exits_nonzero() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path();
    let leaves_path = dir.join("leaves.json");
    std::fs::write(&leaves_path, b"not valid json").expect("write bad leaves.json");

    let status = Command::new(env!("CARGO_BIN_EXE_stwo_run_and_prove_recursive_tree"))
        .arg("--program_input")
        .arg(&leaves_path)
        .arg("--proof_path")
        .arg(dir.join("p"))
        .arg("--program_output")
        .arg(dir.join("po"))
        .arg("--packed_output_path")
        .arg(dir.join("pout"))
        .status()
        .expect("spawn recursive-tree binary");
    assert!(
        !status.success(),
        "binary should exit non-zero on malformed input, got: {status:?}",
    );
}
