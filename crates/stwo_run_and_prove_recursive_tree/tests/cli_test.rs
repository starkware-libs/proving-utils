//! Binary-level integration tests for the `stwo_run_and_prove_recursive_tree` CLI.
//!
//! The cheap error arm (malformed leaves file → non-zero exit) runs always. The single-leaf
//! passthrough success arm builds the canonical circuit shape, so it is gated behind `slow-tests`.

use std::process::Command;

/// A malformed `--program_input` makes `load_leaves` fail (before any expensive setup); the binary
/// must exit non-zero (the `run_binary` error arm) rather than panicking or silently succeeding.
#[test]
fn test_invalid_program_input_exits_nonzero() {
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

/// A single-leaf tree does no folding — the lone leaf is the root — so the binary copies the leaf
/// proof straight through to `--proof_path`. This exercises the whole CLI success path (arg parse →
/// `load_leaves` → `CanonicalCircuit::build` → passthrough → root outputs) without any
/// multiverifier proving. A 1-leaf tree never verifies the proof, so a dummy inline proof and
/// placeholder outputs/root suffice (only the output arity `N_RESERVED` = 8 is checked). Gated
/// behind `slow-tests` because it still builds the canonical circuit shape.
#[cfg(feature = "slow-tests")]
#[test]
fn test_single_leaf_passthrough_succeeds() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path();

    // A leaf input file: a `leaf_prover`-shaped output with the injected `output_preimage`
    // flattened in.
    let outputs =
        "[[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]";
    let root = format!("{:?}", [0u8; 32]);
    let leaf_json = format!(
        r#"{{"program_output":[],"output_preimage":[],"circuit_output":{outputs},"circuit_preprocessed_root":{root},"proof":"AQIDBA=="}}"#,
    );
    let leaf_path = dir.join("leaf0.json");
    std::fs::write(&leaf_path, leaf_json).expect("write leaf0.json");

    // The manifest lists one path to the leaf-output file above.
    let manifest_path = dir.join("leaves.json");
    std::fs::write(
        &manifest_path,
        format!(r#"{{"leaves":[{:?}]}}"#, leaf_path.to_str().unwrap()),
    )
    .expect("write leaves.json");

    let root_proof = dir.join("root.proof");
    let status = Command::new(env!("CARGO_BIN_EXE_stwo_run_and_prove_recursive_tree"))
        .arg("--program_input")
        .arg(&manifest_path)
        .arg("--proof_path")
        .arg(&root_proof)
        .arg("--program_output")
        .arg(dir.join("root_outputs.json"))
        .arg("--packed_output_path")
        .arg(dir.join("root_packed.json"))
        .status()
        .expect("spawn recursive-tree binary");

    assert!(
        status.success(),
        "1-leaf passthrough should succeed, got: {status:?}"
    );
    // The root proof of a single-leaf tree is the leaf proof, copied through unchanged.
    assert_eq!(
        std::fs::read(&root_proof).expect("read root proof"),
        vec![1, 2, 3, 4],
        "root proof must be byte-identical to the single leaf's proof",
    );
    assert!(
        dir.join("root_outputs.json").exists(),
        "root outputs file written"
    );
    assert!(
        dir.join("root_packed.json").exists(),
        "packed tree file written"
    );
}
