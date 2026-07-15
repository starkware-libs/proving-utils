//! Binary-level integration test for the `stwo_run_and_prove_recursive_tree` CLI.
//!
//! Drives the actual compiled binary (via `CARGO_BIN_EXE_*`) end-to-end on a single-leaf input.
//! A single leaf never triggers `reduce_pair`, so the slow STWO prove step and the verifier
//! bootloader are never invoked — the leaf's proof file is just copied through to the root. This
//! lets us cover `main.rs` (`Args` parsing, `run`, `load_leaves` wiring, root-output writing) at
//! the binary boundary without the cost of a real prove, and under coverage runs cargo-llvm-cov
//! captures the spawned binary's profile too.

use std::process::Command;

/// One leaf, no reduction: the binary copies the leaf proof out as the root proof and writes the
/// other three root-output files from the leaf's own `packed_output`.
#[test]
fn single_leaf_cli_run_writes_root_outputs() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path();

    // Opaque leaf-proof bytes; with a single leaf they're copied verbatim to the root proof.
    let leaf_proof_path = dir.join("leaf_proof.json");
    let leaf_proof_bytes: &[u8] = b"<leaf proof bytes (opaque to the binary)>";
    std::fs::write(&leaf_proof_path, leaf_proof_bytes).expect("write leaf proof");

    // leaves.json in the exact wire shape Python's `_create_files_dict_for_recursive_tree`
    // produces: top-level flattened counters, a Composite `packed_output` (outputs as JSON
    // numbers, fact_topologies as {tree_structure, page_sizes}).
    let leaves_path = dir.join("leaves.json");
    let leaves_json = serde_json::json!({
        "leaves": [{
            "train_id": 42,
            "proof_path": leaf_proof_path,
            "program_hash_function": "blake",
            "packed_output": {
                "type": "CompositePackedOutput",
                "outputs": [205, 191],
                "subtasks": [{"type": "PlainPackedOutput"}],
                "fact_topologies": [{"tree_structure": [1, 0], "page_sizes": [5]}],
            },
            "n_non_recursive_jobs": 1,
            "total_non_recursive_output_size": 5,
            "total_n_pages": 1,
            "total_fact_tree_structures_len": 2,
        }]
    });
    std::fs::write(&leaves_path, leaves_json.to_string()).expect("write leaves.json");

    let out_proof = dir.join("root_proof");
    let out_program_output = dir.join("root_outputs.json");
    let out_fact_topologies = dir.join("root_fact_topologies.json");
    let out_packed_output = dir.join("root_packed_output.json");

    // verifier/bootloader programs are never read on the single-leaf path; pass dummy paths to
    // satisfy the required CLI args.
    let status = Command::new(env!("CARGO_BIN_EXE_stwo_run_and_prove_recursive_tree"))
        .arg("--program_input")
        .arg(&leaves_path)
        .arg("--verifier_program")
        .arg(dir.join("unused_verifier"))
        .arg("--bootloader_program")
        .arg(dir.join("unused_bootloader"))
        .arg("--proof_path")
        .arg(&out_proof)
        .arg("--program_output")
        .arg(&out_program_output)
        .arg("--fact_topologies_path")
        .arg(&out_fact_topologies)
        .arg("--packed_output_path")
        .arg(&out_packed_output)
        .status()
        .expect("spawn recursive-tree binary");
    assert!(status.success(), "binary exited with failure: {status:?}");

    // Root proof: byte-for-byte copy of the single leaf's proof.
    assert_eq!(std::fs::read(&out_proof).expect("read root_proof"), leaf_proof_bytes,);

    // program_output: JSON array of hex strings, one per leaf output (0xcd=205, 0xbf=191).
    let outputs_hex: Vec<String> =
        serde_json::from_str(&std::fs::read_to_string(&out_program_output).expect("read po"))
            .expect("parse program_output");
    assert_eq!(outputs_hex.len(), 2);

    // fact_topologies.json: the leaf's own single fact_topology (page_sizes [5]).
    let ft_json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out_fact_topologies).expect("read ft"))
            .expect("parse fact_topologies");
    let ft_arr = ft_json["fact_topologies"].as_array().expect("fact_topologies is array");
    assert_eq!(ft_arr.len(), 1);
    assert_eq!(ft_arr[0]["page_sizes"], serde_json::json!([5]));

    // packed_output.json: the leaf's Composite, serialized with the Python-compatible
    // discriminator.
    let po_json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out_packed_output).expect("read pout"))
            .expect("parse packed_output");
    assert_eq!(po_json["type"], "CompositePackedOutput");
    assert_eq!(po_json["subtasks"][0]["type"], "PlainPackedOutput");
}

/// A malformed `--program_input` makes `load_leaves` fail; the binary must exit non-zero (the
/// `run_binary` error arm) rather than panicking or silently succeeding.
#[test]
fn invalid_program_input_exits_nonzero() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path();
    let leaves_path = dir.join("leaves.json");
    std::fs::write(&leaves_path, b"not valid json").expect("write bad leaves.json");

    let status = Command::new(env!("CARGO_BIN_EXE_stwo_run_and_prove_recursive_tree"))
        .arg("--program_input")
        .arg(&leaves_path)
        .arg("--verifier_program")
        .arg(dir.join("unused_verifier"))
        .arg("--bootloader_program")
        .arg(dir.join("unused_bootloader"))
        .arg("--proof_path")
        .arg(dir.join("p"))
        .arg("--program_output")
        .arg(dir.join("po"))
        .arg("--fact_topologies_path")
        .arg(dir.join("ft"))
        .arg("--packed_output_path")
        .arg(dir.join("pout"))
        .status()
        .expect("spawn recursive-tree binary");
    assert!(!status.success(), "binary should exit non-zero on malformed input, got: {status:?}",);
}
