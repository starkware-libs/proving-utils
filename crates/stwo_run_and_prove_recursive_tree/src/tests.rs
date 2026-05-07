use std::path::PathBuf;

use cairo_air::utils::ProofFormat;
use cairo_program_runner_lib::hints::fact_topologies::FactTopology;
use cairo_program_runner_lib::hints::types::{CompositePackedOutput, PackedOutput};
use cairo_vm::Felt252;

use stwo_run_and_prove_common::MockProverTrait;

use super::{
    LeafInput, RecursiveJobCounters, RecursiveJobData, RecursiveTreeConfig, RecursiveTreeError,
    stwo_run_and_prove_recursive_tree,
};

#[test]
fn empty_leaves_returns_dedicated_error() {
    let config = RecursiveTreeConfig {
        leaves: vec![],
        verifier_program: PathBuf::from("/nonexistent_verifier"),
        bootloader_program: PathBuf::from("/nonexistent_bootloader"),
        prover_params_json: None,
        proof_format: ProofFormat::CairoSerde,
        verify: false,
        proof_path: PathBuf::from("/tmp/proof_should_not_be_written"),
        program_output: PathBuf::from("/tmp/program_output_should_not_be_written"),
        fact_topologies_path: PathBuf::from("/tmp/topology_should_not_be_written"),
        packed_output_path: PathBuf::from("/tmp/packed_should_not_be_written"),
        save_debug_data: false,
        debug_data_dir: None,
    };
    match stwo_run_and_prove_recursive_tree(config, &MockProverTrait::new()) {
        Err(RecursiveTreeError::EmptyLeaves) => {}
        other => panic!("expected EmptyLeaves error, got {other:?}"),
    }
}

#[test]
fn packed_output_serializes_with_python_compatible_discriminator() {
    let plain = PackedOutput::Plain;
    let plain_json = serde_json::to_value(&plain).expect("serialize plain");
    assert_eq!(plain_json["type"], "PlainPackedOutput");

    let composite = PackedOutput::Composite(CompositePackedOutput {
        outputs: vec![Felt252::from(1u64), Felt252::from(42u64)],
        subtasks: vec![PackedOutput::Plain],
        fact_topologies: vec![FactTopology::trivial(2)],
    });
    let composite_json = serde_json::to_value(&composite).expect("serialize composite");
    assert_eq!(composite_json["type"], "CompositePackedOutput");
    // outputs are emitted as decimal strings to preserve precision.
    assert_eq!(composite_json["outputs"], serde_json::json!(["1", "42"]));
    assert_eq!(composite_json["subtasks"][0]["type"], "PlainPackedOutput");
}

#[test]
fn aggregated_combine_sums_per_leaf_counters() {
    let leaf_a = LeafInput {
        train_id: 1,
        proof_path: PathBuf::new(),
        program_hash_function: "blake".to_string(),
        packed_output: PackedOutput::Plain,
        counters: RecursiveJobCounters {
            n_non_recursive_jobs: 1,
            total_non_recursive_output_size: 3,
            total_n_pages: 1,
            total_fact_tree_structures_len: 2,
        },
    };
    let leaf_b = LeafInput {
        train_id: 2,
        proof_path: PathBuf::new(),
        program_hash_function: "blake".to_string(),
        packed_output: PackedOutput::Plain,
        counters: RecursiveJobCounters {
            n_non_recursive_jobs: 1,
            total_non_recursive_output_size: 12,
            total_n_pages: 2,
            total_fact_tree_structures_len: 4,
        },
    };
    let agg_a = RecursiveJobData::from_leaf(&leaf_a, vec![Felt252::from(1u64)]);
    let agg_b = RecursiveJobData::from_leaf(&leaf_b, vec![Felt252::from(2u64)]);
    let merged = RecursiveJobData::combine(&agg_a, &agg_b, vec![Felt252::from(3u64)]);

    assert_eq!(merged.counters.n_non_recursive_jobs, 2);
    assert_eq!(merged.counters.total_non_recursive_output_size, 3 + 5 + 7);
    assert_eq!(merged.counters.total_n_pages, 1 + 2);
    assert_eq!(merged.counters.total_fact_tree_structures_len, 2 + 4);
    assert_eq!(merged.outputs, vec![Felt252::from(3u64)]);
}

#[test]
fn verifier_task_for_child_builds_expected_cairo1executable_json() {
    let verifier_program = PathBuf::from("/programs/stwo_full_cairo_verifier_blake_packing.json");
    let proof_path = PathBuf::from("/scratch/leaf_proof.json");
    let value = super::verifier_task_for_child(&verifier_program, &proof_path, 3, 7, "left");
    assert_eq!(value["type"], "Cairo1Executable");
    assert_eq!(value["path"], serde_json::json!(verifier_program));
    assert_eq!(value["user_args_file"], serde_json::json!(proof_path));
    // The hash function is currently hardcoded inside `verifier_task_for_child`; lock that in.
    assert_eq!(value["program_hash_function"], "blake");
}

#[test]
fn read_outputs_file_parses_hex_strings() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("outputs.json");
    let contents = serde_json::json!(["0x1", "0xCAFE", "0x0"]);
    std::fs::write(&path, contents.to_string()).expect("write outputs.json");
    let parsed = super::read_outputs_file(&path).expect("read_outputs_file ok");
    assert_eq!(
        parsed,
        vec![
            Felt252::from(1u64),
            Felt252::from(0xCAFEu64),
            Felt252::from(0u64),
        ]
    );
}

#[test]
fn read_outputs_file_rejects_invalid_hex() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("outputs.json");
    let contents = serde_json::json!(["not_a_hex_string_zz"]);
    std::fs::write(&path, contents.to_string()).expect("write outputs.json");
    let err = super::read_outputs_file(&path).expect_err("should fail on invalid hex");
    let msg = err.to_string();
    assert!(
        msg.contains("Failed to parse program-output entry"),
        "error should mention parse failure, got: {msg}",
    );
}

#[test]
fn read_fact_topologies_file_parses_wrapper_schema() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("fact_topologies.json");
    let contents = serde_json::json!({
        "fact_topologies": [
            {"tree_structure": [1, 0], "page_sizes": [5]},
            {"tree_structure": [2, 0, 1, 0], "page_sizes": [3, 7]},
        ]
    });
    std::fs::write(&path, contents.to_string()).expect("write fact_topologies.json");
    let parsed = super::read_fact_topologies_file(&path).expect("read_fact_topologies_file ok");
    assert_eq!(parsed.len(), 2);
    assert_eq!(parsed[0].page_sizes, vec![5]);
    assert_eq!(parsed[0].tree_structure, vec![1, 0]);
    assert_eq!(parsed[1].page_sizes, vec![3, 7]);
    assert_eq!(parsed[1].tree_structure, vec![2, 0, 1, 0]);
}

#[test]
fn single_leaf_input_writes_root_outputs_without_reduction() {
    // With exactly one leaf, no reduce_pair runs and the leaf entry becomes the root. Exercises
    // the leaf-init path, the `current_layer.len() > 1` short-circuit, and `write_root_outputs`.
    let tmp = tempfile::tempdir().expect("tempdir");
    let leaf_proof_path = tmp.path().join("leaf_proof.json");
    let leaf_proof_bytes: &[u8] = b"<leaf proof bytes (opaque to this test)>";
    std::fs::write(&leaf_proof_path, leaf_proof_bytes).expect("write leaf proof");

    let leaf_fact_topology = FactTopology::trivial(5);
    let leaf_outputs = vec![Felt252::from(0xCAFEu64), Felt252::from(0xBEEFu64)];
    let leaf_packed_output = PackedOutput::Composite(CompositePackedOutput {
        outputs: leaf_outputs.clone(),
        subtasks: vec![PackedOutput::Plain],
        fact_topologies: vec![leaf_fact_topology.clone()],
    });
    let leaf = LeafInput {
        train_id: 42,
        proof_path: leaf_proof_path,
        program_hash_function: "blake".to_string(),
        packed_output: leaf_packed_output,
        counters: RecursiveJobCounters {
            n_non_recursive_jobs: 1,
            total_non_recursive_output_size: 5,
            total_n_pages: 1,
            total_fact_tree_structures_len: 2,
        },
    };

    let out_proof = tmp.path().join("out_proof");
    let out_program_output = tmp.path().join("out_program_output.json");
    let out_fact_topologies = tmp.path().join("out_fact_topologies.json");
    let out_packed_output = tmp.path().join("out_packed_output.json");
    let config = RecursiveTreeConfig {
        leaves: vec![leaf],
        verifier_program: PathBuf::from("/unused_verifier"),
        bootloader_program: PathBuf::from("/unused_bootloader"),
        prover_params_json: None,
        proof_format: ProofFormat::CairoSerde,
        verify: false,
        proof_path: out_proof.clone(),
        program_output: out_program_output.clone(),
        fact_topologies_path: out_fact_topologies.clone(),
        packed_output_path: out_packed_output.clone(),
        save_debug_data: false,
        debug_data_dir: None,
    };

    let aggregated = stwo_run_and_prove_recursive_tree(config, &MockProverTrait::new())
        .expect("single-leaf passthrough ok");
    assert_eq!(aggregated.counters.n_non_recursive_jobs, 1);
    assert_eq!(aggregated.counters.total_non_recursive_output_size, 5);
    assert_eq!(aggregated.counters.total_n_pages, 1);
    assert_eq!(aggregated.counters.total_fact_tree_structures_len, 2);
    assert_eq!(aggregated.outputs, leaf_outputs);

    // Proof file: byte-for-byte copy of the leaf's proof.
    assert_eq!(
        std::fs::read(&out_proof).expect("read out_proof"),
        leaf_proof_bytes
    );

    // program_output: JSON array of hex strings — one per Felt252 in `aggregated.outputs`.
    let outputs_hex: Vec<String> =
        serde_json::from_str(&std::fs::read_to_string(&out_program_output).expect("read po"))
            .expect("parse program_output");
    assert_eq!(outputs_hex.len(), 2);

    // fact_topologies.json: wrapper `{"fact_topologies": [...]}` with one trivial-5 entry (the
    // leaf's own fact_topology, since the leaf is the root in the single-leaf case).
    let ft_json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out_fact_topologies).expect("read ft"))
            .expect("parse fact_topologies");
    let ft_arr = ft_json["fact_topologies"]
        .as_array()
        .expect("fact_topologies is array");
    assert_eq!(ft_arr.len(), 1);
    assert_eq!(ft_arr[0]["page_sizes"], serde_json::json!([5]));

    // packed_output.json: the leaf's Composite serialized via the Python-compatible discriminator.
    let po_json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out_packed_output).expect("read pout"))
            .expect("parse packed_output");
    assert_eq!(po_json["type"], "CompositePackedOutput");
    assert_eq!(po_json["subtasks"][0]["type"], "PlainPackedOutput");
}

#[test]
fn single_leaf_with_plain_packed_output_returns_error() {
    // Python always sends a Composite via packed_output_from_data(create_recursive_data(...));
    // a Plain at the leaf-init site indicates a contract violation and must surface a descriptive
    // error that names the offending train_id.
    let tmp = tempfile::tempdir().expect("tempdir");
    let leaf_proof_path = tmp.path().join("leaf_proof.json");
    std::fs::write(&leaf_proof_path, b"dummy").expect("write leaf proof");

    let leaf = LeafInput {
        train_id: 999,
        proof_path: leaf_proof_path,
        program_hash_function: "blake".to_string(),
        packed_output: PackedOutput::Plain,
        counters: RecursiveJobCounters {
            n_non_recursive_jobs: 1,
            total_non_recursive_output_size: 0,
            total_n_pages: 0,
            total_fact_tree_structures_len: 0,
        },
    };
    let config = RecursiveTreeConfig {
        leaves: vec![leaf],
        verifier_program: PathBuf::from("/unused"),
        bootloader_program: PathBuf::from("/unused"),
        prover_params_json: None,
        proof_format: ProofFormat::CairoSerde,
        verify: false,
        proof_path: tmp.path().join("p"),
        program_output: tmp.path().join("po"),
        fact_topologies_path: tmp.path().join("ft"),
        packed_output_path: tmp.path().join("pout"),
        save_debug_data: false,
        debug_data_dir: None,
    };
    let err = stwo_run_and_prove_recursive_tree(config, &MockProverTrait::new())
        .expect_err("should reject Plain leaf");
    let msg = err.to_string();
    assert!(
        msg.contains("train_id=999"),
        "error should name the offending train_id, got: {msg}",
    );
    assert!(
        msg.contains("Plain"),
        "error should mention Plain packed_output, got: {msg}",
    );
}

/// End-to-end exercise of `reduce_pair` plus the surrounding reduction loop using real Cairo VM
/// execution: the bootloader actually runs two verifier tasks against the mock STWO leaf proof,
/// and the only mocked step is the (slow) STWO prove that would otherwise produce the new
/// pair-level proof. The mock writes a placeholder file so `write_root_outputs` can finish.
///
/// 2 leaves → exactly 1 `reduce_pair` call → 1 mocked prove. We don't extend to 3 leaves (where
/// a second `reduce_pair` would need to verify the mocked layer-1 proof — which isn't a real
/// STWO proof and would fail the verifier task).
#[test]
fn two_leaves_runs_reduce_pair_end_to_end_with_mocked_prover() {
    let crate_resources = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("resources");
    let verifier_program = crate_resources.join("stwo_cairo_verifier_with_blake_packing.json");
    let bootloader_program =
        crate_resources.join("no_builtin_simulation_simple_bootloader_compiled.json");
    let leaf_proof_src = crate_resources.join("mock_proof.json");

    let tmp = tempfile::tempdir().expect("tempdir");
    // Distinct on-disk leaf-proof paths so the two verifier tasks in the bootloader run see
    // independent inputs (same byte contents — the recursive_tree binary doesn't care).
    let leaf_proof_1 = tmp.path().join("leaf_proof_1");
    let leaf_proof_2 = tmp.path().join("leaf_proof_2");
    std::fs::copy(&leaf_proof_src, &leaf_proof_1).expect("copy leaf proof 1");
    std::fs::copy(&leaf_proof_src, &leaf_proof_2).expect("copy leaf proof 2");

    let leaf_fact_topology = FactTopology::trivial(1);
    let leaf_outputs = vec![Felt252::from(0x32u64)];
    let leaf_packed_output = PackedOutput::Composite(CompositePackedOutput {
        outputs: leaf_outputs.clone(),
        subtasks: vec![PackedOutput::Plain],
        fact_topologies: vec![leaf_fact_topology.clone()],
    });
    let make_leaf = |train_id: u64, proof_path: PathBuf| LeafInput {
        train_id,
        proof_path,
        program_hash_function: "blake".to_string(),
        packed_output: leaf_packed_output.clone(),
        counters: RecursiveJobCounters {
            n_non_recursive_jobs: 1,
            total_non_recursive_output_size: 1,
            total_n_pages: 1,
            total_fact_tree_structures_len: 2,
        },
    };

    let out_proof = tmp.path().join("root_proof");
    let out_program_output = tmp.path().join("root_outputs.json");
    let out_fact_topologies = tmp.path().join("root_fact_topologies.json");
    let out_packed_output = tmp.path().join("root_packed_output.json");
    let config = RecursiveTreeConfig {
        leaves: vec![make_leaf(1, leaf_proof_1), make_leaf(2, leaf_proof_2)],
        verifier_program,
        bootloader_program,
        prover_params_json: None,
        proof_format: ProofFormat::CairoSerde,
        verify: false,
        proof_path: out_proof.clone(),
        program_output: out_program_output.clone(),
        fact_topologies_path: out_fact_topologies.clone(),
        packed_output_path: out_packed_output.clone(),
        save_debug_data: false,
        debug_data_dir: None,
    };

    let mut mock_prover = MockProverTrait::new();
    mock_prover
        .expect_create_and_serialize_proof()
        .times(1)
        .returning(|_, _, proof_path, _, _| {
            std::fs::write(&proof_path, b"<mock pair-level proof>")?;
            Ok(())
        });

    let aggregated = stwo_run_and_prove_recursive_tree(config, &mock_prover)
        .expect("end-to-end two-leaves reduction failed");

    // Aggregate counters sum across the 2 leaves (n_non_recursive_jobs etc.).
    assert_eq!(aggregated.counters.n_non_recursive_jobs, 2);
    assert_eq!(aggregated.counters.total_non_recursive_output_size, 2);
    assert_eq!(aggregated.counters.total_n_pages, 2);
    assert_eq!(aggregated.counters.total_fact_tree_structures_len, 4);

    // Root files were written.
    assert!(
        std::fs::metadata(&out_proof)
            .expect("stat root_proof")
            .is_file()
    );
    let outputs_hex: Vec<String> =
        serde_json::from_str(&std::fs::read_to_string(&out_program_output).expect("read po"))
            .expect("parse program_output");
    // Bootloader output starts with n_tasks = 2 (one word per the simple bootloader contract).
    assert!(
        !outputs_hex.is_empty(),
        "root program_output should be non-empty"
    );

    let ft_json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out_fact_topologies).expect("read ft"))
            .expect("parse fact_topologies");
    // Bootloader wrote one fact_topology per verifier task (= 2 per the 2-task reduce_pair).
    assert_eq!(
        ft_json["fact_topologies"]
            .as_array()
            .expect("fact_topologies is array")
            .len(),
        2,
    );

    let po_json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out_packed_output).expect("read pout"))
            .expect("parse packed_output");
    assert_eq!(po_json["type"], "CompositePackedOutput");
    // The composite carries the two leaf packed_outputs as subtasks.
    assert_eq!(
        po_json["subtasks"]
            .as_array()
            .expect("subtasks is array")
            .len(),
        2,
    );
}
