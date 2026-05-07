use std::path::PathBuf;

use cairo_air::utils::ProofFormat;
use cairo_program_runner_lib::hints::fact_topologies::FactTopology;
use cairo_program_runner_lib::hints::types::{CompositePackedOutput, PackedOutput};
use cairo_vm::Felt252;

use super::{
    LeafInput, RecursiveJobData, RecursiveTreeConfig, RecursiveTreeError,
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
    match stwo_run_and_prove_recursive_tree(config) {
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
        n_non_recursive_jobs: 1,
        total_non_recursive_output_size: 3,
        total_n_pages: 1,
        total_fact_tree_structures_len: 2,
    };
    let leaf_b = LeafInput {
        train_id: 2,
        proof_path: PathBuf::new(),
        program_hash_function: "blake".to_string(),
        packed_output: PackedOutput::Plain,
        n_non_recursive_jobs: 1,
        total_non_recursive_output_size: 12,
        total_n_pages: 2,
        total_fact_tree_structures_len: 4,
    };
    let agg_a = RecursiveJobData::from_leaf(&leaf_a, vec![Felt252::from(1u64)]);
    let agg_b = RecursiveJobData::from_leaf(&leaf_b, vec![Felt252::from(2u64)]);
    let merged = RecursiveJobData::combine(&agg_a, &agg_b, vec![Felt252::from(3u64)]);

    assert_eq!(merged.n_non_recursive_jobs, 2);
    assert_eq!(merged.total_non_recursive_output_size, 3 + 5 + 7);
    assert_eq!(merged.total_n_pages, 1 + 2);
    assert_eq!(merged.total_fact_tree_structures_len, 2 + 4);
    assert_eq!(merged.outputs, vec![Felt252::from(3u64)]);
}
