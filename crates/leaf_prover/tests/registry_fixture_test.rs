//! Guards the `cli_test` registry fixture: it must list the leaf the slow end-to-end test proves,
//! resolve to the expected pad target, and carry the same preprocessed root as the committed
//! expected output. Fast (no proving), so it runs on every test job unlike `cli_test`.

use std::fs;
use std::path::PathBuf;

use circuit_registry::CircuitRegistry;
use leaf_proof_format::SerializedLeafProof;

#[test]
fn registry_fixture_matches_expected_leaf() {
    let data_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data");

    let registry: CircuitRegistry =
        serde_json::from_str(&fs::read_to_string(data_dir.join("registry.json")).unwrap())
            .expect("Cannot parse registry fixture");

    // The fixture lists exactly the one leaf the e2e test proves, found by its identity.
    assert_eq!(registry.leaf_verifiers.len(), 1);
    let leaf = &registry.leaf_verifiers[0];
    assert!(registry.leaf_verifier(leaf.trace_log_size, leaf.log_blowup_factor).is_some());

    // Its config resolves to the pad target the leaf prover expects.
    let pad = registry.config_pad_target(&leaf.config).expect("leaf verifier config missing");
    assert_eq!(pad.eq, 1 << 20);
    assert_eq!(pad.qm31_ops, 1 << 23);
    assert_eq!(pad.m31_to_u32, 1 << 20);
    assert_eq!(pad.triple_xor, 1 << 19);
    assert_eq!(pad.blake_g_gate, 1 << 23);

    // Its preprocessed root equals the root in the committed expected e2e output, so a matching
    // leaf passes the prover's root check.
    let expected: SerializedLeafProof =
        serde_json::from_str(&fs::read_to_string(data_dir.join("expected_output.json")).unwrap())
            .expect("Cannot parse expected output");
    assert_eq!(leaf.preprocessed_root.to_le_bytes(), expected.circuit_preprocessed_root);
}
