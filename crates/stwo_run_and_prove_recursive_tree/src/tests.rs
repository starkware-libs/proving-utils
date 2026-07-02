use circuit_common::finalize::{ComponentSizes, compute_padded_sizes};

use crate::canonical::{
    CanonicalCircuit, TARGET_PADDING_SIZES, build_unpadded_leaf_context,
    build_unpadded_multiverifier_context,
};
use crate::fold::PackedNode;
use crate::{LeafInput, RecursiveTreeError, fold_plan, load_leaves};

// ------------------------------------------------------------------------------------------------
// Tree-shape / odd-carry logic (cheap, no proving).
// ------------------------------------------------------------------------------------------------

fn ceil_log2(n: usize) -> usize {
    if n <= 1 {
        0
    } else {
        (n - 1).ilog2() as usize + 1
    }
}

#[test]
fn fold_plan_depth_and_reductions() {
    // A balanced two-to-one tree with odd-carry: depth = ceil(log2 n), reductions = n - 1.
    for n in 1..=64usize {
        let (layers, reductions) = fold_plan(n);
        assert_eq!(layers, ceil_log2(n), "wrong layer count for n={n}");
        assert_eq!(reductions, n - 1, "wrong reduction count for n={n}");
    }
}

#[test]
fn fold_plan_small_cases() {
    assert_eq!(fold_plan(1), (0, 0));
    assert_eq!(fold_plan(2), (1, 1));
    assert_eq!(fold_plan(3), (2, 2));
    assert_eq!(fold_plan(4), (2, 3));
    assert_eq!(fold_plan(5), (3, 4));
    assert_eq!(fold_plan(8), (3, 7));
}

// ------------------------------------------------------------------------------------------------
// Serde shapes.
// ------------------------------------------------------------------------------------------------

#[test]
fn leaf_input_roundtrips() {
    let json = r#"{"train_id": 7, "output_values": [[1,2,3,4],[5,6,7,8]], "preprocessed_root": [11,22,33,44,55,66,77,88], "proof_path": "/tmp/leaf_7.proof"}"#;
    let leaf: LeafInput = serde_json::from_str(json).unwrap();
    assert_eq!(leaf.train_id, 7);
    assert_eq!(leaf.output_values, vec![[1, 2, 3, 4], [5, 6, 7, 8]]);
    assert_eq!(leaf.preprocessed_root, [11, 22, 33, 44, 55, 66, 77, 88]);
    assert_eq!(leaf.proof_path.to_str().unwrap(), "/tmp/leaf_7.proof");
    let back = serde_json::to_string(&leaf).unwrap();
    let leaf2: LeafInput = serde_json::from_str(&back).unwrap();
    assert_eq!(leaf2.train_id, leaf.train_id);
    assert_eq!(leaf2.output_values, leaf.output_values);
    assert_eq!(leaf2.preprocessed_root, leaf.preprocessed_root);
}

#[test]
fn load_leaves_reads_file() {
    let tmp = tempfile::tempdir().unwrap();
    let path = tmp.path().join("leaves.json");
    std::fs::write(
        &path,
        r#"{"leaves":[{"train_id":3,"output_values":[[1,2,3,4]],"preprocessed_root":[9,9,9,9,9,9,9,9],"proof_path":"/tmp/leaf.proof"}]}"#,
    )
    .unwrap();
    let leaves = load_leaves(&path).unwrap();
    assert_eq!(leaves.len(), 1);
    assert_eq!(leaves[0].train_id, 3);
    assert_eq!(leaves[0].preprocessed_root, [9; 8]);
}

#[test]
fn parse_output_values_checks_arity() {
    let leaf = |output_values| LeafInput {
        train_id: 42,
        output_values,
        preprocessed_root: [0; 8],
        proof_path: "/tmp/leaf.proof".into(),
    };
    // Correct arity round-trips to `N_RESERVED` QM31s.
    assert!(
        leaf(vec![[0, 0, 0, 0]; circuit_common::N_RESERVED])
            .parse_output_values()
            .is_ok()
    );
    // Wrong arity is rejected, and the error carries the offending leaf's train id.
    match leaf(vec![[0, 0, 0, 0]; circuit_common::N_RESERVED + 1]).parse_output_values() {
        Err(RecursiveTreeError::BadLeafOutputs { train_id, .. }) => assert_eq!(train_id, 42),
        other => panic!("expected BadLeafOutputs, got {other:?}"),
    }
}

#[test]
fn packed_node_serializes_leaf_and_internal() {
    let leaf_a = PackedNode {
        output_values: std::array::from_fn(|i| [i as u32 + 1, 0, 0, 0]),
        subtasks: vec![],
    };
    let leaf_b = PackedNode {
        output_values: std::array::from_fn(|i| [i as u32 + 9, 0, 0, 0]),
        subtasks: vec![],
    };
    // `output_values_qm31` must be the exact inverse of the stored limb encoding.
    assert_eq!(
        leaf_a
            .output_values_qm31()
            .map(|q| crate::fold::qm31_to_u32_limbs(&q)),
        leaf_a.output_values
    );
    // Leaf: `subtasks` is omitted entirely.
    let leaf_json: serde_json::Value =
        serde_json::from_str(&serde_json::to_string(&leaf_a).unwrap()).unwrap();
    assert!(leaf_json.get("subtasks").is_none());
    assert_eq!(leaf_json["output_values"][0][0], 1);

    // Internal: two subtasks present.
    let internal = PackedNode {
        output_values: std::array::from_fn(|i| [(i as u32 + 1) * 100, 0, 0, 0]),
        subtasks: vec![leaf_a, leaf_b],
    };
    let internal_json: serde_json::Value =
        serde_json::from_str(&serde_json::to_string(&internal).unwrap()).unwrap();
    assert_eq!(internal_json["subtasks"].as_array().unwrap().len(), 2);
    assert_eq!(internal_json["subtasks"][1]["output_values"][0][0], 9);

    // Round-trip: deserializing must succeed even though leaf subtasks omit `subtasks` on the wire
    // (regression for the missing `#[serde(default)]` — the recursive-tree reads back its own
    // `root_packed.json`).
    let internal_roundtrip: PackedNode =
        serde_json::from_str(&serde_json::to_string(&internal).unwrap()).unwrap();
    assert_eq!(internal_roundtrip.subtasks.len(), 2);
    assert!(internal_roundtrip.subtasks[0].subtasks.is_empty());
    assert!(internal_roundtrip.subtasks[1].subtasks.is_empty());
}

// ------------------------------------------------------------------------------------------------
// B-0: lock TARGET_PADDING_SIZES and the homogeneity (padding parity) invariant.
// ------------------------------------------------------------------------------------------------

/// The pinned [`TARGET_PADDING_SIZES`] must be exactly the per-component max (each already rounded
/// up to a power of two by `compute_padded_sizes`) of the unpadded leaf and multiverifier circuits.
/// If this fails, the assertion prints the value the constant should be updated to.
#[test]
fn target_padding_sizes_are_consistent() {
    let leaf = compute_padded_sizes(&build_unpadded_leaf_context());
    let multiverifier = compute_padded_sizes(&build_unpadded_multiverifier_context());
    let derived = ComponentSizes {
        eq: leaf.eq.max(multiverifier.eq),
        qm31_ops: leaf.qm31_ops.max(multiverifier.qm31_ops),
        m31_to_u32: leaf.m31_to_u32.max(multiverifier.m31_to_u32),
        triple_xor: leaf.triple_xor.max(multiverifier.triple_xor),
        blake_g_gate: leaf.blake_g_gate.max(multiverifier.blake_g_gate),
    };
    assert_eq!(
        derived, TARGET_PADDING_SIZES,
        "leaf sizes: {leaf}\nmultiverifier sizes: {multiverifier}\n\
         update crate::canonical::TARGET_PADDING_SIZES to the derived value above"
    );
}

/// Building the canonical circuit must succeed; in particular the leaf and multiverifier circuits,
/// padded to [`TARGET_PADDING_SIZES`], must share a preprocessed root (checked inside `build`).
#[test]
fn canonical_circuit_builds_with_matching_preprocessed_root() {
    CanonicalCircuit::build()
        .expect("canonical circuit should build with matching preprocessed root");
}

// ------------------------------------------------------------------------------------------------
// End-to-end fold over a pre-generated leaf proof (gated behind the `slow-tests` feature).
//
// This test focuses on the recursive-tree binary itself and does NOT run `leaf_prover`. It
// duplicates a single pre-generated privacy cairo-verifier proof (the fixture at
// `test_data/privacy_cairo_verifier_proof.bin`, taken from `circuit_multiverifier::verify_test`) as
// N leaves and folds them. The tree is configured to match that proof (see `canonical`), so every
// fold builds and proves a real multiverifier circuit over two valid child proofs. Still
// proving-heavy (one multiverifier proof per pair), hence `slow-tests`; run in RELEASE mode
// (`cargo test --release --features slow-tests`).
// ------------------------------------------------------------------------------------------------

#[cfg(feature = "slow-tests")]
mod e2e {
    use std::path::PathBuf;

    use blake2::{Blake2s256, Digest};
    use circuits::blake::HashValue;
    use circuits::ivalue::IValue;
    use stwo::core::fields::qm31::QM31;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
    use stwo::prover::CommitmentTreeProver;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::mempool::BaseColumnPool;
    use stwo::prover::poly::circle::PolyOps;

    use crate::canonical::{CIRCUIT_LOG_BLOWUP_FACTOR, CanonicalCircuit};
    use crate::fold::{PackedNode, qm31_to_u32_limbs};
    use crate::{LeafInput, RecursiveTreeConfig, stwo_run_and_prove_recursive_tree};

    /// Preprocessed root of the cairo-verifier circuit that produced the committed fixture proof
    /// `test_data/privacy_cairo_verifier_proof.bin`; declared in each leaf's `LeafInput`.
    const LEAF_PREPROCESSED_ROOT: [u32; circuit_common::N_RESERVED] = [
        1000331179, 2681434797, 3806553994, 1868679953, 3615184069, 3937104268, 679470514,
        520074062,
    ];

    /// The output values attested by the pre-generated privacy cairo-verifier proof (see
    /// `circuit_multiverifier::verify_test::PRIVACY_CAIRO_VERIFIER_OUTPUT_VALUES`). Inline in each
    /// duplicated leaf's `LeafInput` so the multiverifier's output check is satisfied.
    const LEAF_OUTPUT_VALUES: [u32; circuit_common::N_RESERVED] = [
        2299450592, 1514947052, 87572453, 633358207, 462231094, 464091325, 2016711704, 1173534648,
    ];

    fn leaf_proof_fixture() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_data/privacy_cairo_verifier_proof.bin")
    }

    fn init_tracing() {
        let _ = tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .try_init();
    }

    /// Out-of-circuit `circuits::blake::blake2s_u32s`: Blake2s-256 over the little-endian bytes of
    /// `words`, digest read back as eight little-endian u32 words (mirrors verify_test's helper).
    fn blake2s_u32s_host(words: &[u32]) -> [u32; circuit_common::N_RESERVED] {
        let mut hasher = Blake2s256::new();
        for word in words {
            hasher.update(word.to_le_bytes());
        }
        let hash: [u8; 32] = hasher.finalize().into();
        std::array::from_fn(|i| u32::from_le_bytes(hash[i * 4..i * 4 + 4].try_into().unwrap()))
    }

    /// Raw u32 output words in the on-disk `PackedNode` limb encoding: each word as
    /// `[low16, high16, 0, 0]` (= `qm31_to_u32_limbs(QM31::pack_u32(word))`).
    fn packed_limbs(
        words: [u32; circuit_common::N_RESERVED],
    ) -> [[u32; 4]; circuit_common::N_RESERVED] {
        words.map(|w| [w & 0xFFFF, w >> 16, 0, 0])
    }

    /// Merkle root of the canonical multiverifier's preprocessed trace — the `preprocessed_root`
    /// every internal node carries. Returns the eight digest words (as `hash_value_to_u32s` does).
    fn multiverifier_preprocessed_root(
        canonical: &CanonicalCircuit,
    ) -> [u32; circuit_common::N_RESERVED] {
        let circuit = &canonical.preprocessed_multiverifier;
        let lifting_log_size = circuit.trace_log_size + CIRCUIT_LOG_BLOWUP_FACTOR;
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(lifting_log_size)
                .circle_domain()
                .half_coset,
        );
        let trace = circuit.preprocessed_trace.get_trace::<SimdBackend>();
        let polys = SimdBackend::interpolate_columns(trace, &twiddles);
        let tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
            polys,
            CIRCUIT_LOG_BLOWUP_FACTOR,
            &twiddles,
            true,
            Some(lifting_log_size),
            &BaseColumnPool::<SimdBackend>::new(),
        );
        let root: HashValue<QM31> = tree.commitment.root().into();
        std::array::from_fn(|i| root[i].get().unpack_u32())
    }

    /// An expected tree node: the raw u32 output words + preprocessed root (both needed to hash a
    /// parent) alongside the `PackedNode` subtree the binary should emit for it.
    struct ExpectedNode {
        output_words: [u32; circuit_common::N_RESERVED],
        preprocessed_root: [u32; circuit_common::N_RESERVED],
        packed: PackedNode,
    }

    fn expected_leaf() -> ExpectedNode {
        ExpectedNode {
            output_words: LEAF_OUTPUT_VALUES,
            preprocessed_root: LEAF_PREPROCESSED_ROOT,
            packed: PackedNode {
                output_values: packed_limbs(LEAF_OUTPUT_VALUES),
                subtasks: vec![],
            },
        }
    }

    /// Mirrors `reduce_pair`'s output: the multiverifier hashes, for each child, its preprocessed
    /// root (8 words) followed by each output word split into `[low, high, 0, 0]`, and keeps the
    /// resulting eight-word digest as its own output.
    fn expected_reduce(
        left: ExpectedNode,
        right: ExpectedNode,
        multiverifier_root: [u32; circuit_common::N_RESERVED],
    ) -> ExpectedNode {
        let mut preimage = Vec::new();
        for child in [&left, &right] {
            preimage.extend_from_slice(&child.preprocessed_root);
            for &w in &child.output_words {
                preimage.extend_from_slice(&[w & 0xFFFF, w >> 16, 0, 0]);
            }
        }
        let output_words = blake2s_u32s_host(&preimage);
        ExpectedNode {
            output_words,
            preprocessed_root: multiverifier_root,
            packed: PackedNode {
                output_values: packed_limbs(output_words),
                subtasks: vec![left.packed, right.packed],
            },
        }
    }

    /// Folds `n` identical leaves exactly as the binary does (pair adjacent, carry the odd one up)
    /// and returns the expected root node. `multiverifier_root` is the preprocessed root every
    /// internal node carries (see [`multiverifier_preprocessed_root`]).
    fn expected_root(
        n: usize,
        multiverifier_root: [u32; circuit_common::N_RESERVED],
    ) -> ExpectedNode {
        let mut layer: Vec<ExpectedNode> = (0..n).map(|_| expected_leaf()).collect();
        while layer.len() > 1 {
            let mut next = Vec::with_capacity(layer.len().div_ceil(2));
            let mut pairs = layer.into_iter();
            while let Some(left) = pairs.next() {
                match pairs.next() {
                    Some(right) => next.push(expected_reduce(left, right, multiverifier_root)),
                    None => next.push(left),
                }
            }
            layer = next;
        }
        layer.pop().expect("at least one leaf")
    }

    /// Stages `n` leaves in `dir` — each a pure copy of the pre-generated leaf proof, described by
    /// a `LeafInput` carrying the leaf's output values inline — folds them with the binary, and
    /// asserts the produced root proof, root outputs, and full `packed_output` tree match what we
    /// recompute independently (topology + values) from the identical leaves.
    fn dupe_and_fold(n: usize, dir: &std::path::Path) {
        init_tracing();
        let proof_bytes = std::fs::read(leaf_proof_fixture()).unwrap();
        // The leaf's N_RESERVED output values as `[u32; 4]` QM31 limbs, inline in each `LeafInput`.
        // Each value is a u32 word packed into a QM31 (matching `verify_test::build_cairo_input`).
        let output_values: Vec<[u32; 4]> = LEAF_OUTPUT_VALUES
            .iter()
            .map(|&w| qm31_to_u32_limbs(&QM31::pack_u32(w)))
            .collect();

        let mut leaves = Vec::new();
        for i in 0..n {
            let proof_path = dir.join(format!("leaf_{i}.proof"));
            std::fs::write(&proof_path, &proof_bytes).unwrap();
            leaves.push(LeafInput {
                train_id: i as u64,
                output_values: output_values.clone(),
                preprocessed_root: LEAF_PREPROCESSED_ROOT,
                proof_path,
            });
        }
        let config = RecursiveTreeConfig {
            leaves,
            proof_path: dir.join("root.proof"),
            program_output: dir.join("root_outputs.json"),
            packed_output_path: dir.join("root_packed.json"),
        };
        stwo_run_and_prove_recursive_tree(config).unwrap();

        // Root proof must re-deserialize under the canonical proof config.
        let canonical = crate::canonical::CanonicalCircuit::build().unwrap();
        let bytes = std::fs::read(dir.join("root.proof")).unwrap();
        circuit_serialize::deserialize::deserialize_proof_with_config(
            &mut bytes.as_slice(),
            &canonical.shared_config.proof_config,
        )
        .expect("root proof deserializes under canonical config");

        // Independently recompute the whole tree (topology + hashed output values) from the leaves.
        let expected = expected_root(n, multiverifier_preprocessed_root(&canonical));

        let actual_outputs: Vec<[u32; 4]> =
            serde_json::from_str(&std::fs::read_to_string(dir.join("root_outputs.json")).unwrap())
                .unwrap();
        assert_eq!(
            actual_outputs,
            expected.packed.output_values.to_vec(),
            "root output values mismatch"
        );

        let actual_packed: PackedNode =
            serde_json::from_str(&std::fs::read_to_string(dir.join("root_packed.json")).unwrap())
                .unwrap();
        assert_eq!(
            actual_packed, expected.packed,
            "packed output tree (topology + values) mismatch"
        );
    }

    #[test]
    fn fold_two_leaves() {
        let tmp = tempfile::tempdir().unwrap();
        dupe_and_fold(2, tmp.path());
    }

    #[test]
    fn fold_three_leaves_with_carry() {
        let tmp = tempfile::tempdir().unwrap();
        dupe_and_fold(3, tmp.path());
    }

    #[test]
    fn fold_four_leaves() {
        let tmp = tempfile::tempdir().unwrap();
        dupe_and_fold(4, tmp.path());
    }
}
