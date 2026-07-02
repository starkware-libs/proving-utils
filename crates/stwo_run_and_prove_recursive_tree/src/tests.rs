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
    // A representative leaf: `circuit_output` has exactly `N_RESERVED` entries, `proof` is base64
    // ("AQID" = bytes [1, 2, 3]), and `circuit_preprocessed_root` is 32 bytes.
    let circuit_output: Vec<[u32; 4]> = (0..circuit_common::N_RESERVED as u32)
        .map(|i| [i, i + 1, i + 2, i + 3])
        .collect();
    let root_bytes: Vec<u8> = (0..32).collect();
    let json = format!(
        r#"{{"program_output":["42","7"],"circuit_output":{},"circuit_preprocessed_root":{root_bytes:?},"proof":"AQID"}}"#,
        serde_json::to_string(&circuit_output).unwrap(),
    );
    let leaf: LeafInput = serde_json::from_str(&json).unwrap();
    assert_eq!(leaf.program_output, vec!["42", "7"]);
    assert_eq!(leaf.circuit_output, circuit_output);
    assert_eq!(leaf.circuit_preprocessed_root[0], 0);
    assert_eq!(leaf.circuit_preprocessed_root[31], 31);
    assert_eq!(leaf.proof, vec![1, 2, 3]);
    let back = serde_json::to_string(&leaf).unwrap();
    let leaf2: LeafInput = serde_json::from_str(&back).unwrap();
    assert_eq!(leaf2.circuit_output, leaf.circuit_output);
    assert_eq!(
        leaf2.circuit_preprocessed_root,
        leaf.circuit_preprocessed_root
    );
    assert_eq!(leaf2.proof, leaf.proof);
}

#[test]
fn load_leaves_reads_manifest_of_paths() {
    let tmp = tempfile::tempdir().unwrap();
    let leaf_path = tmp.path().join("leaf0.json");
    std::fs::write(
        &leaf_path,
        r#"{"program_output":["1"],"circuit_output":[[1,2,3,4]],"circuit_preprocessed_root":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"proof":"AQID"}"#,
    )
    .unwrap();
    let manifest = tmp.path().join("leaves.json");
    std::fs::write(
        &manifest,
        format!(r#"{{"leaves":[{:?}]}}"#, leaf_path.to_str().unwrap()),
    )
    .unwrap();
    let leaves = load_leaves(&manifest).unwrap();
    assert_eq!(leaves.len(), 1);
    assert_eq!(leaves[0].circuit_output, vec![[1, 2, 3, 4]]);
    assert_eq!(leaves[0].proof, vec![1, 2, 3]);
}

#[test]
fn parse_output_values_checks_arity() {
    let leaf = |circuit_output| LeafInput {
        program_output: vec![],
        circuit_output,
        circuit_preprocessed_root: [0; 32],
        proof: vec![],
    };
    // Correct arity round-trips to `N_RESERVED` QM31s.
    assert!(
        leaf(vec![[0, 0, 0, 0]; circuit_common::N_RESERVED])
            .parse_output_values()
            .is_ok()
    );
    // Wrong arity is rejected.
    match leaf(vec![[0, 0, 0, 0]; circuit_common::N_RESERVED + 1]).parse_output_values() {
        Err(RecursiveTreeError::BadLeafOutputs { reason }) => assert!(reason.contains("expected")),
        other => panic!("expected BadLeafOutputs, got {other:?}"),
    }
}

#[test]
fn packed_node_serializes_leaf_and_internal() {
    // A leaf: a `Composite` circuit node over a single `Plain` carrying the program output.
    let leaf_a = PackedNode::Composite {
        output_values: std::array::from_fn(|i| [i as u32 + 1, 0, 0, 0]),
        subtasks: vec![PackedNode::Plain {
            program_output: vec!["1".to_string(), "2".to_string()],
        }],
    };
    // `output_values_qm31` must be the exact inverse of the stored limb encoding.
    assert_eq!(
        leaf_a
            .output_values_qm31()
            .map(|q| crate::fold::qm31_to_u32_limbs(&q)),
        *leaf_a.output_values()
    );
    // Serializes as `{"Composite": { output_values, subtasks: [{"Plain": { program_output }}] }}`.
    let leaf_json: serde_json::Value =
        serde_json::from_str(&serde_json::to_string(&leaf_a).unwrap()).unwrap();
    assert_eq!(leaf_json["Composite"]["output_values"][0][0], 1);
    assert_eq!(
        leaf_json["Composite"]["subtasks"][0]["Plain"]["program_output"][0],
        "1"
    );

    // Internal: a `Composite` over two child subtasks.
    let leaf_b = PackedNode::Composite {
        output_values: std::array::from_fn(|i| [i as u32 + 9, 0, 0, 0]),
        subtasks: vec![PackedNode::Plain {
            program_output: vec![],
        }],
    };
    let internal = PackedNode::Composite {
        output_values: std::array::from_fn(|i| [(i as u32 + 1) * 100, 0, 0, 0]),
        subtasks: vec![leaf_a, leaf_b],
    };

    // Round-trips exactly (the recursive-tree reads back its own `root_packed.json`).
    let back: PackedNode =
        serde_json::from_str(&serde_json::to_string(&internal).unwrap()).unwrap();
    assert_eq!(back, internal);
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
            // The fixture leaves carry an empty program output (see `dupe_and_fold`), so each leaf
            // is a `Composite` over a `Plain` with no program output.
            packed: PackedNode::Composite {
                output_values: packed_limbs(LEAF_OUTPUT_VALUES),
                subtasks: vec![PackedNode::Plain {
                    program_output: vec![],
                }],
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
            packed: PackedNode::Composite {
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

    /// `LEAF_PREPROCESSED_ROOT` (eight words) as the 32-byte digest a `leaf_prover` output carries,
    /// i.e. the little-endian bytes `LeafInput::preprocessed_root` reads back.
    fn leaf_preprocessed_root_bytes() -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for (i, w) in LEAF_PREPROCESSED_ROOT.iter().enumerate() {
            bytes[i * 4..i * 4 + 4].copy_from_slice(&w.to_le_bytes());
        }
        bytes
    }

    /// Folds `n` identical leaves — each a `LeafInput` mirroring a `leaf_prover` output (the
    /// pre-generated fixture proof inline, with its outputs and preprocessed root) — with the
    /// binary entry point, and asserts the produced root proof, root outputs, and full
    /// `packed_output` tree match what we recompute independently (topology + values) from the
    /// identical leaves.
    fn dupe_and_fold(n: usize, dir: &std::path::Path) {
        init_tracing();
        let proof_bytes = std::fs::read(leaf_proof_fixture()).unwrap();
        // The leaf's N_RESERVED output values as `[u32; 4]` QM31 limbs (each a u32 word packed into
        // a QM31), exactly as `leaf_prover` emits `circuit_output`.
        let circuit_output: Vec<[u32; 4]> = LEAF_OUTPUT_VALUES
            .iter()
            .map(|&w| qm31_to_u32_limbs(&QM31::pack_u32(w)))
            .collect();
        let circuit_preprocessed_root = leaf_preprocessed_root_bytes();

        let leaves: Vec<LeafInput> = (0..n)
            .map(|_| LeafInput {
                program_output: vec![],
                circuit_output: circuit_output.clone(),
                circuit_preprocessed_root,
                proof: proof_bytes.clone(),
            })
            .collect();
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
            expected.packed.output_values().to_vec(),
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
