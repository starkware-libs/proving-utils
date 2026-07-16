use circuit_common::finalize::{ComponentSizes, compute_padded_sizes};

use crate::canonical::{
    CanonicalCircuit, TARGET_PADDING_SIZES, build_unpadded_leaf_context,
    build_unpadded_multiverifier_context,
};
use crate::fold::PackedNode;
use crate::{LeafInput, RecursiveTreeError, load_leaves};

// ------------------------------------------------------------------------------------------------
// Serde shapes.
// ------------------------------------------------------------------------------------------------

#[test]
fn test_leaf_input_roundtrips() {
    // A representative leaf: `proof` is base64 ("AQID" = bytes [1, 2, 3]) and
    // `circuit_preprocessed_root` is 32 bytes, with the injected `output_preimage` flattened in.
    let root_bytes: Vec<u8> = (0..32).collect();
    let json = format!(
        r#"{{"output_preimage":["5","11"],"circuit_preprocessed_root":{root_bytes:?},"proof":"AQID"}}"#,
    );
    let leaf: LeafInput = serde_json::from_str(&json).unwrap();
    assert_eq!(leaf.output_preimage, vec!["5", "11"]);
    assert_eq!(leaf.proof.circuit_preprocessed_root[0], 0);
    assert_eq!(leaf.proof.circuit_preprocessed_root[31], 31);
    assert_eq!(leaf.proof.proof, vec![1, 2, 3]);
    // The wrapper is flattened: it round-trips through the same flat JSON object,
    // `SerializedLeafProof` fields at top level next to `output_preimage`.
    let back = serde_json::to_string(&leaf).unwrap();
    let leaf2: LeafInput = serde_json::from_str(&back).unwrap();
    assert_eq!(leaf2, leaf);
}

#[test]
fn test_load_leaves_reads_manifest_of_paths() {
    let tmp = tempfile::tempdir().unwrap();
    let leaf_path = tmp.path().join("leaf0.json");
    std::fs::write(
        &leaf_path,
        r#"{"output_preimage":["2"],"circuit_preprocessed_root":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"proof":"AQID"}"#,
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
    assert_eq!(leaves[0].output_preimage, vec!["2"]);
    assert_eq!(leaves[0].proof.proof, vec![1, 2, 3]);
}

/// [`LeafInput::output_values`] must replay the leaf's full hash chain — cairo0-encoded Blake2s of
/// the preimage to the Uint256 `H1`, then the circuit's Blake2s over the two halves' 9-bit-limb
/// encoding. Golden values recomputed independently (and matching a real leaf-bootloader run).
#[test]
fn test_leaf_output_values_derived_from_preimage() {
    let leaf = LeafInput {
        proof: crate::SerializedLeafProof {
            circuit_preprocessed_root: [0; 32],
            proof: vec![],
        },
        output_preimage: [
            "1433852663250257978909904594223798547176815246431631498282706690602142197827",
            "11",
            "13",
            "17",
        ]
        .map(str::to_string)
        .to_vec(),
    };
    assert_eq!(
        leaf.output_values().unwrap(),
        [
            674598343, 2086328319, 2388903078, 494718056, 1680677827, 3548094245, 1935139671,
            3988038855,
        ]
    );
}

#[test]
fn test_leaf_output_values_rejects_invalid_felt() {
    let leaf = LeafInput {
        proof: crate::SerializedLeafProof {
            circuit_preprocessed_root: [0; 32],
            proof: vec![],
        },
        output_preimage: vec!["not-a-felt".to_string()],
    };
    match leaf.output_values() {
        Err(RecursiveTreeError::BadLeafOutputs { reason }) => {
            assert!(reason.contains("not-a-felt"))
        }
        other => panic!("expected BadLeafOutputs, got {other:?}"),
    }
}

#[test]
fn test_packed_node_serializes_leaf_and_internal() {
    // A leaf: a `Composite` (the leaf circuit) over `Plain` (the raw preimage reveal).
    let leaf_a = PackedNode::leaf(vec!["1".to_string(), "2".to_string()]);
    // Serializes as `{"Composite": { subtasks: [{"Plain": { output_preimage }}] }}`.
    let leaf_json: serde_json::Value =
        serde_json::from_str(&serde_json::to_string(&leaf_a).unwrap()).unwrap();
    assert_eq!(
        leaf_json["Composite"]["subtasks"][0]["Plain"]["output_preimage"][0],
        "1"
    );

    // Internal: a `Composite` over two child subtasks.
    let leaf_b = PackedNode::leaf(vec![]);
    let internal = PackedNode::internal(leaf_a, leaf_b);

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
fn test_target_padding_sizes_are_consistent() {
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
fn test_canonical_circuit_builds_with_matching_preprocessed_root() {
    CanonicalCircuit::build()
        .expect("canonical circuit should build with matching preprocessed root");
}

// ------------------------------------------------------------------------------------------------
// End-to-end fold over a pre-generated leaf proof (gated behind the `slow-tests` feature).
//
// This test focuses on the recursive-tree fold itself and does NOT run `leaf_prover`. It
// duplicates a single pre-generated privacy cairo-verifier proof (the fixture at
// `test_data/privacy_cairo_verifier_proof.bin`, taken from `circuit_multiverifier`'s
// `test_data/circuit_multiverifier/proof_cairo.bin`) as N layer-0 entries and folds them. The
// entries are built directly (not through `LeafInput`): the privacy fixture's output values stem
// from the *privacy* bootloader's hash chain, not the leaf bootloader's, so they are not derivable
// by `LeafInput::output_values` — that derivation is unit-tested separately. The tree is
// configured to match the fixture proof (see `canonical`), so every fold builds and proves a real
// multiverifier circuit over two valid child proofs. Still proving-heavy (one multiverifier proof
// per pair), hence `slow-tests`; run in RELEASE mode (`cargo test --release --features
// slow-tests`).
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
    use crate::fold::{LayerEntry, PackedNode};
    use crate::{fold_entries, output};

    /// Preprocessed root of the cairo-verifier circuit that produced the committed fixture proof
    /// `test_data/privacy_cairo_verifier_proof.bin` (matches
    /// `circuit_multiverifier::test_utils::PRIVACY_CAIRO_VERIFIER_PREPROCESSED_ROOT`).
    const LEAF_PREPROCESSED_ROOT: [u32; circuit_common::N_RESERVED] = [
        3927153469, 2149409952, 1045374089, 2379944016, 2639147837, 600016285, 2135210114,
        302122822,
    ];

    /// The output values attested by the pre-generated privacy cairo-verifier proof (matches
    /// `circuit_multiverifier::test_utils::PRIVACY_CAIRO_VERIFIER_OUTPUT_VALUES`). Set on each
    /// duplicated layer-0 entry so the multiverifier's output check is satisfied.
    const LEAF_OUTPUT_VALUES: [u32; circuit_common::N_RESERVED] = [
        3035180123, 3555538090, 587798257, 1881776298, 3385462846, 2102605012, 3369268656,
        403460632,
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
            lifting_log_size,
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
            // The fixture leaves carry an empty preimage (see `dupe_and_fold`), so each leaf is a
            // `Composite` over an empty `Plain`.
            packed: PackedNode::leaf(vec![]),
        }
    }

    /// Mirrors `reduce_pair`'s output: the multiverifier hashes, for each child, its preprocessed
    /// root (8 words) followed by its raw output words (8 words), and keeps the resulting
    /// eight-word digest as its own output.
    fn expected_reduce(
        left: ExpectedNode,
        right: ExpectedNode,
        multiverifier_root: [u32; circuit_common::N_RESERVED],
    ) -> ExpectedNode {
        let mut preimage = Vec::new();
        for child in [&left, &right] {
            preimage.extend_from_slice(&child.preprocessed_root);
            preimage.extend_from_slice(&child.output_words);
        }
        let output_words = blake2s_u32s_host(&preimage);
        ExpectedNode {
            output_words,
            preprocessed_root: multiverifier_root,
            packed: PackedNode::internal(left.packed, right.packed),
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

    /// Folds `n` identical layer-0 entries — each carrying the pre-generated fixture proof, its
    /// output values, and its preprocessed root, exactly as `LayerEntry::from_leaf` would populate
    /// them for a real leaf — and asserts the fold's shape stats plus the produced root proof,
    /// root outputs, and full `packed_output` tree match what we recompute independently
    /// (topology + values) from the identical leaves.
    fn dupe_and_fold(n: usize, dir: &std::path::Path) {
        init_tracing();
        let proof_bytes = std::fs::read(leaf_proof_fixture()).unwrap();

        let canonical = CanonicalCircuit::build().unwrap();
        let entries: Vec<LayerEntry> = (0..n)
            .map(|_| LayerEntry {
                proof_bytes: proof_bytes.clone(),
                preprocessed_root: HashValue::from(LEAF_PREPROCESSED_ROOT),
                output_values: LEAF_OUTPUT_VALUES,
                packed_output: PackedNode::leaf(vec![]),
            })
            .collect();
        let (root, stats) = fold_entries(entries, &canonical).unwrap();

        // A balanced two-to-one tree with odd-carry: depth = ceil(log2 n), reductions = n - 1.
        assert_eq!(stats.n_leaves, n, "leaf count mismatch");
        assert_eq!(
            stats.n_layers,
            n.next_power_of_two().ilog2() as usize,
            "layer count mismatch"
        );
        assert_eq!(stats.n_pair_reductions, n - 1, "reduction count mismatch");
        output::write_root_outputs(
            &root,
            &dir.join("root.proof"),
            &dir.join("root_outputs.json"),
            &dir.join("root_packed.json"),
        )
        .unwrap();

        // The root proof is the Cairo circuit verifier's `--arguments-file` stream: a JSON array
        // of hex-string felts (the final fold is proven with the standard Blake2s channel and
        // serialized via `prepare_circuit_proof_for_cairo_verifier`).
        let root_felts: Vec<String> =
            serde_json::from_str(&std::fs::read_to_string(dir.join("root.proof")).unwrap())
                .expect("root proof parses as a JSON array of hex felts");
        assert!(
            !root_felts.is_empty() && root_felts.iter().all(|f| f.starts_with("0x")),
            "root proof felts must be 0x-prefixed hex strings"
        );

        // Independently recompute the whole tree (topology + hashed output values) from the leaves.
        let expected = expected_root(n, multiverifier_preprocessed_root(&canonical));

        let actual_outputs: Vec<u32> =
            serde_json::from_str(&std::fs::read_to_string(dir.join("root_outputs.json")).unwrap())
                .unwrap();
        assert_eq!(
            actual_outputs,
            expected.output_words.to_vec(),
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
    fn test_fold_two_leaves() {
        let tmp = tempfile::tempdir().unwrap();
        dupe_and_fold(2, tmp.path());
    }

    #[test]
    fn test_fold_three_leaves_with_carry() {
        let tmp = tempfile::tempdir().unwrap();
        dupe_and_fold(3, tmp.path());
    }

    #[test]
    fn test_fold_four_leaves() {
        let tmp = tempfile::tempdir().unwrap();
        dupe_and_fold(4, tmp.path());
    }
}
