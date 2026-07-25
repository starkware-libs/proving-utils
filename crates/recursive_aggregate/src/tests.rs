//! Step-1 smoke test: fold an N=4 tree of cairo-verifier leaf proofs into a single root, using the
//! committed cairo proof fixture as four identical leaves.
//!
//! A successful root prove is end-to-end validation of the recursion: the root node runs the STARK
//! verifier on its children in-circuit (at k=FOLD_ARITY=8, N=4 folds into a single short 4-child
//! root), so the root only proves if all four cairo leaf proofs verified in-circuit.
//!
//! Heavy (real proving) — run on the prover VM, not the laptop:
//!   cargo +nightly-2026-01-15 test -p recursive-aggregate --release \
//!     tests::smoke -- --nocapture --test-threads=1

use std::collections::BTreeMap;
use std::time::Instant;

use blake2::{Blake2s256, Digest};
use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_common::N_RESERVED;
use circuit_multiverifier::verify::SharedConfig;
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuit_verifier::circuit_hash::config_words;
use circuit_verifier::statement::{
    INTERACTION_POW_BITS, all_circuit_components, circuit_component_log_sizes,
};
use circuits::blake::HashValue;
use circuits::context::FinalizedContext;
use circuits_stark_verifier::order_hash_map::OrderedHashMap;
use circuits_stark_verifier::proof::ProofConfig;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::pools::PoolSet;
use crate::precomputes::{RecursionPrecompute, TreeSpec, node_preprocessed_from_shared};
use crate::prove::recursive_aggregate_fold_leaves;
use crate::prove_streaming::recursive_aggregate_prove_leaves_streaming;
use crate::root_prover::{LeafBottom, ZkBlind, prove_root_verification_leaves};
use crate::test_utils::{derive_unpacker_config, preprocessed_root};
use crate::{AggregateConfig, TreeProof, level0_group_sizes};

/// Fold arity `k` used by these tests (the production default; env parsing lives in the
/// `gate-air-leaf` binary, so the value is inlined here byte-identically).
const FOLD_ARITY: usize = 8;

/// A modest pool set for tests: 2 pools sized to half the machine. Mirrors the harness's
/// partitioning so the fold exercises the concurrent path; correctness is independent of the sizes.
fn test_pools() -> PoolSet {
    let cores = std::thread::available_parallelism()
        .map(|c| c.get())
        .unwrap_or(2);
    PoolSet::new(2, (cores / 2).max(1), None)
}

// --- Constants mirrored from stwo-circuits circuit_multiverifier::verify_test (rev 041ec610). ---

const LOG_BLOWUP_FACTOR: u32 = 3;
const LEAF_VERIFIER_TRACE_LOG_SIZE: u32 = 21;
const CIRCUIT_N_PREPROCESSED_COLUMNS: usize = 45;

const LEAF_VERIFIER_PREPROCESSED_ROOT: [u32; 8] = [
    1564451235, 1866679958, 2011431219, 402982173, 1661380608, 1553398776, 620364350, 714877734,
];

// NOTE: under #1425 `N_RESERVED == BLAKE2S_DIGEST_N_WORDS == 8`; a leaf's `output_values` is now
// the full eight-word digest. These first two words are the historical cairo-leaf fixture outputs;
// the remaining six are zero-padded stand-ins. The tests that actually PROVE with `proof_cairo.bin`
// (`smoke_*`, `opener_recomputes_known_root`) are VM-only and require regenerating the fixture's
// eight-word outputs on-box — a box concern. The laptop-runnable `mv_tree_root_output_two_phase`
// builds its own synthetic 8-word leaves, so it does not depend on these values.
// Each output is now a single raw digest word (u32), not a full QM31. These are stand-in
// placeholders; the tests that consume them (`smoke_*`) PROVE with `proof_cairo.bin` and are
// box-only — they require regenerating the fixture's eight raw output words on-box.
fn cairo_output_values() -> [u32; N_RESERVED] {
    let mut out = [0u32; N_RESERVED];
    out[0] = 151966945;
    out[1] = 462231094;
    out
}

/// Padding targets shared by every node. Sized for the k=FOLD_ARITY(=8) node under the #1425 8-word
/// root: the multiverifier test's original targets were for a 2-child node, and an 8-child node
/// with the 8-word preprocessed-root + `blake2s_u32s` preimage needs the larger targets below
/// (measured via `probe_node_sizes`; each is the smallest power of two that fits the k=8 node's
/// unpadded size).
fn target_padding_sizes() -> circuit_common::finalize::ComponentSizes {
    circuit_common::finalize::ComponentSizes {
        eq: 1 << 17,
        qm31_ops: 1 << 22,
        m31_to_u32: 1 << 20,
        triple_xor: 1 << 19,
        blake_g_gate: 1 << 22,
    }
}

fn multiverifier_preprocessed_column_log_sizes() -> OrderedHashMap<PreProcessedColumnId, u32> {
    [
        ("bitwise_xor_4_0", 8),
        ("bitwise_xor_4_1", 8),
        ("bitwise_xor_4_2", 8),
        ("bitwise_xor_7_0", 14),
        ("bitwise_xor_7_1", 14),
        ("bitwise_xor_7_2", 14),
        ("seq_16", 16),
        ("bitwise_xor_8_0", 16),
        ("bitwise_xor_8_1", 16),
        ("bitwise_xor_8_2", 16),
        ("eq_in0_address", 17),
        ("eq_in1_address", 17),
        ("triple_xor_input_addr_0", 17),
        ("triple_xor_input_addr_1", 17),
        ("triple_xor_input_addr_2", 17),
        ("triple_xor_output_addr", 17),
        ("triple_xor_multiplicity", 17),
        ("m31_to_u32_input_addr", 18),
        ("m31_to_u32_output_addr", 18),
        ("m31_to_u32_multiplicity", 18),
        ("bitwise_xor_9_0", 18),
        ("bitwise_xor_9_1", 18),
        ("bitwise_xor_9_2", 18),
        ("blake_g_gate_input_addr_a", 20),
        ("blake_g_gate_input_addr_b", 20),
        ("blake_g_gate_input_addr_c", 20),
        ("blake_g_gate_input_addr_d", 20),
        ("blake_g_gate_input_addr_f0", 20),
        ("blake_g_gate_input_addr_f1", 20),
        ("blake_g_gate_output_addr_a", 20),
        ("blake_g_gate_output_addr_b", 20),
        ("blake_g_gate_output_addr_c", 20),
        ("blake_g_gate_output_addr_d", 20),
        ("blake_g_gate_multiplicity", 20),
        ("bitwise_xor_10_0", 20),
        ("bitwise_xor_10_1", 20),
        ("bitwise_xor_10_2", 20),
        ("qm31_ops_add_flag", 21),
        ("qm31_ops_sub_flag", 21),
        ("qm31_ops_mul_flag", 21),
        ("qm31_ops_pointwise_mul_flag", 21),
        ("qm31_ops_in0_address", 21),
        ("qm31_ops_in1_address", 21),
        ("qm31_ops_out_address", 21),
        ("qm31_ops_mults", 21),
    ]
    .into_iter()
    .map(|(id, log_size)| (PreProcessedColumnId { id: id.to_string() }, log_size))
    .collect()
}

fn aggregate_config() -> RecursionPrecompute {
    let pcs_config = get_pcs_config(LEAF_VERIFIER_TRACE_LOG_SIZE, LOG_BLOWUP_FACTOR);
    let proof_config = ProofConfig::new(
        &all_circuit_components::<QM31>(),
        CIRCUIT_N_PREPROCESSED_COLUMNS,
        &pcs_config,
        INTERACTION_POW_BITS,
    );
    // `SharedConfig` is not `Clone`, so build one per field it's stored in (leaf + node). The cairo
    // stand-in leaves share the node's shape here, so both configs are identical.
    let make_shared = || SharedConfig {
        pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: multiverifier_preprocessed_column_log_sizes(),
    };
    let shared_config = make_shared();

    // These cairo stand-in smoke tests exercise the fold plumbing, not the leaf↔node decoupling.
    // The synthetic cairo leaves share the node's shape (single-target regime), so the
    // level1-node and fold-node roots coincide at every arity and both shared configs are the
    // same. `node_shared_config` builds node-verifying nodes and verifies the root in the
    // unpacker.
    //
    // NOTE: the hardcoded `LEAF_VERIFIER_PREPROCESSED_ROOT` constant is stale relative to
    // stwo-circuits (the canonical leaf root the cairo-leaf path produces is different). The
    // off-circuit-only tests use it as an opaque hash input; the tree precompute's soundness guard
    // asserts against the FRESHLY computed node root so the cache is internally consistent with the
    // circuit `prove_leaf_or_short` / `prove_short_fold_node` actually proves.
    //
    // Build a per-arity level1/fold root table + the held per-arity trees. `RecursionPrecompute`
    // now holds one tree per arity, so build every arity 2..=k (the pinned-tree design proves
    // each short arity from its own held tree, not by rebuilding).
    let arity_root = |arity: usize| -> HashValue<QM31> {
        let pp = node_preprocessed_from_shared(&shared_config, target_padding_sizes(), arity);
        preprocessed_root(&pp, LOG_BLOWUP_FACTOR)
    };
    let mut level1_roots: BTreeMap<usize, HashValue<QM31>> = BTreeMap::new();
    let mut fold_roots: BTreeMap<usize, HashValue<QM31>> = BTreeMap::new();
    for arity in 2..=FOLD_ARITY {
        let root = arity_root(arity);
        level1_roots.insert(arity, root.clone());
        fold_roots.insert(arity, root);
    }

    let leaf_preprocessed_root = HashValue::from(LEAF_VERIFIER_PREPROCESSED_ROOT);

    // Held per-arity trees (leaf tree stands in as an arity-2 node — leaves arrive pre-proven so it
    // is never actually used, but the flat struct requires a leaf tree). Cairo stand-in: level1
    // == fold. Built from `config.fold_shared_config` after the config takes `shared_config`.
    let config = AggregateConfig {
        // Shared / fold-node fields — real values, used by the shared up-tree fold.
        fold_shared_config: shared_config,
        node_target_padding_sizes: target_padding_sizes(),
        node_pcs_config: pcs_config,
        fold_arity: FOLD_ARITY,
        // Leaf / level1 fields — the tier these cairo-leaf smoke tests exercise. Cairo stand-in:
        // level1 == fold roots at every arity (single-target regime); leaf/node PCS coincide.
        leaf_shared_config: make_shared(),
        level1_roots,
        fold_roots,
        leaf_preprocessed_root,
        leaf_target_padding_sizes: target_padding_sizes(),
        leaf_pcs_config: pcs_config,
    };
    let spec = |arity: usize, root: HashValue<QM31>| TreeSpec {
        preprocessed: node_preprocessed_from_shared(
            &config.fold_shared_config,
            target_padding_sizes(),
            arity,
        ),
        pcs_config,
        expected_root: root,
    };
    let leaf = spec(2, config.level1_root(2));
    let level1: BTreeMap<usize, TreeSpec> = (2..=FOLD_ARITY)
        .map(|a| (a, spec(a, config.level1_root(a))))
        .collect();
    let fold: BTreeMap<usize, TreeSpec> = (2..=FOLD_ARITY)
        .map(|a| (a, spec(a, config.fold_root(a))))
        .collect();
    RecursionPrecompute::new(leaf, level1, fold, config)
}

fn load_cairo_leaves(config: &AggregateConfig, n: usize) -> Vec<TreeProof> {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/test_data/proof_cairo.bin"
    ))
    .expect("test_data/proof_cairo.bin");
    let leaf_shared_config = &config.leaf_shared_config;
    let proof =
        deserialize_proof_with_config(&mut bytes.as_slice(), &leaf_shared_config.proof_config)
            .expect("deserialize cairo proof");
    (0..n)
        .map(|_| TreeProof {
            proof: proof.clone(),
            preprocessed_root: HashValue::from(LEAF_VERIFIER_PREPROCESSED_ROOT),
            output_values: cairo_output_values(),
        })
        .collect()
}

/// Off-circuit test oracle: recompute the multiverifier tree's root commitment `R` from the leaves'
/// `(preprocessed_root, output_values)` alone — the plain-Rust mirror of the in-circuit unpacker in
/// `prove_root_verification`. Used only to validate that the in-circuit hashing/shape reproduces a
/// known-good `R` without a VM prove; not part of the production path (there `R` is just the root
/// multiverifier proof's `output_values`). Mirrors the two-phase fold for any `N >= 1`.
///
/// `node_preprocessed_root` is the reported root a produced node carries. Under the cairo stand-in
/// (single-target) regime the level1-node and fold-node roots are equal and short-node roots
/// collapse to the same value, so ONE constant suffices here; the real decoupled unpacker
/// recomputes level1/fold-node/short roots per (kind, arity).
fn mv_tree_root_output(
    leaves: &[TreeProof],
    node_preprocessed_root: HashValue<QM31>,
    config: &AggregateConfig,
) -> [u32; N_RESERVED] {
    assert!(!leaves.is_empty());
    if leaves.len() == 1 {
        return leaves[0].output_values;
    }
    // Level-0 nodes verify LEAVES; levels >= 1 verify NODES — the same per-height child-verifier
    // config selection the in-circuit unpacker (`NodeKind::child_shared_config`) uses.
    let leaf_shared = &config.leaf_shared_config;
    let fold_shared = &config.fold_shared_config;
    // LEVEL 0: consume all leaves into height-1 leaf-nodes (no leaf survives above height 1).
    let mut leaf_iter = leaves.iter();
    let mut level: Vec<(HashValue<QM31>, [u32; N_RESERVED])> =
        level0_group_sizes(leaves.len(), FOLD_ARITY)
            .into_iter()
            .map(|m| {
                let group: Vec<(HashValue<QM31>, [u32; N_RESERVED])> = (0..m)
                    .map(|_| {
                        let l = leaf_iter.next().unwrap();
                        (l.preprocessed_root.clone(), l.output_values)
                    })
                    .collect();
                (node_preprocessed_root.clone(), mv_node_hash(&group, leaf_shared))
            })
            .collect();
    // LEVELS >= 1: classic group+carry over NODES only.
    while level.len() > 1 {
        if level.len() <= FOLD_ARITY {
            return mv_node_hash(&level, fold_shared);
        }
        let remainder = level.len() % FOLD_ARITY;
        let carry: Vec<(HashValue<QM31>, [u32; N_RESERVED])> =
            level.split_off(level.len() - remainder);
        let mut next = Vec::with_capacity(level.len() / FOLD_ARITY + remainder);
        for group in level.chunks(FOLD_ARITY) {
            next.push((node_preprocessed_root.clone(), mv_node_hash(group, fold_shared)));
        }
        next.extend(carry);
        level = next;
    }
    level[0].1
}

/// Out-of-circuit mirror of [`circuits::blake::blake2s_u32s`]: hashes the little-endian words with
/// Blake2s and returns the eight raw digest words. Mirrors `verify_test::blake2s_u32s_host`.
fn blake2s_u32s_host(words: &[u32]) -> [u32; N_RESERVED] {
    let mut hasher = Blake2s256::new();
    for word in words {
        hasher.update(word.to_le_bytes());
    }
    let hash: [u8; 32] = hasher.finalize().into();
    std::array::from_fn(|i| u32::from_le_bytes(hash[i * 4..i * 4 + 4].try_into().unwrap()))
}

/// Extracts the eight raw 32-bit words from a `HashValue<QM31>` (each word held as
/// `(low_u16, high_u16, 0, 0)`). Mirrors `verify_test::hash_value_to_u32s`.
fn hash_value_to_u32s(hash: &HashValue<QM31>) -> [u32; N_RESERVED] {
    std::array::from_fn(|i| {
        let [low, high, 0, 0] = hash[i].get().to_m31_array().map(|m| m.0) else {
            panic!("hash word must have zeroes in the last two coordinates");
        };
        low | (high << 16)
    })
}

/// The child `circuit_hash` the multiverifier binds: `blake2s(config_words || preprocessed_root)`,
/// the plain-Rust mirror of `compute_circuit_hash`. `config_words` packs the FRI blowup + the
/// child-verifier's component log sizes (from `child_shared`); the eight preprocessed-root words
/// follow.
fn mv_circuit_hash(pp: &HashValue<QM31>, child_shared: &SharedConfig) -> [u32; N_RESERVED] {
    let components = all_circuit_components::<QM31>();
    let log_sizes =
        circuit_component_log_sizes(&components, &child_shared.preprocessed_column_log_sizes);
    let cfg_words = config_words(
        child_shared.pcs_config.fri_config.log_blowup_factor,
        &log_sizes,
    );
    let preimage: Vec<u32> = cfg_words
        .iter()
        .copied()
        .chain(hash_value_to_u32s(pp))
        .collect();
    blake2s_u32s_host(&preimage)
}

/// One multiverifier-node Blake binding over the children, concatenated left-to-right — the
/// plain-Rust mirror of the in-circuit node preimage in `build_multiverifier_circuit`. Per child the
/// preimage is `[circuit_hash (8 words), output words (one raw word per output)]`, hashed with
/// `blake2s_u32s`. `child_shared` is the parent node's child-verifier config (it fixes each child's
/// `circuit_hash`). The node's output is the eight raw digest words.
fn mv_node_hash(
    children: &[(HashValue<QM31>, [u32; N_RESERVED])],
    child_shared: &SharedConfig,
) -> [u32; N_RESERVED] {
    let mut preimage: Vec<u32> = Vec::new();
    for (pp, outs) in children {
        preimage.extend(mv_circuit_hash(pp, child_shared));
        // One raw word per output (NOT four M31 coords).
        preimage.extend(outs);
    }
    blake2s_u32s_host(&preimage)
}

#[test]
#[ignore = "box-only: real STARK proves"]
fn smoke_fold_four_cairo_leaves() {
    let pre = aggregate_config();
    let leaves = load_cairo_leaves(&pre.aggregate_config, 4);

    let t0 = Instant::now();
    let out = recursive_aggregate_fold_leaves(leaves, &pre, &test_pools());
    let elapsed = t0.elapsed();

    // At k=FOLD_ARITY (=8), 4 leaves (< k) fold in ONE level into a single short 4-child root.
    assert_eq!(
        out.n_levels, 1,
        "4 leaves at k=8 fold in one level (single short root)"
    );
    println!(
        "SMOKE OK (no blinding): 4 cairo leaves folded to root in {:.2}s ({} level, 1 node prove); \
         root output_values = {:?}",
        elapsed.as_secs_f64(),
        out.n_levels,
        out.root.output_values,
    );
}

/// Two-phase (decoupling-fix) shape check — NO proving, runs anywhere (laptop).
///
/// At k=FOLD_ARITY (=8), builds N=k+1 leaves with distinct `(pp_root, outputs)` so positions
/// matter, and checks [`mv_tree_root_output`] against a hand-rolled recompute of the NEW topology:
/// level 0 splits the 9 leaves into TWO leaf-nodes of arity `(k-1, 2)` (`level0_group_sizes(9) ==
/// [7, 2]`), then the root folds those two NODES. This is the fix: no bare leaf is carried above
/// height 1 (the old shape `node([0..8]) + carried leaf 8` put a lift24 leaf under the lift25 root
/// ⇒ Merkle panic). Exercises the short level-0 grouping and the homogeneous node-node root off
/// circuit (the in-circuit twin is exercised on the VM).
#[test]
#[ignore = "box-only: commits a 2^22 preprocessed tree (no prove; off-circuit shape check)"]
fn mv_tree_root_output_two_phase() {
    assert_eq!(FOLD_ARITY, 8, "this hand-rolled shape is written for k=8");
    let pre = aggregate_config();
    let config = &pre.aggregate_config;
    let base = load_cairo_leaves(config, 1).pop().unwrap();
    let node_pp = config.fold_root(FOLD_ARITY);
    let leaf_shared = &config.leaf_shared_config;
    let fold_shared = &config.fold_shared_config;
    // Distinct 8-word pp_root + 8-word (raw u32) outputs per leaf so position matters.
    // The proof field is unused by `mv_tree_root_output`; only (pp_root, output_values) matter.
    let leaf = |i: u32| TreeProof {
        proof: base.proof.clone(),
        preprocessed_root: HashValue::from(std::array::from_fn::<u32, N_RESERVED, _>(|j| {
            i + 1 + j as u32
        })),
        output_values: std::array::from_fn(|j| 10 * i + 3 + j as u32),
    };
    let n = FOLD_ARITY + 1; // 9
    let leaves: Vec<TreeProof> = (0..n as u32).map(leaf).collect();
    assert_eq!(
        level0_group_sizes(n, FOLD_ARITY),
        vec![FOLD_ARITY - 1, 2],
        "N=9 level-0 split"
    );

    let group = |lo: usize, hi: usize| -> Vec<(HashValue<QM31>, [u32; N_RESERVED])> {
        (lo..hi)
            .map(|i| (leaves[i].preprocessed_root.clone(), leaves[i].output_values))
            .collect()
    };
    // Level 0: leaf-node A over leaves 0..7, leaf-node B over leaves 7..9 (children are LEAVES).
    let node_a = mv_node_hash(&group(0, FOLD_ARITY - 1), leaf_shared);
    let node_b = mv_node_hash(&group(FOLD_ARITY - 1, n), leaf_shared);
    // Root: node-node fold over (A, B), both reported at node_pp (children are NODES).
    let expected = mv_node_hash(
        &[(node_pp.clone(), node_a), (node_pp.clone(), node_b)],
        fold_shared,
    );

    assert_eq!(
        mv_tree_root_output(&leaves, node_pp, config),
        expected,
        "N=k+1 root must match the two-phase (two leaf-nodes, node-node root) shape",
    );
}

/// Opener formula check — NO proving, runs anywhere (laptop).
///
/// Recomputes the multiverifier tree's root output from the 4 cairo leaves' `(ppR, outs)` via the
/// off-circuit [`mv_tree_root_output`] reference, and asserts it equals the exact root hash the
/// `smoke_fold_four_cairo_leaves` prove produced on the VM. This confirms the wrapper's opener
/// reconstructs the multiverifier commitment (which `circuit_unpacker`'s single-`pp_root` scheme
/// does not), so that the in-circuit opener can bind verified leaf outputs to the verified root.
// IGNORED pending on-box golden recapture at k=FOLD_ARITY: the stored `expected` below is the k=2
// N=4 root (two 2-child levels). At k=8 the N=4 tree is a single 4-child root, so the root's Blake
// binding — and thus this value — changes. Re-capture it from a fresh
// `smoke_fold_four_cairo_leaves` prove on the VM (it prints `root output_values`) and drop the
// `#[ignore]`.
#[test]
#[ignore = "stale k=2 golden; recapture the k=8 N=4 root on-box (see smoke_fold_four_cairo_leaves)"]
fn opener_recomputes_known_root() {
    let pre = aggregate_config();
    let config = &pre.aggregate_config;
    let leaves = load_cairo_leaves(config, 4);

    let root = mv_tree_root_output(&leaves, config.fold_root(FOLD_ARITY), config);

    // The root output_values printed by the passing N=4 smoke prove (gate-for-gate the in-circuit
    // Blake binding the multiverifier emitted). STALE — the root is now the eight raw digest words
    // AND the preimage changed to the new (circuit_hash, 1-word-per-output) scheme. Recapture all
    // eight words on-box.
    let mut expected = [0u32; N_RESERVED];
    expected[0] = 1466062331;
    expected[1] = 160575954;
    assert_eq!(
        root, expected,
        "opener must reproduce the multiverifier root commitment"
    );
}

/// Full root verification: fold 4 cairo leaves → root, then build+prove the root verification that
/// verifies the root in-circuit, unpacks it to the leaf outputs, and emits them. Heavy — VM only.
#[test]
#[ignore = "box-only: real STARK proves"]
fn smoke_root_verification() {
    let pre = aggregate_config();
    let leaves = load_cairo_leaves(&pre.aggregate_config, 4);

    let out = recursive_aggregate_fold_leaves(leaves.clone(), &pre, &test_pools());

    let t0 = Instant::now();
    let bottom = LeafBottom {
        leaves: leaves.clone(),
    };
    // Capture-style: recompute the pinned unpacker config to hand into the prover (production
    // supplies a pinned const instead).
    let unpacker_config = derive_unpacker_config(4, &pre.aggregate_config, LOG_BLOWUP_FACTOR, None);
    let rv = prove_root_verification_leaves(&out.root, &bottom, &pre, &unpacker_config, None);
    let elapsed = t0.elapsed();

    // The unpacker emits all 4 leaf outputs, bound in-circuit to the verified root.
    assert_eq!(rv.leaf_outputs.len(), 4, "unpacks all 4 leaf outputs");
    for lo in &rv.leaf_outputs {
        assert_eq!(
            *lo,
            cairo_output_values(),
            "emitted leaf output must equal the cairo leaf output"
        );
    }
    // Off-circuit twin of the in-circuit unpack must reach the same root.
    assert_eq!(
        mv_tree_root_output(
            &leaves,
            pre.aggregate_config.fold_root(FOLD_ARITY),
            &pre.aggregate_config
        ),
        out.root.output_values,
        "off-circuit recomputation of R must match"
    );
    println!(
        "ROOT-VERIFY OK: proof built in {:.2}s; trace 2^{}; unpacked {} leaf outputs bound to root",
        elapsed.as_secs_f64(),
        rv.trace_log_size,
        rv.leaf_outputs.len(),
    );
}

/// Root verification with zk-blinding ON — the hiding step. `add_zk_blinding` works here (a
/// `circuit_verifier`-family circuit), unlike on a multiverifier node. Asserts the blinded proof
/// still unpacks the same leaf outputs and reports the overhead.
#[test]
#[ignore = "box-only: real STARK proves"]
fn smoke_root_verification_zk_blinded() {
    let pre = aggregate_config();
    let leaves = load_cairo_leaves(&pre.aggregate_config, 4);
    let out = recursive_aggregate_fold_leaves(leaves.clone(), &pre, &test_pools());

    let n_queries = get_pcs_config(LEAF_VERIFIER_TRACE_LOG_SIZE, LOG_BLOWUP_FACTOR)
        .fri_config
        .n_queries;
    let zk = ZkBlind {
        seed: [7u8; 32],
        n_padding: n_queries,
    };

    let t0 = Instant::now();
    let bottom = LeafBottom {
        leaves: leaves.clone(),
    };
    let unpacker_config =
        derive_unpacker_config(4, &pre.aggregate_config, LOG_BLOWUP_FACTOR, Some(n_queries));
    let rv = prove_root_verification_leaves(&out.root, &bottom, &pre, &unpacker_config, Some(zk));
    let elapsed = t0.elapsed();

    assert_eq!(rv.leaf_outputs.len(), 4);
    for lo in &rv.leaf_outputs {
        assert_eq!(
            *lo,
            cairo_output_values(),
            "blinding must not change unpacked outputs"
        );
    }
    println!(
        "ROOT-VERIFY ZK OK: blinded proof built in {:.2}s; trace 2^{}; n_padding={}",
        elapsed.as_secs_f64(),
        rv.trace_log_size,
        n_queries,
    );
}

// NOTE: zk-blinding is intentionally NOT exercised here. No multiverifier node (root included) is
// ever published, so none is blinded; blinding belongs to the separate final wrapper circuit
// (verify-root + unpacker + commitment), which is the only published proof. That wrapper is a
// circuit_verifier-family circuit — the family `add_zk_blinding` is validated against — so blinding
// is tested there, once the wrapper exists.

/// Termination + panic propagation for [`recursive_aggregate_prove_leaves_streaming`]: a `build`
/// closure that panics must make the coordinator re-panic on the parent (via `thread::scope` join),
/// for BOTH n_pools == 1 and > 1 — no hang, no silent drop. The panic fires INSIDE `build`, before
/// any node proves, so the machinery under test is pure scheduling/termination (leaf-type-agnostic:
/// the input `W` is a bare `usize`, never turned into a real cairo leaf).
///
/// Box-only (`#[ignore]`d): `aggregate_config()` commits a 2^22-padded node preprocessed tree
/// (~minutes, GBs), even though no recursion PROVE runs (the build closure panics first).
#[test]
#[ignore = "box-only: builds a 2^22 preprocessed tree"]
fn streaming_wrap_panic_propagates() {
    let pre = aggregate_config();

    for n_pools in [1usize, 2] {
        let pre = &pre;
        let n_leaves = 2usize; // one level1 group (n <= k); build panics before any node proves.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let pools = PoolSet::new(n_pools, 2, None);
            let (tx, rx) = std::sync::mpsc::channel::<(usize, usize)>();
            for i in 0..n_leaves {
                tx.send((i, i)).unwrap();
            }
            drop(tx);
            // Every `build` panics — a worker panic must re-panic on the coordinator's
            // `thread::scope` join (not hang, not be silently dropped).
            recursive_aggregate_prove_leaves_streaming(
                rx,
                n_leaves,
                |i: usize| -> FinalizedContext<QM31> {
                    panic!("intentional build panic at leaf {i}")
                },
                pre,
                &pools,
            );
        }));
        assert!(
            result.is_err(),
            "n_pools={n_pools}: a panicking build must re-panic on the parent (no hang, no silent drop)"
        );
    }
}
