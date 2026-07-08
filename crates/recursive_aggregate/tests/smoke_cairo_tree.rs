//! Step-1 smoke test: fold an N=4 tree of cairo-verifier leaf proofs into a single root, using the
//! committed cairo proof fixture as four identical leaves.
//!
//! A successful root prove is end-to-end validation of the recursion: the root node runs the STARK
//! verifier on its children in-circuit (at k=FOLD_ARITY=8, N=4 folds into a single short 4-child
//! root), so the root only proves if all four cairo leaf proofs verified in-circuit.
//!
//! Heavy (real proving) — run on the prover VM, not the laptop:
//!   cargo +nightly-2026-01-15 test -p recursive-aggregate --release \
//!     --test smoke_cairo_tree -- --nocapture --test-threads=1

use std::time::Instant;

use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_multiverifier::verify::SharedConfig;
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use blake2::{Blake2s256, Digest};
use circuit_common::N_RESERVED;
use circuits::blake::HashValue;
use circuits_stark_verifier::order_hash_map::OrderedHashMap;
use circuits_stark_verifier::proof::ProofConfig;
use std::sync::Arc;

use recursive_aggregate::{
    AggregateConfig, CircuitPrecompute, FOLD_ARITY, LeafBottom, PoolSet, TreeProof, ZkBlind,
    node_preprocessed_from_shared, preprocessed_root, prove_root_verification_leaves,
    recursive_aggregate_prove_leaves,
};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

/// A modest pool set for tests: 2 pools sized to half the machine. Mirrors the harness's
/// partitioning so the fold exercises the concurrent path; correctness is independent of the sizes.
fn test_pools() -> PoolSet {
    let cores = std::thread::available_parallelism()
        .map(|c| c.get())
        .unwrap_or(2);
    PoolSet::new(2, (cores / 2).max(1))
}

// --- Constants mirrored from stwo-circuits circuit_multiverifier::verify_test (rev 041ec610). ---

const LOG_BLOWUP_FACTOR: u32 = 3;
const PRIVACY_CAIRO_VERIFIER_TRACE_LOG_SIZE: u32 = 21;
const CIRCUIT_N_PREPROCESSED_COLUMNS: usize = 45;

const PRIVACY_CAIRO_VERIFIER_PREPROCESSED_ROOT: [u32; 8] = [
    1564451235, 1866679958, 2011431219, 402982173, 1661380608, 1553398776, 620364350, 714877734,
];

const MULTIVERIFIER_PREPROCESSED_ROOT: [u32; 8] = [
    1207218485, 45060776, 317382138, 1169749503, 506165738, 1544606560, 1742997373, 1081501915,
];

// NOTE: under #1425 `N_RESERVED == BLAKE2S_DIGEST_N_WORDS == 8`; a leaf's `output_values` is now the
// full eight-word digest. These first two words are the historical cairo-leaf fixture outputs; the
// remaining six are zero-padded stand-ins. The tests that actually PROVE with `proof_cairo.bin`
// (`smoke_*`, `opener_recomputes_known_root`) are VM-only and require regenerating the fixture's
// eight-word outputs on-box — a box concern. The laptop-runnable `mv_tree_root_output_two_phase`
// builds its own synthetic 8-word leaves, so it does not depend on these values.
fn cairo_output_values() -> [QM31; N_RESERVED] {
    let mut out = [QM31::from_m31_array([M31(0), M31(0), M31(0), M31(0)]); N_RESERVED];
    out[0] = QM31::from_m31_array([
        M31(151966945),
        M31(1514947052),
        M31(87572453),
        M31(633358207),
    ]);
    out[1] = QM31::from_m31_array([
        M31(462231094),
        M31(464091325),
        M31(2016711704),
        M31(1173534648),
    ]);
    out
}

/// Padding targets shared by every node. Sized for the k=FOLD_ARITY(=8) node under the #1425 8-word
/// root: the multiverifier test's original targets were for a 2-child node, and an 8-child node with
/// the 8-word preprocessed-root + `blake2s_u32s` preimage needs the larger targets below (measured
/// via `probe_node_sizes`; each is the smallest power of two that fits the k=8 node's unpadded size).
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

fn aggregate_config() -> AggregateConfig {
    let pcs_config = get_pcs_config(PRIVACY_CAIRO_VERIFIER_TRACE_LOG_SIZE, LOG_BLOWUP_FACTOR);
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
    let node_preprocessed_root = HashValue::from(MULTIVERIFIER_PREPROCESSED_ROOT);

    // Build the witness-independent node precompute once (committed tree0 + twiddles), reused by
    // every node prove. The leaves arrive pre-proven, so no leaf precompute is needed here.
    //
    // NOTE: the hardcoded `MULTIVERIFIER_PREPROCESSED_ROOT` / `PRIVACY_CAIRO_VERIFIER_PREPROCESSED_ROOT`
    // constants above are stale relative to stwo-circuits rev 041ec610 (the canonical node root the
    // cairo-leaf path produces at this rev is different). The off-circuit-only tests still use the old
    // constants as opaque hash inputs, so we don't touch them here; for the precompute's soundness
    // guard we assert against the *freshly computed* node root so the optimization is exercised and the
    // cache is internally consistent with the circuit `prove_node` actually proves.
    let node_pp = node_preprocessed_from_shared(&shared_config, target_padding_sizes(), FOLD_ARITY);
    let node_root = preprocessed_root(&node_pp, LOG_BLOWUP_FACTOR);
    let node_precompute = Some(Arc::new(CircuitPrecompute::new(
        node_pp,
        pcs_config,
        node_root,
    )));

    // These cairo stand-in smoke tests exercise the fold plumbing, not the leaf↔node decoupling.
    // The synthetic cairo leaves share the node's shape (the historical single-target regime), so
    // the level-1 (leaf-verifying) and level-≥2 (node-verifying) configs coincide here: R1 == R2 and
    // both shared configs are the same. `node_shared_config` is used both to build node-verifying
    // nodes and to verify the root in the unpacker.
    let leaf_preprocessed_root = HashValue::from(PRIVACY_CAIRO_VERIFIER_PREPROCESSED_ROOT);
    AggregateConfig {
        // Shared / R2 (base-fanning) fields — real values, used by the shared up-tree fold.
        node_shared_config: shared_config,
        node_preprocessed_root: node_preprocessed_root.clone(),
        node_target_padding_sizes: target_padding_sizes(),
        node_pcs_config: pcs_config,
        node_precompute: node_precompute.clone(),
        fold_arity: FOLD_ARITY,
        // Base-fanning-only fields — UNUSED under FoldMode::LeafR1R2 (this smoke test's mode). Set to
        // the leaf root so the struct is well-formed; the leaf unpacker never reads them.
        base_node_preprocessed_root: leaf_preprocessed_root.clone(),
        base_preprocessed_root: leaf_preprocessed_root.clone(),
        // LeafR1R2 extras — the tier these cairo-leaf smoke tests exercise. Cairo stand-in: leaves
        // share the node's shape (single-target regime), so R1 == R2 and the leaf/node PCS coincide.
        leaf_shared_config: Some(make_shared()),
        level1_preprocessed_root: Some(node_preprocessed_root),
        leaf_preprocessed_root: Some(leaf_preprocessed_root),
        leaf_target_padding_sizes: Some(target_padding_sizes()),
        leaf_pcs_config: Some(pcs_config),
        level1_precompute: node_precompute,
        leaf_precompute: None,
    }
}

fn load_cairo_leaves(config: &AggregateConfig, n: usize) -> Vec<TreeProof> {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/test_data/proof_cairo.bin"
    ))
    .expect("test_data/proof_cairo.bin");
    let leaf_shared_config = config
        .leaf_shared_config
        .as_ref()
        .expect("smoke_cairo_tree config is LeafR1R2 (leaf_shared_config present)");
    let proof =
        deserialize_proof_with_config(&mut bytes.as_slice(), &leaf_shared_config.proof_config)
            .expect("deserialize cairo proof");
    (0..n)
        .map(|_| TreeProof {
            proof: proof.clone(),
            preprocessed_root: HashValue::from(PRIVACY_CAIRO_VERIFIER_PREPROCESSED_ROOT),
            output_values: cairo_output_values(),
        })
        .collect()
}

/// Level-0 leaf-node arities for `n` leaves — the plain-Rust mirror of `level0_group_sizes` in the
/// recursion crate (kept in sync by the topology tests there). Every leaf consumed, no lone leaf.
fn level0_group_sizes(n: usize) -> Vec<usize> {
    assert!(n >= 2);
    if n <= FOLD_ARITY {
        return vec![n];
    }
    let full = n / FOLD_ARITY;
    match n % FOLD_ARITY {
        0 => vec![FOLD_ARITY; full],
        1 => {
            let mut v = vec![FOLD_ARITY; full - 1];
            v.push(FOLD_ARITY - 1);
            v.push(2);
            v
        }
        r => {
            let mut v = vec![FOLD_ARITY; full];
            v.push(r);
            v
        }
    }
}

/// Off-circuit test oracle: recompute the multiverifier tree's root commitment `R` from the leaves'
/// `(preprocessed_root, output_values)` alone — the plain-Rust mirror of the in-circuit unpacker in
/// `prove_root_verification`. Used only to validate that the in-circuit hashing/shape reproduces a
/// known-good `R` without a VM prove; not part of the production path (there `R` is just the root
/// multiverifier proof's `output_values`). Mirrors the two-phase fold for any `N >= 1`.
///
/// `node_preprocessed_root` is the reported root a produced node carries. Under the cairo stand-in
/// (single-target) regime R1 == R2 and short-node roots collapse to the same value, so ONE constant
/// suffices here; the real decoupled unpacker recomputes R1/R2/short roots per (level, arity).
fn mv_tree_root_output(
    leaves: &[TreeProof],
    node_preprocessed_root: HashValue<QM31>,
) -> [QM31; N_RESERVED] {
    assert!(!leaves.is_empty());
    if leaves.len() == 1 {
        return leaves[0].output_values;
    }
    // LEVEL 0: consume all leaves into height-1 leaf-nodes (no leaf survives above height 1).
    let mut leaf_iter = leaves.iter();
    let mut level: Vec<(HashValue<QM31>, [QM31; N_RESERVED])> = level0_group_sizes(leaves.len())
        .into_iter()
        .map(|m| {
            let group: Vec<(HashValue<QM31>, [QM31; N_RESERVED])> = (0..m)
                .map(|_| {
                    let l = leaf_iter.next().unwrap();
                    (l.preprocessed_root.clone(), l.output_values)
                })
                .collect();
            (node_preprocessed_root.clone(), mv_node_hash(&group))
        })
        .collect();
    // LEVELS >= 1: classic group+carry over NODES only.
    while level.len() > 1 {
        if level.len() <= FOLD_ARITY {
            return mv_node_hash(&level);
        }
        let remainder = level.len() % FOLD_ARITY;
        let carry: Vec<(HashValue<QM31>, [QM31; N_RESERVED])> =
            level.split_off(level.len() - remainder);
        let mut next = Vec::with_capacity(level.len() / FOLD_ARITY + remainder);
        for group in level.chunks(FOLD_ARITY) {
            next.push((node_preprocessed_root.clone(), mv_node_hash(group)));
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

/// One multiverifier-node Blake binding over the children's `(preprocessed_root, outputs)`,
/// concatenated left-to-right — the plain-Rust mirror of the in-circuit node preimage in
/// `build_multiverifier_circuit`. Per child, the preimage is
/// `chain!(preprocessed_root [8 words], each output QM31 unpacked to its four M31 coords as u32)`,
/// hashed with `blake2s_u32s`. The node's output is the eight raw digest words, each re-encoded as a
/// QM31 `(lo, hi, 0, 0)` via `HashValue::from` — exactly what the in-circuit node emits.
fn mv_node_hash(children: &[(HashValue<QM31>, [QM31; N_RESERVED])]) -> [QM31; N_RESERVED] {
    let mut preimage: Vec<u32> = Vec::new();
    for (pp, outs) in children {
        preimage.extend(hash_value_to_u32s(pp));
        // `unpack_qm31s_to_u32_words` emits one word per M31 coordinate of each output QM31.
        for out in outs {
            preimage.extend(out.to_m31_array().map(|m| m.0));
        }
    }
    HashValue::<QM31>::from(blake2s_u32s_host(&preimage))
        .0
        .map(|w| *w.get())
}

#[test]
fn smoke_fold_four_cairo_leaves() {
    if std::env::var("GATE_AIR_HEAVY_RECURSION").is_err() {
        eprintln!(
            "smoke_fold_four_cairo_leaves: SKIPPED (heavy: real STARK proves, VM only). Set \
             GATE_AIR_HEAVY_RECURSION=1 to run."
        );
        return;
    }
    let config = aggregate_config();
    let leaves = load_cairo_leaves(&config, 4);

    let t0 = Instant::now();
    let out = recursive_aggregate_prove_leaves(leaves, &config, &test_pools());
    let elapsed = t0.elapsed();

    // At k=FOLD_ARITY (=8), 4 leaves (< k) fold in ONE level into a single short 4-child root.
    assert_eq!(out.n_levels, 1, "4 leaves at k=8 fold in one level (single short root)");
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
/// At k=FOLD_ARITY (=8), builds N=k+1 leaves with distinct `(pp_root, outputs)` so positions matter,
/// and checks [`mv_tree_root_output`] against a hand-rolled recompute of the NEW topology: level 0
/// splits the 9 leaves into TWO leaf-nodes of arity `(k-1, 2)` (`level0_group_sizes(9) == [7, 2]`),
/// then the root folds those two NODES. This is the fix: no bare leaf is carried above height 1 (the
/// old shape `node([0..8]) + carried leaf 8` put a lift24 leaf under the lift25 root ⇒ Merkle panic).
/// Exercises the short level-0 grouping and the homogeneous node-node root off circuit (the
/// in-circuit twin is exercised on the VM).
#[test]
fn mv_tree_root_output_two_phase() {
    // RUN-GUARD: `aggregate_config()` commits a 2^22-padded node preprocessed tree (CPU
    // interpolation + Merkle, ~minutes), so gate it to GATE_AIR_HEAVY_RECURSION even though it does
    // NOT prove/verify — keeps plain `cargo test` fast. Off-circuit shape check only.
    if std::env::var("GATE_AIR_HEAVY_RECURSION").is_err() {
        eprintln!(
            "mv_tree_root_output_two_phase: SKIPPED (builds a 2^22 preprocessed tree). Set \
             GATE_AIR_HEAVY_RECURSION=1 to run."
        );
        return;
    }
    assert_eq!(FOLD_ARITY, 8, "this hand-rolled shape is written for k=8");
    let config = aggregate_config();
    let base = load_cairo_leaves(&config, 1).pop().unwrap();
    let node_pp = config.node_preprocessed_root.clone();
    let q = |a: u32| QM31::from_m31_array([M31(a), M31(0), M31(0), M31(0)]);
    // Distinct 8-word pp_root + 8-word outputs per leaf so position matters.
    // The proof field is unused by `mv_tree_root_output`; only (pp_root, output_values) matter.
    let leaf = |i: u32| TreeProof {
        proof: base.proof.clone(),
        preprocessed_root: HashValue::from(std::array::from_fn::<u32, N_RESERVED, _>(|j| {
            i + 1 + j as u32
        })),
        output_values: std::array::from_fn(|j| q(10 * i + 3 + j as u32)),
    };
    let n = FOLD_ARITY + 1; // 9
    let leaves: Vec<TreeProof> = (0..n as u32).map(leaf).collect();
    assert_eq!(level0_group_sizes(n), vec![FOLD_ARITY - 1, 2], "N=9 level-0 split");

    let group = |lo: usize, hi: usize| -> Vec<(HashValue<QM31>, [QM31; N_RESERVED])> {
        (lo..hi)
            .map(|i| (leaves[i].preprocessed_root.clone(), leaves[i].output_values))
            .collect()
    };
    // Level 0: leaf-node A over leaves 0..7, leaf-node B over leaves 7..9.
    let node_a = mv_node_hash(&group(0, FOLD_ARITY - 1));
    let node_b = mv_node_hash(&group(FOLD_ARITY - 1, n));
    // Root: node-node fold over (A, B), both reported at node_pp.
    let expected = mv_node_hash(&[(node_pp.clone(), node_a), (node_pp.clone(), node_b)]);

    assert_eq!(
        mv_tree_root_output(&leaves, node_pp),
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
// binding — and thus this value — changes. Re-capture it from a fresh `smoke_fold_four_cairo_leaves`
// prove on the VM (it prints `root output_values`) and drop the `#[ignore]`.
#[test]
#[ignore = "stale k=2 golden; recapture the k=8 N=4 root on-box (see smoke_fold_four_cairo_leaves)"]
fn opener_recomputes_known_root() {
    // RUN-GUARD (in addition to #[ignore]): `aggregate_config()` builds a 2^22 preprocessed tree.
    if std::env::var("GATE_AIR_HEAVY_RECURSION").is_err() {
        eprintln!("opener_recomputes_known_root: SKIPPED. Set GATE_AIR_HEAVY_RECURSION=1 to run.");
        return;
    }
    let config = aggregate_config();
    let leaves = load_cairo_leaves(&config, 4);

    let root = mv_tree_root_output(&leaves, config.node_preprocessed_root);

    // The root output_values printed by the passing N=4 smoke prove (gate-for-gate the in-circuit
    // Blake binding the multiverifier emitted). STALE at k=8 AND at the #1425 8-word root — the root
    // is now the full eight-word digest, not two reduced QM31s. Recapture all eight words on-box.
    let mut expected = [QM31::from_m31_array([M31(0), M31(0), M31(0), M31(0)]); N_RESERVED];
    expected[0] = QM31::from_m31_array([
        M31(1466062331),
        M31(2095555614),
        M31(814256726),
        M31(92449459),
    ]);
    expected[1] = QM31::from_m31_array([
        M31(160575954),
        M31(794103935),
        M31(313097236),
        M31(1202656710),
    ]);
    assert_eq!(
        root, expected,
        "opener must reproduce the multiverifier root commitment"
    );
}

/// Full root verification: fold 4 cairo leaves → root, then build+prove the root verification that
/// verifies the root in-circuit, unpacks it to the leaf outputs, and emits them. Heavy — VM only.
#[test]
fn smoke_root_verification() {
    if std::env::var("GATE_AIR_HEAVY_RECURSION").is_err() {
        eprintln!(
            "smoke_root_verification: SKIPPED (heavy: real STARK proves, VM only). Set \
             GATE_AIR_HEAVY_RECURSION=1 to run."
        );
        return;
    }
    let config = aggregate_config();
    let leaves = load_cairo_leaves(&config, 4);

    let out = recursive_aggregate_prove_leaves(leaves.clone(), &config, &test_pools());

    let t0 = Instant::now();
    let bottom = LeafBottom { leaves: leaves.clone() };
    let rv = prove_root_verification_leaves(&out.root, &bottom, &config, LOG_BLOWUP_FACTOR, None);
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
        mv_tree_root_output(&leaves, config.node_preprocessed_root),
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
fn smoke_root_verification_zk_blinded() {
    if std::env::var("GATE_AIR_HEAVY_RECURSION").is_err() {
        eprintln!(
            "smoke_root_verification_zk_blinded: SKIPPED (heavy: real STARK proves, VM only). Set \
             GATE_AIR_HEAVY_RECURSION=1 to run."
        );
        return;
    }
    let config = aggregate_config();
    let leaves = load_cairo_leaves(&config, 4);
    let out = recursive_aggregate_prove_leaves(leaves.clone(), &config, &test_pools());

    let n_queries = get_pcs_config(PRIVACY_CAIRO_VERIFIER_TRACE_LOG_SIZE, LOG_BLOWUP_FACTOR)
        .fri_config
        .n_queries;
    let zk = ZkBlind {
        seed: [7u8; 32],
        n_padding: n_queries,
    };

    let t0 = Instant::now();
    let bottom = LeafBottom { leaves: leaves.clone() };
    let rv =
        prove_root_verification_leaves(&out.root, &bottom, &config, LOG_BLOWUP_FACTOR, Some(zk));
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

