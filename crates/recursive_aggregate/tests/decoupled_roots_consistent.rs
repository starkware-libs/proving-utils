//! Defense-in-depth regression test for the leaf↔node decoupling fix: in a GENUINELY decoupled
//! config (R1 != R2, i.e. the leaf shape differs from the node shape — the regime that hid the
//! original carry bug), the two DIFFERENT full-`FOLD_ARITY` preprocessed-root build paths must
//! agree:
//!   - the config's trusted R1/R2 (`level1_preprocessed_root` / `node_preprocessed_root`), built the
//!     PRODUCTION way via `multiverifier_node_preprocessed` / `node_preprocessed_from_shared`
//!     (exactly as the downstream leaf prover's config derivation builds them), and
//!   - the witness-independent recompute the unpacker binds short nodes / the root to
//!     (`AggregateConfig::assert_full_arity_roots_consistent`, which goes through the private
//!     `short_node_preprocessed_root(FOLD_ARITY)`).
//!
//! If those diverged at full arity, the unpacker would bind full-`FOLD_ARITY` nodes to a root the
//! prover never reported and the fold/root verification would REJECT (fail-closed) — so this only
//! turns that one otherwise-unasserted recompute equivalence into a loud early check, and pins it in
//! the decoupled regime the smoke tests do NOT cover (their config is the collapsed R1==R2 regime).
//!
//! Laptop-runnable: builds preprocessed multiverifier circuits (CPU interpolation + Merkle commit),
//! NO full STARK prove. It is `#[ignore]`d because building several 2^22-padded node preprocessed
//! circuits takes a few minutes; run it explicitly with:
//!   cargo test -p recursive-aggregate --test decoupled_roots_consistent -- --ignored --nocapture

use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_common::finalize::ComponentSizes;
use circuit_multiverifier::verify::SharedConfig;
use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuits::blake::HashValue;
use circuits_stark_verifier::order_hash_map::OrderedHashMap;
use circuits_stark_verifier::proof::ProofConfig;
use recursive_aggregate::{
    AggregateConfig, FOLD_ARITY, multiverifier_node_preprocessed, node_preprocessed_from_shared,
    preprocessed_root, shared_config_for_leaf,
};
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

const LOG_BLOWUP_FACTOR: u32 = 3;
const CAIRO_TRACE_LOG_SIZE: u32 = 21;
const CAIRO_N_PREPROCESSED_COLUMNS: usize = 45;

/// Component-wise `max`, mirroring the downstream leaf prover's private `max_sizes`, used to grow the
/// common node target to the R1/R2 fixed point exactly like its config derivation does.
fn max_sizes(a: &ComponentSizes, b: &ComponentSizes) -> ComponentSizes {
    ComponentSizes {
        eq: a.eq.max(b.eq),
        qm31_ops: a.qm31_ops.max(b.qm31_ops),
        m31_to_u32: a.m31_to_u32.max(b.m31_to_u32),
        triple_xor: a.triple_xor.max(b.triple_xor),
        blake_g_gate: a.blake_g_gate.max(b.blake_g_gate),
    }
}

/// The cairo-verifier preprocessed column log sizes (a real, fixed leaf-verifier shape) — mirrored
/// from `smoke_cairo_tree.rs`. Used only to build a *seed* `SharedConfig` from which we manufacture
/// a small distinct "leaf" preprocessed circuit below.
fn cairo_preprocessed_column_log_sizes() -> OrderedHashMap<PreProcessedColumnId, u32> {
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

/// A strictly-SMALLER LEAF target — dominant components one power below the node target — so the
/// leaf's trace_log_size (~2^21) is strictly below the node's (~2^22). This is the real production
/// decoupling axis: the leaf PCS lifting (leaf_trace + blowup) is one below the node PCS lifting, so
/// a node verifying LEAF children (R1) has a different child Merkle-path length — hence different gate
/// structure — than a node verifying NODE children (R2). The leaf here is a small arity-2
/// multiverifier node whose unpadded sizes fit comfortably below these; `build_decoupled_config`
/// asserts the trace actually came out strictly smaller (fail-loud if the assumption breaks).
fn leaf_target_seed() -> ComponentSizes {
    ComponentSizes {
        eq: 1 << 16,
        qm31_ops: 1 << 21,
        m31_to_u32: 1 << 19,
        triple_xor: 1 << 18,
        blake_g_gate: 1 << 21,
    }
}

/// Builds a GENUINELY decoupled `AggregateConfig` (R1 != R2) using ONLY the production build paths
/// (`multiverifier_node_preprocessed` / `node_preprocessed_from_shared`), replicating the downstream
/// leaf prover's config-derivation node-fixed-point loop.
///
/// Decoupling source (mirrors production exactly): the "leaf" is a small arity-2 multiverifier node
/// padded to a SMALLER `leaf_target` (~2^21 trace, PCS lifting one below the node's), while the nodes
/// pad to `node_target` (~2^22 trace, one-higher lifting). A node verifying LEAF children (R1) then
/// has a different child Merkle-path length — hence different gate structure and preprocessed root —
/// than a node verifying NODE children (R2). This is the same leaf(~2^21)↔node(~2^22) lifting split
/// the config derivation produces for a real leaf circuit. Crucially, R1/R2 are built via
/// `multiverifier_node_preprocessed` / `node_preprocessed_from_shared`, NOT via
/// `short_node_preprocessed_root` — that recompute is the thing under test.
fn build_decoupled_config() -> AggregateConfig {
    // Seed shared config in the cairo-verifier shape (a real leaf-verifier proof shape).
    let seed_pcs = get_pcs_config(CAIRO_TRACE_LOG_SIZE, LOG_BLOWUP_FACTOR);
    let seed_proof_config = ProofConfig::new(
        &all_circuit_components::<QM31>(),
        CAIRO_N_PREPROCESSED_COLUMNS,
        &seed_pcs,
        INTERACTION_POW_BITS,
    );
    let seed_shared = SharedConfig {
        pcs_config: seed_pcs,
        proof_config: seed_proof_config,
        preprocessed_column_log_sizes: cairo_preprocessed_column_log_sizes(),
    };

    // Manufacture the "leaf" as a SMALL (arity-2) multiverifier node padded to the SMALLER leaf
    // target, so its trace (~2^21) — and hence its PCS lifting — is strictly below the node's.
    let leaf_target = leaf_target_seed();
    let leaf_pp = node_preprocessed_from_shared(&seed_shared, leaf_target.clone(), 2);
    // The leaf PCS lifting is pinned to the LEAF trace size (production `leaf_pcs_config` behaviour).
    let pcs = get_pcs_config(leaf_pp.trace_log_size, LOG_BLOWUP_FACTOR);
    let leaf_preprocessed_root = preprocessed_root(&leaf_pp, LOG_BLOWUP_FACTOR);
    let leaf_shared_config = shared_config_for_leaf(&leaf_pp, pcs);

    // Node-size fixed point over the two variants, IDENTICAL to `derive_aggregate_config` (uses the
    // LEAF pcs throughout the loop; the node pcs is applied to R2's shape afterwards).
    let (_, node1_seed_sizes) = multiverifier_node_preprocessed(&leaf_pp, pcs, None, FOLD_ARITY);
    let mut node_target = node1_seed_sizes;
    let level1_pp = loop {
        let (level1_pp, level1_unpadded) =
            multiverifier_node_preprocessed(&leaf_pp, pcs, Some(node_target.clone()), FOLD_ARITY);
        let (_node_pp, node2_unpadded) =
            multiverifier_node_preprocessed(&level1_pp, pcs, Some(node_target.clone()), FOLD_ARITY);
        let new_target = max_sizes(&level1_unpadded, &node2_unpadded);
        if new_target == node_target {
            break level1_pp;
        }
        node_target = new_target;
    };

    // The node trace MUST have come out strictly larger than the leaf trace — otherwise the PCS
    // liftings coincide and R1 == R2 (collapse). Fail loud here so the test can never silently run in
    // the collapsed regime.
    assert!(
        level1_pp.trace_log_size > leaf_pp.trace_log_size,
        "node trace (2^{}) must exceed leaf trace (2^{}) for genuine lifting decoupling",
        level1_pp.trace_log_size,
        leaf_pp.trace_log_size
    );

    // R1: the leaf-verifying node's root, built (like the loop) with the LEAF pcs child config.
    let level1_preprocessed_root = preprocessed_root(&level1_pp, LOG_BLOWUP_FACTOR);

    // Node PCS (lifting one above the leaf's) + node shared config, then build R2 from that config
    // with the NODE pcs — exactly as `derive_aggregate_config` does.
    let node_pcs = get_pcs_config(level1_pp.trace_log_size, LOG_BLOWUP_FACTOR);
    let node_shared_config = shared_config_for_leaf(&level1_pp, node_pcs);
    let node_pp = node_preprocessed_from_shared(&node_shared_config, node_target.clone(), FOLD_ARITY);
    let node_preprocessed_root = preprocessed_root(&node_pp, LOG_BLOWUP_FACTOR);

    AggregateConfig {
        // Shared / R2 fields — real values (this is a genuinely decoupled R1 != R2
        // config; the R2 tier is real, so the R2 half of the consistency check is exercised too).
        node_shared_config,
        node_preprocessed_root,
        node_target_padding_sizes: node_target,
        node_pcs_config: node_pcs,
        fold_arity: FOLD_ARITY,
        // LeafR1R2 extras — the tier under test.
        leaf_shared_config: Some(leaf_shared_config),
        level1_preprocessed_root: Some(level1_preprocessed_root),
        leaf_preprocessed_root: Some(leaf_preprocessed_root),
        leaf_target_padding_sizes: Some(leaf_target),
        leaf_pcs_config: Some(pcs),
        // No precomputes: this test builds preprocessed circuits only, never proves. The precompute
        // fields now live on a separate `RecursionPrecompute` (unused here).
    }
}

/// In a genuinely decoupled config (R1 != R2), the trusted full-`FOLD_ARITY` roots the unpacker binds
/// to must equal the witness-independent recompute path used for short nodes / the root.
#[test]
#[ignore = "builds several 2^22-padded node preprocessed circuits (~minutes, CPU-only, no prove); \
            run with: cargo test -p recursive-aggregate --test decoupled_roots_consistent -- \
            --ignored --nocapture"]
fn full_arity_roots_consistent_in_decoupled_regime() {
    // RUN-GUARD (in addition to #[ignore]): builds several 2^22-padded node preprocessed circuits.
    if std::env::var("HEAVY_RECURSION").is_err() {
        eprintln!(
            "full_arity_roots_consistent_in_decoupled_regime: SKIPPED. Set \
             HEAVY_RECURSION=1 (and --ignored) to run."
        );
        return;
    }
    let config = build_decoupled_config();

    // MUST be the decoupled regime — a collapsed R1 == R2 config is exactly what hid the original
    // carry bug, so fail loudly if it ever collapses here.
    let r1 = config
        .level1_preprocessed_root
        .clone()
        .expect("decoupled config carries R1 (LeafR1R2 tier)");
    let r2 = config.node_preprocessed_root.clone();
    println!("R1 (level1/leaf-verifying) = {:?}", hv(&r1));
    println!("R2 (node-verifying)        = {:?}", hv(&r2));
    assert_ne!(
        r1, r2,
        "test config collapsed to R1 == R2 — NOT the decoupled regime; the check would be vacuous"
    );
    println!("DECOUPLED regime confirmed: R1 != R2");

    // The check under test: the config's production-built R1/R2 equal the unpacker's
    // witness-independent full-arity recompute (`short_node_preprocessed_root(FOLD_ARITY)`).
    config.assert_full_arity_roots_consistent();
    println!("assert_full_arity_roots_consistent PASSED at full arity in the decoupled regime");
}

/// Renders a `HashValue<QM31>`'s eight words for printing.
fn hv(h: &HashValue<QM31>) -> [u32; 8] {
    std::array::from_fn(|i| {
        let [lo, hi, 0, 0] = h[i].get().to_m31_array().map(|m| m.0) else {
            return 0;
        };
        lo | (hi << 16)
    })
}
