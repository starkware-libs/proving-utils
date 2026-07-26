//! Capture / drift DERIVATION. Feature-gated (`test-utils`) so a dependent crate's tests can reach
//! it. One fresh-cascade derivation ([`derive_configs`]) feeds both capture (raw) and drift
//! ([`check_configs`], per-field `assert_eq`); the const-friendly pinned twin
//! (`DerivedConfigs`/`PinnedConfigs`) + assembler live in `crate::pinned_configs`.

use crate::pinned_configs::{DerivedConfigs, RecursionConfig, assemble_aggregate_config};
use crate::precomputes::node_preprocessed_from_shared;
use crate::root_prover::{
    ZkBlind, build_root_verification_context, root_verification_shared_config,
};
use crate::{AggregateConfig, shared_config_from_circuit_config};

use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_common::N_RESERVED;
use circuit_common::finalize::{ComponentSizes, compute_padded_sizes, pad_to_targets};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_verifier::verify::CircuitConfig;
use circuits::blake::HashValue;
use circuits::ivalue::NoValue;
use circuits_stark_verifier::order_hash_map::OrderedHashMap;
use circuits_stark_verifier::proof::empty_proof;
use num_traits::Zero;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::circle::PolyOps;

/// Derives fresh via [`derive_configs`] and compares per-field / per-arity against `expected`,
/// panicking with a labelled `assert_eq` on drift (e.g. `"level1[3] config drift"`). Replaces the
/// old per-layer `check_*_config`.
pub fn check_configs(leaf_pp: &PreprocessedCircuit, leaf_pcs: PcsConfig, config: &RecursionConfig) {
    let expected = config.to_derived(config.leaf_log_blowup, config.recursion_log_blowup);
    let real = derive_configs(
        leaf_pp,
        leaf_pcs,
        config.leaf_log_blowup,
        config.recursion_log_blowup,
        config.fold_arity,
        config.n_leaves,
    );
    assert_eq!(real.leaf, expected.leaf, "leaf config drift");
    assert_eq!(real.node_target, expected.node_target, "node_target drift");
    assert_eq!(
        real.level1.len(),
        expected.level1.len(),
        "level1 arity count drift"
    );
    for (i, (r, e)) in real.level1.iter().zip(&expected.level1).enumerate() {
        assert_eq!(r, e, "level1[{}] config drift", i + 2);
    }
    assert_eq!(
        real.fold.len(),
        expected.fold.len(),
        "fold arity count drift"
    );
    for (i, (r, e)) in real.fold.iter().zip(&expected.fold).enumerate() {
        assert_eq!(r, e, "fold[{}] config drift", i + 2);
    }
    assert_eq!(real.unpacker, expected.unpacker, "unpacker config drift");
}

/// Single-point capture: derives the fresh cascade for one operating point and emits every `@@`
/// line `gen_recursion_consts.py` parses. Relocated from gate_air's `capture_all` so the derived
/// config type + derivation stay crate-internal; the AIR-specific leaf build + `@@POINT`/
/// `@@CAPTURE_DONE` framing stay at the call site.
pub fn capture_point(
    leaf_pp: &PreprocessedCircuit,
    leaf_pcs: PcsConfig,
    leaf_blowup: u32,
    node_blowup: u32,
    fold_arity: usize,
    n: usize,
) {
    let derived = derive_configs(leaf_pp, leaf_pcs, leaf_blowup, node_blowup, fold_arity, n);
    emit_captured_point(&derived, node_blowup);
}

/// The single fresh-cascade derivation, AIR-agnostic: the caller builds the AIR-specific leaf
/// preprocessed circuit and passes it in; this derives everything downstream (node_target fixed
/// point, per-arity level1/fold configs, the per-N unpacker) and returns every derived config. NO
/// asserts — pure derivation, so `capture_all` (no pinned to compare) reuses it.
///
/// `leaf_blowup`/`node_blowup` are the leaf-wrap / node FRI blowups (decoupled); `fold_arity` the
/// node arity `k`; `n` the leaf count (for the unpacker).
pub(crate) fn derive_configs(
    leaf_pp: &PreprocessedCircuit,
    leaf_pcs: PcsConfig,
    leaf_blowup: u32,
    node_blowup: u32,
    fold_arity: usize,
    n: usize,
) -> DerivedConfigs {
    assert!(fold_arity >= 2, "fold_arity k must be >= 2");
    let leaf = leaf_circuit_config(leaf_pp, leaf_pcs, leaf_blowup);

    // Node-size fixed point over the two full-`fold_arity` variants (level1 verifies leaves, fold
    // verifies nodes), both padded to a COMMON `node_target`. Matches `derive_aggregate_config`.
    let node_target = node_target_fixed_point(leaf_pp, leaf_pcs, fold_arity, node_blowup);

    // Per-arity level1 (child = fresh leaf config) + fold (child = fresh level1[k] config) configs,
    // recomputed from the leaf/level1 configs against the common `node_target`.
    let (level1_k, _) = recompute_node(&leaf, fold_arity, node_target.clone(), node_blowup);
    let level1 = node_configs(&leaf, &node_target, fold_arity, node_blowup);
    let fold = node_configs(&level1_k, &node_target, fold_arity, node_blowup);

    // Unpacker: from the assembled `AggregateConfig` (real child roots baked). Build a partial
    // `DerivedConfigs` (unpacker filled last) to reuse the shared assembler; `leaf_target` is inert
    // for the unpacker path so a zeroed one suffices here.
    let mut derived = DerivedConfigs {
        leaf,
        node_target,
        level1,
        fold,
        unpacker: placeholder_circuit_config(),
    };
    let config = assemble_aggregate_config(&derived, zero_sizes(), fold_arity);
    let n_queries = config.node_pcs_config.fri_config.n_queries;
    derived.unpacker = derive_unpacker_config(n, &config, node_blowup, Some(n_queries));
    derived
}

/// Merkle root of a circuit's preprocessed trace — used to regenerate/check the pinned root table.
pub(crate) fn preprocessed_root(
    preprocessed: &PreprocessedCircuit,
    log_blowup_factor: u32,
) -> HashValue<QM31> {
    let lifting_log_size = preprocessed.trace_log_size + log_blowup_factor;
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(lifting_log_size)
            .circle_domain()
            .half_coset,
    );
    let trace = preprocessed.preprocessed_trace.get_trace::<SimdBackend>();
    let polys = SimdBackend::interpolate_columns(trace, &twiddles);
    let tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        polys,
        log_blowup_factor,
        &twiddles,
        true,
        Some(lifting_log_size),
        &BaseColumnPool::<SimdBackend>::new(),
    );
    tree.commitment.root().into()
}

/// Recomputes the full [`CircuitConfig`] a trusted final verifier would use to `verify_circuit` the
/// published root-verification proof, from public `(n, config)` via the same shared builder
/// (NoValue witness), so it is byte-identical to the honest proof's preprocessed shape. Its
/// `preprocessed_root` is the canonical unpacker root. `zk_n_padding` must equal the prover's
/// blinding `n_padding` (`None` = no blinding).
pub(crate) fn derive_unpacker_config(
    n: usize,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_n_padding: Option<usize>,
) -> CircuitConfig {
    let root_pp = HashValue::from([0u32; N_RESERVED]);
    let zk_blind = zk_n_padding.map(|n_padding| ZkBlind {
        seed: [0u8; 32],
        n_padding,
    });
    let root_output_values = [QM31::zero(); N_RESERVED];
    let leaf_output_values = vec![[NoValue; N_RESERVED]; n];
    let mut context = build_root_verification_context::<NoValue>(
        empty_proof(&root_verification_shared_config(n, config).proof_config),
        &root_output_values,
        &root_pp,
        &leaf_output_values,
        n,
        config,
        zk_blind,
    );
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let trace_log_size = preprocessed.trace_log_size;
    CircuitConfig {
        config: get_pcs_config(trace_log_size, log_blowup_factor),
        n_outputs: n * N_RESERVED,
        preprocessed_column_log_sizes: preprocessed.preprocessed_trace.log_sizes(),
        preprocessed_root: preprocessed_root(&preprocessed, log_blowup_factor),
    }
}

/// Emits every `@@` line for one point's [`DerivedConfigs`] (leaf shape/root, node_target,
/// per-arity level1/fold shape+roots, the unpacker) — the format `gen_recursion_consts.py` parses.
/// The layer shape (`@@{tag}_TRACE`/`@@{tag}_COLS`) is emitted once per node layer (arity 2), roots
/// per arity.
fn emit_captured_point(d: &DerivedConfigs, node_blowup: u32) {
    let leaf_root = HashValue::from(hv_words(&d.leaf.preprocessed_root));
    emit_layer("LEAF", trace_of(&d.leaf, node_blowup), &d.leaf);
    emit_root("LEAF_ROOT", &leaf_root);

    let nt = &d.node_target;
    println!(
        "@@NODE_TARGET {} {} {} {} {}",
        nt.eq, nt.qm31_ops, nt.m31_to_u32, nt.triple_xor, nt.blake_g_gate
    );

    for (tag, layer) in [("LEVEL1", &d.level1), ("FOLD", &d.fold)] {
        for (i, cfg) in layer.iter().enumerate() {
            let arity = i + 2;
            if arity == 2 {
                emit_layer(tag, trace_of(cfg, node_blowup), cfg);
            }
            emit_root(&format!("{tag}_ROOT_{arity}"), &cfg.preprocessed_root);
        }
    }

    let u = &d.unpacker;
    let p = &u.config;
    println!(
        "@@UNPACKER_PCS {} {} {} {} {} {}",
        p.pow_bits,
        p.fri_config.log_blowup_factor,
        p.fri_config.log_last_layer_degree_bound,
        p.fri_config.n_queries,
        p.fri_config.fold_step,
        p.lifting_log_size.expect("unpacker lifting"),
    );
    println!("@@UNPACKER_NOUT {}", u.n_outputs);
    println!("@@UNPACKER_COLS {}", cols_str(u));
    emit_root("UNPACKER_ROOT", &u.preprocessed_root);
}

/// A config's trace log-size = its PCS lifting minus the FRI blowup.
fn trace_of(cfg: &CircuitConfig, blowup: u32) -> u32 {
    cfg.config.lifting_log_size.expect("lifting") - blowup
}

/// Emits a layer's `@@{tag}_TRACE` + `@@{tag}_COLS` lines for the fill generator.
fn emit_layer(tag: &str, trace_log_size: u32, cfg: &CircuitConfig) {
    println!("@@{tag}_TRACE {trace_log_size}");
    println!("@@{tag}_COLS {}", cols_str(cfg));
}

/// Space-separated `id:log_size` preprocessed-column pairs, in canonical committed order.
fn cols_str(cfg: &CircuitConfig) -> String {
    cfg.preprocessed_column_log_sizes
        .iter()
        .map(|(id, ls)| format!("{}:{}", id.id, ls))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Emits `@@{tag} w0 w1 .. w7` for an eight-word root.
fn emit_root(tag: &str, root: &HashValue<QM31>) {
    let words: Vec<String> = hv_words(root).iter().map(|w| w.to_string()).collect();
    println!("@@{tag} {}", words.join(" "));
}

/// Renders a `HashValue<QM31>`'s eight raw words for a paste-able `[u32; 8]` literal.
fn hv_words(h: &HashValue<QM31>) -> [u32; 8] {
    std::array::from_fn(|i| {
        let [lo, hi, 0, 0] = h[i].get().to_m31_array().map(|m| m.0) else {
            return 0;
        };
        lo | (hi << 16)
    })
}

/// An empty [`CircuitConfig`] placeholder for the unpacker slot while assembling the intermediate
/// `AggregateConfig` (which never reads it).
fn placeholder_circuit_config() -> CircuitConfig {
    CircuitConfig {
        config: get_pcs_config(1, 1),
        n_outputs: 0,
        preprocessed_column_log_sizes: OrderedHashMap::default(),
        preprocessed_root: HashValue::from([0u32; 8]),
    }
}

/// All-zero `ComponentSizes` — an inert `leaf_target` for an `AggregateConfig` used only by the
/// unpacker derivation (which does not read `leaf_target_padding_sizes`).
fn zero_sizes() -> ComponentSizes {
    ComponentSizes {
        eq: 0,
        qm31_ops: 0,
        m31_to_u32: 0,
        triple_xor: 0,
        blake_g_gate: 0,
    }
}

/// The leaf verifier [`CircuitConfig`] from its preprocessed circuit.
fn leaf_circuit_config(
    leaf_pp: &PreprocessedCircuit,
    leaf_pcs: PcsConfig,
    leaf_blowup: u32,
) -> CircuitConfig {
    CircuitConfig {
        config: leaf_pcs,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: leaf_pp.preprocessed_trace.log_sizes(),
        preprocessed_root: preprocessed_root(leaf_pp, leaf_blowup),
    }
}

/// The per-arity (`2..=fold_arity`, index `arity - 2`) node [`CircuitConfig`]s recomputed from
/// `child` against `node_target`.
fn node_configs(
    child: &CircuitConfig,
    node_target: &ComponentSizes,
    fold_arity: usize,
    node_blowup: u32,
) -> Vec<CircuitConfig> {
    (2..=fold_arity)
        .map(|arity| recompute_node(child, arity, node_target.clone(), node_blowup).0)
        .collect()
}

/// The node-target fixed point (the common padding target every level1/fold node pads to), matching
/// `derive_aggregate_config`'s loop: seed from the level1 variant's unpadded sizes, then join
/// level1 (leaf child) and fold (node child) unpadded sizes until stable.
fn node_target_fixed_point(
    leaf_pp: &PreprocessedCircuit,
    leaf_pcs: PcsConfig,
    fold_arity: usize,
    node_blowup: u32,
) -> ComponentSizes {
    let (_, node1_seed_sizes) =
        multiverifier_node_preprocessed(leaf_pp, leaf_pcs, None, fold_arity);
    let mut node_target = node1_seed_sizes;
    loop {
        let (level1_pp, level1_unpadded) = multiverifier_node_preprocessed(
            leaf_pp,
            leaf_pcs,
            Some(node_target.clone()),
            fold_arity,
        );
        let node_child_pcs = get_pcs_config(level1_pp.trace_log_size, node_blowup);
        let (_node_pp, node2_unpadded) = multiverifier_node_preprocessed(
            &level1_pp,
            node_child_pcs,
            Some(node_target.clone()),
            fold_arity,
        );
        let new_target = max_sizes(&level1_unpadded, &node2_unpadded);
        if new_target == node_target {
            break;
        }
        node_target = new_target;
    }
    node_target
}

/// Elementwise max of two `ComponentSizes` — the node-target fixed-point join.
fn max_sizes(a: &ComponentSizes, b: &ComponentSizes) -> ComponentSizes {
    ComponentSizes {
        eq: a.eq.max(b.eq),
        qm31_ops: a.qm31_ops.max(b.qm31_ops),
        m31_to_u32: a.m31_to_u32.max(b.m31_to_u32),
        triple_xor: a.triple_xor.max(b.triple_xor),
        blake_g_gate: a.blake_g_gate.max(b.blake_g_gate),
    }
}

/// Recompute a fold-node's [`CircuitConfig`] + preprocessed root from its CHILD config, `arity`,
/// the common `node_target`, and the node FRI blowup. AIR-agnostic — the caller passes the child
/// config (a leaf config for a level-1 node, a level-1 node config for a fold node).
fn recompute_node(
    child_config: &CircuitConfig,
    arity: usize,
    node_target: ComponentSizes,
    node_log_blowup: u32,
) -> (CircuitConfig, HashValue<QM31>) {
    let child_shared = shared_config_from_circuit_config(child_config);
    let node_pp = node_preprocessed_from_shared(&child_shared, node_target, arity);
    let root = preprocessed_root(&node_pp, node_log_blowup);
    let config = CircuitConfig {
        config: get_pcs_config(node_pp.trace_log_size, node_log_blowup),
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: node_pp.preprocessed_trace.log_sizes(),
        preprocessed_root: root.clone(),
    };
    (config, root)
}

/// Builds + preprocesses the NoValue node verifying children of `leaf_preprocessed`'s config
/// (optionally padded), to recompute the node's `preprocessed_root`. Also returns the node's
/// UNPADDED component sizes (for deriving the shared `node_target = max(level1, node)`).
fn multiverifier_node_preprocessed(
    leaf_preprocessed: &PreprocessedCircuit,
    pcs_config: PcsConfig,
    target_padding: Option<ComponentSizes>,
    fold_arity: usize,
) -> (PreprocessedCircuit, ComponentSizes) {
    let proof_config = crate::precomputes::noval_node_proof_config(
        leaf_preprocessed.preprocessed_trace.n_columns(),
        &pcs_config,
    );
    let shared = SharedConfig {
        pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: leaf_preprocessed.preprocessed_trace.log_sizes(),
    };
    let inputs: Vec<MultiverifierInput<NoValue>> = (0..fold_arity)
        .map(|_| crate::precomputes::empty_node_input(&proof_config))
        .collect();
    let mut ctx = build_multiverifier_circuit::<NoValue>(inputs, &shared);
    let unpadded_sizes = compute_padded_sizes(&ctx);
    if let Some(t) = target_padding {
        pad_to_targets(&mut ctx, t);
    }
    (
        PreprocessedCircuit::preprocess_circuit(&mut ctx),
        unpadded_sizes,
    )
}
