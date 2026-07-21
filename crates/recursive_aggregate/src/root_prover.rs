//! Root verification / unpacker: build and prove the published, zk-blinded root-verification proof —
//! verify the root multiverifier proof in-circuit, then unpack it (reconstruct + bind the tree root
//! from per-leaf output hints, emit the leaf outputs). See the crate root for the unpack contract.

use crate::{
    AggregateConfig, TreeProof, level0_group_sizes, preprocessed_root, reported_root,
};

use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_common::N_RESERVED;
use circuit_common::finalize::{add_zk_blinding, pad_context};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::SharedConfig;
use circuit_prover::prover::{
    prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
};
use circuit_verifier::statement::CircuitStatement;
use circuit_verifier::verify::{CircuitConfig, CircuitPublicData, verify_circuit};
use circuits::blake::{HashValue, blake2s_u32s, unpack_qm31s_to_u32_words};
use circuits::wrappers::U32Wrapper;
use circuits::context::{Context, FinalizedContext, Var};
use circuits::ivalue::{IValue, NoValue};
use circuits::ops::{Guess, eq};
use circuits_stark_verifier::proof::{Proof, empty_proof};
use circuits_stark_verifier::verify::verify;
use num_traits::Zero;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;

/// The bottom-level input to the unpacker: the ordered standalone leaves.
pub struct LeafBottom {
    /// The standalone leaves in canonical order (leaf `i` is shard `i`).
    pub leaves: Vec<TreeProof>,
}

/// The published root-verification proof.
pub struct RootVerificationOutput {
    /// The root verification's STARK proof — the single public artifact of the whole aggregation.
    pub proof: Proof<QM31>,
    /// The unpacked leaf outputs, in tree-position order — the result the proof exposes.
    pub leaf_outputs: Vec<[QM31; N_RESERVED]>,
    /// The root-verification circuit's trace log size (from which its PCS config was derived).
    pub trace_log_size: u32,
}

/// zk-blinding parameters for the root verification (the only blinded proof).
#[derive(Clone, Copy)]
pub struct ZkBlind {
    /// Seed for the ChaCha20 RNG that draws the blinding values.
    pub seed: [u8; 32],
    /// Blinding rows per witness component — must be the root proof's `n_queries`.
    pub n_padding: usize,
}

/// Recomputes the canonical unpacker preprocessed root for the trusted public `(n, config)`,
/// witness-independently — the value the trusted final verifier checks `rv.proof` against. Rebuilds
/// the SAME circuit via the shared [`build_root_verification_context`] with a `NoValue` witness, so it
/// equals the published proof's root by construction.
///
/// The caller must pass a `config` whose child roots are the canonical (trusted) values derived from
/// public `(n, config)`, never from the prover. `zk_n_padding` must equal the prover's blinding
/// `n_padding` (`None` = no blinding).
pub fn unpacker_preprocessed_root(
    n: usize,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_n_padding: Option<usize>,
) -> HashValue<QM31> {
    // The root node's own preprocessed root is guessed (a witness), so a placeholder suffices here.
    let root_pp = HashValue::from([0u32; N_RESERVED]);
    let zk_blind = zk_n_padding.map(|n_padding| ZkBlind { seed: [0u8; 32], n_padding });
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
    preprocessed_root(&preprocessed, log_blowup_factor)
}

/// Recomputes the full [`CircuitConfig`] the trusted final verifier uses to `verify_circuit` the
/// published root-verification proof, from trusted public `(n, config)` via the same shared builder.
/// `preprocessed_root` is the canonical unpacker root (the pin — a forged reconstruction yields a
/// different root ⇒ rejected); the rest is the recomputed trace's own shape. See
/// [`unpacker_preprocessed_root`] for the trust contract.
pub fn unpacker_verify_config(
    n: usize,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_n_padding: Option<usize>,
) -> CircuitConfig {
    let root_pp = HashValue::from([0u32; N_RESERVED]);
    let zk_blind = zk_n_padding.map(|n_padding| ZkBlind { seed: [0u8; 32], n_padding });
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

/// Builds and proves the root verification — the only published, only zk-blinded proof — for the
/// standalone-leaf topology, via the shared [`build_root_verification_context`].
/// `bottom.leaves` must be the same ordered leaves fed to
/// [`crate::prove::recursive_aggregate_prove_leaves`], and `root` its returned root.
pub fn prove_root_verification_leaves(
    root: &TreeProof,
    bottom: &LeafBottom,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_blind: Option<ZkBlind>,
) -> RootVerificationOutput {
    let leaves = &bottom.leaves;
    let n = leaves.len();
    assert!(!leaves.is_empty(), "need at least one leaf");

    let leaf_output_values: Vec<[QM31; N_RESERVED]> =
        leaves.iter().map(|l| l.output_values).collect();
    let mut context = build_root_verification_context::<QM31>(
        root.proof.clone(),
        &root.output_values,
        &root.preprocessed_root,
        &leaf_output_values,
        n,
        config,
        zk_blind,
    );
    // Correctness tripwire (QM31 prove pass only; the shared builder skips it for the NoValue recompute).
    context.validate_circuit();

    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let trace_log_size = preprocessed.trace_log_size;
    let pcs_config = get_pcs_config(trace_log_size, log_blowup_factor);
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
        pcs_config,
    )
    .expect("root-verification prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let verify_config = CircuitConfig {
        config: pcs_config,
        n_outputs: n * N_RESERVED,
        preprocessed_column_log_sizes: preprocessed.preprocessed_trace.log_sizes(),
        preprocessed_root: preprocessed_root(&preprocessed, log_blowup_factor),
    };
    verify_circuit(
        verify_config,
        proof.clone(),
        CircuitPublicData { output_values: public_data.output_values },
    )
    .expect("root-verification proof failed to verify (final-proof sanity check)");

    RootVerificationOutput {
        proof,
        leaf_outputs: leaves.iter().map(|l| l.output_values).collect(),
        trace_log_size,
    }
}

/// Bakes a canonical preprocessed root into the circuit as eight `context.constant` wires, usable
/// exactly where a guessed root was. SOUNDNESS: a constant is FIXED circuit data (hashed into the
/// preprocessed output), so a forged value can only miss the trusted verifier's root check — it cannot
/// be substituted the way a guessed witness could. Identical constants in both the QM31 prove and
/// NoValue recompute passes ⇒ identical preprocessed traces.
fn constant_pp<Value: IValue>(
    context: &mut Context<Value>,
    pp: &HashValue<QM31>,
) -> HashValue<Var> {
    HashValue(std::array::from_fn(|i| {
        U32Wrapper::new_unsafe(context.constant(*pp[i].get()))
    }))
}

/// The `SharedConfig` used to verify the ROOT proof — the single `n == 1` selector shared by the QM31
/// prove pass and the NoValue recompute so both build the identical shape. N≥2 ⇒ a genuine
/// level1-/fold-node (`fold_shared_config`); N==1 ⇒ the root IS the lone leaf (proved with the
/// LEAF config).
fn root_verification_shared_config(n: usize, config: &AggregateConfig) -> &SharedConfig {
    if n == 1 {
        &config.leaf_shared_config
    } else {
        &config.fold_shared_config
    }
}

/// The `PcsConfig` used to verify the ROOT proof (leaf lifting for the N==1 lone-leaf root — so the
/// in-circuit Merkle auth-path height matches how it was proved — node lifting otherwise). Mirrors
/// [`root_verification_shared_config`]'s `n == 1` selection.
fn root_verification_pcs_config(n: usize, config: &AggregateConfig) -> PcsConfig {
    if n == 1 {
        config.leaf_pcs_config
    } else {
        config.node_pcs_config
    }
}

/// Builds the root-verification unpacker circuit, generic over `Value` — the SINGLE code path shared
/// by the QM31 prove ([`prove_root_verification_leaves`]) and the NoValue canonical-root recompute the
/// trusted verifier runs. Sharing one builder is what guarantees the recomputed preprocessed root
/// equals the published proof's (identical structure, baked constants, blinding).
///
/// `root_proof` / `leaf_output_values` carry the witness; `root_output_values` and every preprocessed
/// root are QM31 constants independent of `Value`. Every child preprocessed root is a canonical
/// config-derived value BAKED as a constant ([`constant_pp`]), pinning the whole reconstructed fold.
fn build_root_verification_context<Value: IValue>(
    root_proof: Proof<Value>,
    root_output_values: &[QM31],
    root_preprocessed_root: &HashValue<QM31>,
    leaf_output_values: &[[Value; N_RESERVED]],
    n: usize,
    config: &AggregateConfig,
    zk_blind: Option<ZkBlind>,
) -> FinalizedContext<Value> {
    assert!(n >= 1, "need at least one leaf");
    assert_eq!(leaf_output_values.len(), n, "leaf_output_values count must equal n");
    let leaf_preprocessed_root = config.leaf_preprocessed_root.clone();
    let k = config.fold_arity;

    let mut context = Context::<Value>::new(n * N_RESERVED);

    // (1) Verify the root multiverifier proof in-circuit, using the `n == 1` config/PCS selectors
    // (leaf for a lone-leaf root, node otherwise) — the same selectors the NoValue recompute uses.
    let root_shared_config = root_verification_shared_config(n, config);
    let root_pcs_config = root_verification_pcs_config(n, config);
    let circuit_config = CircuitConfig {
        config: root_pcs_config,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: root_shared_config
            .preprocessed_column_log_sizes
            .clone(),
        preprocessed_root: root_preprocessed_root.clone(),
    };
    let statement = CircuitStatement::new(&mut context, &circuit_config, root_output_values);
    let proof_vars = root_proof.guess(&mut context);
    verify(
        &mut context,
        &proof_vars,
        &root_shared_config.proof_config,
        &statement,
    );
    let root_out_vars: Vec<Var> = statement.get_output_values().to_vec();

    // (2) Unpack: reconstruct the tree root from the guessed per-leaf outputs and bind it. Every child
    // root is BAKED as a `constant_pp` (soundness-pinned), not guessed. One trusted leaf tree0 root
    // for EVERY leaf (forces a shared leaf AIR).
    let leaf_pp = constant_pp(&mut context, &leaf_preprocessed_root);
    let mut leaf_output_vars: Vec<Vec<Var>> = Vec::with_capacity(n);
    // Per-leaf entries (height 0), each carrying `leaf_pp` and its guessed outputs.
    let mut leaf_entries: Vec<(usize, HashValue<Var>, Vec<Var>)> = leaf_output_values
        .iter()
        .map(|outs| {
            let outs: Vec<Var> = outs.iter().map(|v| v.guess(&mut context)).collect();
            leaf_output_vars.push(outs.clone());
            (0usize, leaf_pp.clone(), outs)
        })
        .collect();

    // Bottom (level 0): consume ALL leaves into height-1 leaf-nodes (n == 1 ⇒ the lone leaf is the root).
    let mut level: Vec<(usize, HashValue<Var>, Vec<Var>)> = if n == 1 {
        leaf_entries
    } else {
        let sizes = level0_group_sizes(n, k);
        let mut leaves_iter = leaf_entries.drain(..);
        let level0: Vec<(usize, HashValue<Var>, Vec<Var>)> = sizes
            .iter()
            .map(|&m| {
                let group: Vec<(usize, HashValue<Var>, Vec<Var>)> =
                    (0..m).map(|_| leaves_iter.next().unwrap()).collect();
                fold_group(&mut context, &group, config)
            })
            .collect();
        drop(leaves_iter);
        level0
    };

    // Levels ≥ 1: shared group+carry over nodes.
    while level.len() > 1 {
        if level.len() <= k {
            let root = fold_group(&mut context, &level, config);
            level = vec![root];
            break;
        }
        let remainder = level.len() % k;
        let carry: Vec<(usize, HashValue<Var>, Vec<Var>)> =
            level.split_off(level.len() - remainder);
        let mut next = Vec::with_capacity(level.len() / k + remainder);
        for group in level.chunks(k) {
            next.push(fold_group(&mut context, group, config));
        }
        next.extend(carry);
        level = next;
    }
    // Bind the reconstructed root's eight digest words to the verified root's eight output words.
    let computed_root = &level[0].2;
    for i in 0..N_RESERVED {
        eq(&mut context, computed_root[i], root_out_vars[i]);
    }

    // (3) Emit the unpacked per-leaf outputs as public outputs.
    let flat_outputs: Vec<Var> = leaf_output_vars.iter().flatten().copied().collect();
    context.set_outputs(&flat_outputs);

    // (4) Finalize, (optionally) blind, pad. No `validate_circuit` here (generic over `Value`; the
    //     QM31 prove path validates the returned context itself).
    let mut context = context.finalize(false);
    if let Some(zk) = zk_blind {
        add_zk_blinding(&mut context, zk.seed, zk.n_padding);
    }
    pad_context(&mut context);
    context
}

/// Shared child-preimage hash for one ordered group — matches the in-circuit node hash in
/// `build_multiverifier_circuit`.
fn fold_hash<Value: IValue>(
    context: &mut Context<Value>,
    group: &[(usize, HashValue<Var>, Vec<Var>)],
) -> Vec<Var> {
    let mut preimage: Vec<U32Wrapper<Var>> = Vec::new();
    for (_, pp, outs) in group {
        let output_words = unpack_qm31s_to_u32_words(context, outs.iter().copied());
        preimage.extend(pp.iter().copied().chain(output_words));
    }
    let n_bytes = 4 * preimage.len();
    let h = blake2s_u32s(context, preimage, n_bytes);
    h.iter().map(|w| *w.get()).collect()
}

/// Folds one ordered group into a node, baking the same preprocessed root the prover reported (via
/// [`reported_root`]). Since it is pinned, a wrong reconstruction can only miss the verified root ⇒
/// rejected, never accepted-invalid.
fn fold_group<Value: IValue>(
    context: &mut Context<Value>,
    group: &[(usize, HashValue<Var>, Vec<Var>)],
    config: &AggregateConfig,
) -> (usize, HashValue<Var>, Vec<Var>) {
    let outs = fold_hash(context, group);
    let height = group.iter().map(|(h, _, _)| *h).max().unwrap() + 1;
    let node_pp = constant_pp(context, &reported_root(config, height, group.len()));
    (height, node_pp, outs)
}
