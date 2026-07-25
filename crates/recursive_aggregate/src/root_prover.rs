//! Root verification / unpacker: build and prove the published, zk-blinded root-verification proof
//! — verify the root multiverifier proof in-circuit, then unpack it (reconstruct + bind the tree
//! root from per-leaf output hints, emit the leaf outputs). See the crate root for the unpack
//! contract.

use crate::precomputes::{RecursionPrecompute, build_one_shot_tree};
use crate::{AggregateConfig, NodeKind, TreeProof, level0_group_sizes, reported_root};

use circuit_common::N_RESERVED;
use circuit_common::finalize::{add_zk_blinding, pad_context};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::SharedConfig;
use circuit_prover::prover::{
    prepare_circuit_proof_for_circuit_verifier, prove_circuit_with_precompute,
};
use circuit_verifier::circuit_hash::compute_circuit_hash;
use circuit_verifier::statement::{
    CircuitStatement, all_circuit_components, circuit_component_log_sizes,
};
use circuit_verifier::verify::{CircuitConfig, CircuitPublicData, verify_circuit};
use circuits::blake::{HashValue, blake2s_u32s};
use circuits::context::{Context, FinalizedContext, Var};
use circuits::ivalue::IValue;
use circuits::ops::{Guess, eq};
use circuits::wrappers::U32Wrapper;
use circuits_stark_verifier::proof::Proof;
use circuits_stark_verifier::verify::verify;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;

/// The bottom-level input to the unpacker: the ordered standalone leaves.
pub struct LeafBottom {
    /// The standalone leaves in canonical order (leaf `i` is shard `i`).
    pub leaves: Vec<TreeProof>,
}

/// The published root-verification proof.
pub struct RootVerificationOutput {
    /// The root verification's STARK proof — the single public artifact of the whole aggregation.
    pub proof: Proof<QM31>,
    /// The unpacked leaf outputs, in tree-position order — the result the proof exposes. Each is the
    /// leaf circuit's `N_RESERVED` raw digest words.
    pub leaf_outputs: Vec<[u32; N_RESERVED]>,
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

/// Builds and proves the root verification — the only published, only zk-blinded proof — for the
/// standalone-leaf topology, via the shared [`build_root_verification_context`]. `bottom.leaves`
/// must be the same ordered leaves fed to [`crate::prove::recursive_aggregate_prove_leaves`], and
/// `root` its returned root.
///
/// `unpacker_config` is the pinned per-N unpacker [`CircuitConfig`] the caller supplies: its
/// `preprocessed_root` is the trusted canonical unpacker root and its `config` the trusted PCS. The
/// per-run unpacker tree is a ONE-SHOT built here by the shared tree-builder, asserting the
/// committed root equals that pinned root (so a shape mismatch aborts before proving). `zk_blind`
/// must match the blinding baked into the pinned config (`None` = no blinding).
pub fn prove_root_verification_leaves(
    root: &TreeProof,
    bottom: &LeafBottom,
    pre: &RecursionPrecompute,
    unpacker_config: &CircuitConfig,
    zk_blind: Option<ZkBlind>,
) -> RootVerificationOutput {
    let config = &pre.aggregate_config;
    let leaves = &bottom.leaves;
    let n = leaves.len();
    assert!(!leaves.is_empty(), "need at least one leaf");

    let leaf_output_values: Vec<[u32; N_RESERVED]> =
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
    // Correctness tripwire (QM31 prove pass only; the shared builder skips it for the NoValue
    // recompute).
    context.validate_circuit();

    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let trace_log_size = preprocessed.trace_log_size;
    // One-shot unpacker tree via the shared builder; asserts the committed root == the pinned root.
    let (tree, twiddles, pool) = build_one_shot_tree(
        preprocessed,
        unpacker_config.config,
        unpacker_config.preprocessed_root.clone(),
    );
    let circuit_proof = prove_circuit_with_precompute::<Blake2sM31MerkleChannel>(
        &pool,
        &twiddles,
        &tree.preprocessed,
        MaybeOwned::Borrowed(&tree.tree),
        context.values(),
        tree.pcs_config,
    )
    .expect("root-verification prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    // Final-proof sanity check against the pinned unpacker config (its root == the one-shot
    // tree's).
    verify_circuit(
        CircuitConfig {
            config: tree.pcs_config,
            n_outputs: n * N_RESERVED,
            preprocessed_column_log_sizes: tree.preprocessed.preprocessed_trace.log_sizes(),
            preprocessed_root: unpacker_config.preprocessed_root.clone(),
        },
        proof.clone(),
        CircuitPublicData {
            output_values: public_data.output_values,
        },
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
/// preprocessed output), so a forged value can only miss the trusted verifier's root check — it
/// cannot be substituted the way a guessed witness could. Identical constants in both the QM31
/// prove and NoValue recompute passes ⇒ identical preprocessed traces.
fn constant_pp<Value: IValue>(
    context: &mut Context<Value>,
    pp: &HashValue<QM31>,
) -> HashValue<Var> {
    HashValue(std::array::from_fn(|i| {
        U32Wrapper::new_unsafe(context.constant(*pp[i].get()))
    }))
}

/// The `SharedConfig` used to verify the ROOT proof — the single `n == 1` selector shared by the
/// QM31 prove pass and the NoValue recompute so both build the identical shape. N≥2 ⇒ a genuine
/// level1-/fold-node (`fold_shared_config`); N==1 ⇒ the root IS the lone leaf (proved with the
/// LEAF config).
pub(crate) fn root_verification_shared_config(n: usize, config: &AggregateConfig) -> &SharedConfig {
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

/// Builds the root-verification unpacker circuit, generic over `Value` — the SINGLE code path
/// shared by the QM31 prove ([`prove_root_verification_leaves`]) and the NoValue canonical-root
/// recompute the trusted verifier runs. Sharing one builder is what guarantees the recomputed
/// preprocessed root equals the published proof's (identical structure, baked constants, blinding).
///
/// `root_proof` / `leaf_output_values` carry the witness; `root_output_values` and every
/// preprocessed root are QM31 constants independent of `Value`. Every child preprocessed root is a
/// canonical config-derived value BAKED as a constant ([`constant_pp`]), pinning the whole
/// reconstructed fold.
pub(crate) fn build_root_verification_context<Value: IValue>(
    root_proof: Proof<Value>,
    root_output_values: &[u32],
    root_preprocessed_root: &HashValue<QM31>,
    leaf_output_values: &[[u32; N_RESERVED]],
    n: usize,
    config: &AggregateConfig,
    zk_blind: Option<ZkBlind>,
) -> FinalizedContext<Value> {
    assert!(n >= 1, "need at least one leaf");
    assert_eq!(
        leaf_output_values.len(),
        n,
        "leaf_output_values count must equal n"
    );
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
        preprocessed_column_log_sizes: root_shared_config.preprocessed_column_log_sizes.clone(),
        preprocessed_root: root_preprocessed_root.clone(),
    };
    // `CircuitStatement::new` takes already-guessed output `Var`s. Guess each raw output word EXACTLY
    // as `build_multiverifier_circuit` does — `pack_u32`-embedded then `guess` — so the wires match.
    let root_output_vars: Vec<Var> = root_output_values
        .iter()
        .map(|word| *guess_output_word(&mut context, *word).get())
        .collect();
    let statement = CircuitStatement::new(&mut context, &circuit_config, &root_output_vars);
    let proof_vars = root_proof.guess(&mut context);
    verify(
        &mut context,
        &proof_vars,
        &root_shared_config.proof_config,
        &statement,
    );
    let root_out_vars: Vec<Var> = statement.output_values.clone();

    // (2) Unpack: reconstruct the tree root from the guessed per-leaf outputs and bind it. Every
    // child root is BAKED as a `constant_pp` (soundness-pinned), not guessed. One trusted leaf
    // tree0 root for EVERY leaf (forces a shared leaf AIR).
    let leaf_pp = constant_pp(&mut context, &leaf_preprocessed_root);
    let mut leaf_output_vars: Vec<Vec<Var>> = Vec::with_capacity(n);
    // Per-leaf entries (height 0), each carrying `leaf_pp` and its guessed outputs.
    let mut leaf_entries: Vec<(usize, HashValue<Var>, Vec<Var>)> = leaf_output_values
        .iter()
        .map(|outs| {
            // Guess each raw output word exactly as `build_multiverifier_circuit` does, so the
            // reconstructed fold preimage matches the multiverifier's byte-for-byte.
            let outs: Vec<Var> = outs
                .iter()
                .map(|word| *guess_output_word(&mut context, *word).get())
                .collect();
            leaf_output_vars.push(outs.clone());
            (0usize, leaf_pp.clone(), outs)
        })
        .collect();

    // Bottom (level 0): consume ALL leaves into height-1 leaf-nodes (n == 1 ⇒ the lone leaf is the
    // root).
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

/// Guesses one raw output word into the circuit EXACTLY as `build_multiverifier_circuit` does — a
/// `pack_u32`-embedded value fed through `guess` — so the reconstructed wires (and any hash preimage
/// built from them) are byte-identical to the multiverifier's.
fn guess_output_word<Value: IValue>(
    context: &mut Context<Value>,
    word: u32,
) -> U32Wrapper<Var> {
    U32Wrapper::new_unsafe(Value::pack_u32(word)).guess(context)
}

/// Per-child preimage hash for one ordered group, reproducing `build_multiverifier_circuit`'s node
/// hash byte-for-byte. For each child, left-to-right, the preimage is `[circuit_hash (8 words),
/// output words (one word per output)]`, where `circuit_hash` is the child's in-circuit hash
/// `blake2s(config_words || preprocessed_root)` computed with the PARENT node's child-verifier
/// `shared_config` (its component log sizes + FRI blowup) and the child's own `preprocessed_root`.
/// The whole concatenation is hashed with `blake2s_u32s`.
fn fold_hash<Value: IValue>(
    context: &mut Context<Value>,
    group: &[(usize, HashValue<Var>, Vec<Var>)],
    child_shared_config: &SharedConfig,
) -> Vec<Var> {
    let components = all_circuit_components::<Value>();
    let log_sizes = circuit_component_log_sizes(
        &components,
        &child_shared_config.preprocessed_column_log_sizes,
    );
    let log_blowup_factor = child_shared_config.pcs_config.fri_config.log_blowup_factor;

    let mut preimage: Vec<U32Wrapper<Var>> = Vec::new();
    for (_, pp, outs) in group {
        let circuit_hash = compute_circuit_hash(context, &log_sizes, log_blowup_factor, pp);
        // Each output is carried as a single word — rewrap the guessed output `Var` back into the
        // `U32Wrapper` the multiverifier puts in its preimage (no unpack into M31 coords).
        let output_words = outs.iter().map(|v| U32Wrapper::new_unsafe(*v));
        preimage.extend(circuit_hash.iter().copied().chain(output_words));
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
    let height = group.iter().map(|(h, _, _)| *h).max().unwrap() + 1;
    // The children are verified with the parent node's child-verifier config, which fixes each
    // child's `circuit_hash` — the same config the in-circuit multiverifier at this height uses.
    let child_shared_config = NodeKind::child_shared_config(height, config);
    let outs = fold_hash(context, group, child_shared_config);
    let node_pp = constant_pp(context, &reported_root(config, height, group.len()));
    (height, node_pp, outs)
}
