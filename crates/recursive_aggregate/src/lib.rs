//! N-leaf k-to-1 multiverifier recursion: fold N leaf proofs into one root, then prove the
//! root verification (`crate::root_prover`). Each node verifies its k children and emits a Blake hash
//! of their [ppRoot, outs]; the parent consumes that digest.
//!
//! SOUNDNESS: every node's arity/shape/preprocessed_root is a deterministic function of the public N
//! (never prover-chosen), so one SharedConfig + fixed root serve all internal levels. Two-phase fold:
//! level 0 consumes ALL leaves into height-1 nodes (a leaf surviving higher fails the in-circuit
//! Merkle height check); levels >=1 fold nodes k-ary into the (possibly short) root.

pub mod pools;
pub mod precomputes;
pub mod prove;
pub mod prove_streaming;
pub mod root_prover;

use std::sync::Arc;

use crate::precomputes::{CircuitPrecompute, RecursionPrecompute};

use circuit_common::N_RESERVED;
use circuit_common::finalize::{
    ComponentSizes, compute_padded_sizes, pad_to_targets,
};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_prover::prover::{
    CircuitProof, prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
    prove_circuit_with_precompute,
};
use circuits::blake::HashValue;
use circuits::context::FinalizedContext;
use circuits_stark_verifier::proof::Proof;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sM31MerkleChannel, Blake2sMerkleHasher};
use stwo::prover::ProvingError;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;

use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuits::ivalue::NoValue;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use num_traits::Zero;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::poly::circle::PolyOps;

/// A proven node carried up the tree: the proof plus the two pieces the parent multiverifier needs
/// (the producing circuit's preprocessed root and its output values).
#[derive(Clone)]
pub struct TreeProof {
    pub proof: Proof<QM31>,
    pub preprocessed_root: HashValue<QM31>,
    pub output_values: [QM31; N_RESERVED],
}

/// Static configuration shared by every node in the tree. 
///
/// Short internal nodes (arity `2..=k-1`) have a distinct root per (level, arity), not stored — recomputed on
/// the fly from the public (level, arity). All internal nodes pad to a common `node_target_padding_sizes`
/// so their output proofs share one shape; leaf padding is decoupled (see `leaf_target_padding_sizes`).
pub struct AggregateConfig {
    /// Verifier/prover config for a fold-node whose children are NODES (and for verifying the root in
    /// the unpacker) — the multiverifier's self-verifying fixed point.
    pub fold_shared_config: SharedConfig,
    /// Preprocessed root reported by every height-≥2 (node-verifying) fold-node.
    pub fold_preprocessed_root: HashValue<QM31>,
    /// Padding targets applied to every node's trace, so all node proofs share one shape.
    pub node_target_padding_sizes: ComponentSizes,
    /// PCS config to prove each NODE and to verify the root; carries the node-sized lifting.
    pub node_pcs_config: PcsConfig,
    /// Fold arity `k`. The single source of truth read by every fold fn, the unpacker, and the
    /// in-circuit node hash.
    pub fold_arity: usize,
    /// Verifier/prover config for a level-1 node whose children are LEAVES (from `shared_config_for_leaf`).
    pub leaf_shared_config: SharedConfig,
    /// Preprocessed root reported by every height-1 (leaf-verifying) level1-node.
    pub level1_preprocessed_root: HashValue<QM31>,
    /// Trusted preprocessed root of the leaf circuit; the unpacker uses this one constant for ALL
    /// leaves (forces a shared leaf AIR).
    pub leaf_preprocessed_root: HashValue<QM31>,
    /// Padding targets for every LEAF's trace — the leaf's own (~2^20), decoupled from node size so
    /// `t_leaf` is pinned independent of the fold arity.
    pub leaf_target_padding_sizes: ComponentSizes,
    /// PCS config to prove each LEAF (leaf lifting ~24, below the node's ~25).
    pub leaf_pcs_config: PcsConfig,
}

impl AggregateConfig {
    /// Defense-in-depth: the full-`k` node-node root recomputed via
    /// [`short_fold_preprocessed_root`] must equal the trusted fold-node root (and the level1
    /// recompute must equal the trusted level1-node root). Agrees by construction; a divergence is
    /// already fail-closed, so this just makes it loud.
    pub fn assert_full_arity_roots_consistent(&self) {
        let k = self.fold_arity;
        assert_eq!(
            short_fold_preprocessed_root(self, k),
            self.fold_preprocessed_root,
            "full-{k} node-node preprocessed root recompute != trusted fold-node root",
        );
        assert_eq!(
            short_leaf_node_preprocessed_root(self, k),
            self.level1_preprocessed_root,
            "full-{k} leaf-node preprocessed root recompute != trusted level1-node root",
        );
    }
}

/// Result of folding the tree.
pub struct AggregateOutput {
    pub root: TreeProof,
    /// Number of recursion levels above the leaves.
    pub n_levels: usize,
}

// Config-derivation helpers: build an `AggregateConfig` verifying leaves of a given circuit's config.

/// Merkle root of a circuit's preprocessed trace.
pub fn preprocessed_root(
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

/// The `SharedConfig` a multiverifier needs to verify leaves of `leaf_preprocessed`'s config.
pub fn shared_config_for_leaf(
    leaf_preprocessed: &PreprocessedCircuit,
    pcs_config: PcsConfig,
) -> SharedConfig {
    let proof_config = ProofConfig::new(
        &all_circuit_components::<QM31>(),
        leaf_preprocessed.preprocessed_trace.n_columns(),
        &pcs_config,
        INTERACTION_POW_BITS,
    );
    SharedConfig {
        pcs_config,
        proof_config,
        preprocessed_column_log_sizes: leaf_preprocessed.preprocessed_trace.log_sizes(),
    }
}

/// Builds + preprocesses the NoValue multiverifier node circuit of `arity` children for a given
/// `shared` config, padded to `target_padding`. `arity == k` is the fixed internal-node shape (cache
/// in a node [`CircuitPrecompute`]); `arity < k` is a SHORT node. Keyed on the already-built
/// `SharedConfig` so a caller holding only an [`AggregateConfig`] can rebuild the cache.
pub fn node_preprocessed_from_shared(
    shared: &SharedConfig,
    target_padding: ComponentSizes,
    arity: usize,
) -> PreprocessedCircuit {
    // Same node circuit as `prove_fold_node`/`prove_short_fold_node`, with NoValue witnesses (the preprocessed
    // trace is witness-independent).
    let proof_config =
        noval_node_proof_config(shared.proof_config.n_preprocessed_columns, &shared.pcs_config);
    let node_shared = SharedConfig {
        pcs_config: shared.pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: shared.preprocessed_column_log_sizes.clone(),
    };
    let inputs: Vec<MultiverifierInput<NoValue>> =
        (0..arity).map(|_| empty_node_input(&proof_config)).collect();
    let mut ctx = build_multiverifier_circuit::<NoValue>(inputs, &node_shared);
    pad_to_targets(&mut ctx, target_padding);
    PreprocessedCircuit::preprocess_circuit(&mut ctx)
}

/// Builds + preprocesses the NoValue node verifying leaves of `leaf_preprocessed`'s config (optionally
/// padded), to recompute the node's `preprocessed_root`. Also returns the node's UNPADDED component
/// sizes (for deriving the shared `TARGET_PADDING_SIZES = max(leaf, node)`).
pub fn multiverifier_node_preprocessed(
    leaf_preprocessed: &PreprocessedCircuit,
    pcs_config: PcsConfig,
    target_padding: Option<ComponentSizes>,
    fold_arity: usize,
) -> (PreprocessedCircuit, ComponentSizes) {
    let proof_config =
        noval_node_proof_config(leaf_preprocessed.preprocessed_trace.n_columns(), &pcs_config);
    let shared = SharedConfig {
        pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: leaf_preprocessed.preprocessed_trace.log_sizes(),
    };
    let inputs: Vec<MultiverifierInput<NoValue>> =
        (0..fold_arity).map(|_| empty_node_input(&proof_config)).collect();
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

// Per-node building blocks used by every fold path: the shape helpers and single-node provers
// (level-0 leaf-verifying layer, the shared fold provers, the `reported_root` selector). The fold
// drivers that sequence these into a tree live in `crate::prove`, `crate::prove_streaming`, and the
// unpacker in `crate::root_prover`.

/// What a node's children are (fixed by the public topology). A **level-1** node verifies LEAVES
/// (`leaf_shared_config`) and reports `level1_preprocessed_root`; a **fold** node (height-≥2) verifies
/// NODES (`fold_shared_config`) and reports `fold_preprocessed_root`. Only the bottom layer
/// is `Level1`; the up-tree fold is `Fold`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeKind {
    /// Children are leaves (node height == 1).
    Level1,
    /// Children are nodes (node height >= 2).
    Fold,
}

impl NodeKind {
    /// The node kind for a node of the given height above the leaves (leaves are height 0).
    fn from_height(height: usize) -> Self {
        if height == 1 {
            NodeKind::Level1
        } else {
            NodeKind::Fold
        }
    }

    /// The child-verifier config: `leaf_shared_config` (level1) or `fold_shared_config` (fold).
    fn shared_config(self, config: &AggregateConfig) -> &SharedConfig {
        match self {
            NodeKind::Level1 => &config.leaf_shared_config,
            NodeKind::Fold => &config.fold_shared_config,
        }
    }

    /// The trusted preprocessed root a node of this kind reports (level1-node vs fold-node).
    fn preprocessed_root(self, config: &AggregateConfig) -> HashValue<QM31> {
        match self {
            NodeKind::Level1 => config.level1_preprocessed_root.clone(),
            NodeKind::Fold => config.fold_preprocessed_root.clone(),
        }
    }

    /// The witness-independent precompute for this kind's node circuit, if built.
    fn precompute(self, pre: &RecursionPrecompute) -> Option<&Arc<CircuitPrecompute>> {
        match self {
            NodeKind::Level1 => pre.level1_precompute.as_ref(),
            NodeKind::Fold => pre.fold_precompute.as_ref(),
        }
    }
}

/// The arities of the LEVEL-0 (leaf-verifying) nodes for `n_leaves`, left-to-right — a deterministic
/// function of the public `N` and `k`. Contiguous groups, each arity `2..=k`, NEVER a lone leaf; `r ==
/// 1` splits the trailing `k+1` leaves into `(k-1)` and `2` so no arity falls below 2. Consuming ALL
/// leaves here is the leaf↔node padding-decoupling fix (a carried-up leaf would fail the up-tree
/// Merkle height check). Panics if `n_leaves < 2`.
fn level0_group_sizes(n_leaves: usize, k: usize) -> Vec<usize> {
    assert!(n_leaves >= 2, "level0_group_sizes needs n_leaves >= 2");
    if n_leaves <= k {
        return vec![n_leaves];
    }
    let full = n_leaves / k;
    let r = n_leaves % k;
    match r {
        0 => vec![k; full],
        1 => {
            let mut v = vec![k; full - 1];
            v.push(k - 1);
            v.push(2);
            v
        }
        _ => {
            let mut v = vec![k; full];
            v.push(r);
            v
        }
    }
}

/// Proves one LEVEL-0 (height-1, leaf-verifying) node over `children` leaves: full-`k` groups reuse
/// the level1 precompute and report the fixed level1-node root; short groups recompute their real
/// root. `height` is always 1.
fn prove_leaf_or_short(
    children: &[TreeProof],
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    height: usize,
) -> TreeProof {
    debug_assert_eq!(height, 1, "level-0 leaf nodes are always height 1");
    let kind = NodeKind::Level1;
    let _t_node = std::time::Instant::now();
    let full = children.len() == config.fold_arity;
    let mut context = build_node_context(children, config, kind);

    let (preprocessed_root_reported, circuit_proof) = if full {
        // Full-`k`: reuse the level1 precompute (or self-contained path), report the fixed root.
        let cp = match kind.precompute(pre) {
            Some(pc) => prove_with_precompute(context.values(), pc),
            None => {
                let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
                prove_circuit_assignment(
                    context.values(),
                    &preprocessed,
                    &BaseColumnPool::<SimdBackend>::new(),
                    config.node_pcs_config,
                )
            }
        };
        (kind.preprocessed_root(config), cp)
    } else {
        // Short group: distinct shape, rebuild tree0 and report the recomputed real root.
        let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
        let root =
            preprocessed_root(&preprocessed, config.node_pcs_config.fri_config.log_blowup_factor);
        let cp = prove_circuit_assignment(
            context.values(),
            &preprocessed,
            &BaseColumnPool::<SimdBackend>::new(),
            config.node_pcs_config,
        );
        (root, cp)
    };
    let circuit_proof = circuit_proof.expect("leaf-node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("leaf-node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_leaf_node(arity={},h={height})={:.3}s",
        children.len(),
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: preprocessed_root_reported,
        output_values,
    }
}

/// The preprocessed root a SHORT node of the given `(kind, arity)` reports — recomputed
/// witness-independently over that kind's child config, matching what the prover recomputes for the
/// same shape. Shared body of the two kind-specialised recomputes.
fn short_node_preprocessed_root_at_kind(
    config: &AggregateConfig,
    kind: NodeKind,
    arity: usize,
) -> HashValue<QM31> {
    let shared = kind.shared_config(config);
    let pp = node_preprocessed_from_shared(
        shared,
        config.node_target_padding_sizes.clone(),
        arity,
    );
    preprocessed_root(&pp, config.node_pcs_config.fri_config.log_blowup_factor)
}

/// The preprocessed root a SHORT leaf-verifying (level1) node of the given `arity` reports.
fn short_leaf_node_preprocessed_root(config: &AggregateConfig, arity: usize) -> HashValue<QM31> {
    short_node_preprocessed_root_at_kind(config, NodeKind::Level1, arity)
}

/// The ONE reported-root selector: the trusted preprocessed root a fold node of the given public
/// `(height, arity)` reports — full-`k` ⇒ the fixed level1/fold-node root, short ⇒ the recomputed real
/// root. Both the prover's per-node report and the unpacker's baked constant go through here, so they
/// cannot diverge.
fn reported_root(config: &AggregateConfig, height: usize, arity: usize) -> HashValue<QM31> {
    let kind = NodeKind::from_height(height);
    if arity == config.fold_arity {
        kind.preprocessed_root(config)
    } else {
        short_node_preprocessed_root_at_kind(config, kind, arity)
    }
}

/// Proves a padded circuit's `values` against a prebuilt [`CircuitPrecompute`], reusing its committed
/// tree0 and twiddles instead of rebuilding them.
fn prove_with_precompute(
    values: &[QM31],
    pc: &CircuitPrecompute,
) -> Result<CircuitProof<Blake2sMerkleHasher>, ProvingError> {
    prove_circuit_with_precompute::<Blake2sM31MerkleChannel>(
        &pc.base_column_pool,
        &pc.twiddles,
        &pc.preprocessed,
        MaybeOwned::Borrowed(&pc.tree),
        values,
        pc.pcs_config,
    )
}

/// The `MultiverifierInput` for one child (its proof + the two pieces its parent needs).
fn child_input(c: &TreeProof) -> MultiverifierInput<QM31> {
    MultiverifierInput {
        proof: c.proof.clone(),
        preprocessed_root: c.preprocessed_root.clone(),
        output_values: c.output_values,
    }
}

/// Builds + pads the multiverifier circuit verifying `children` with the child-verifier config for
/// the node's `kind` (`Level1` verifies leaves, `Fold` verifies nodes). The generic node-context
/// builder shared by both the level-0 leaf layer and the up-tree fold.
fn build_node_context(
    children: &[TreeProof],
    config: &AggregateConfig,
    kind: NodeKind,
) -> FinalizedContext<QM31> {
    let inputs: Vec<MultiverifierInput<QM31>> = children.iter().map(child_input).collect();
    let mut context = build_multiverifier_circuit::<QM31>(inputs, kind.shared_config(config));
    pad_to_targets(&mut context, config.node_target_padding_sizes.clone());
    context.validate_circuit();
    context
}

/// Proves one exactly-`k` INTERNAL fold-node verifying `children` nodes. Reports the fold-node root
/// and reuses `fold_precompute`. `height` (≥ 2) is for the measurement log only.
fn prove_fold_node(
    children: &[TreeProof],
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    height: usize,
) -> TreeProof {
    debug_assert_eq!(
        children.len(),
        config.fold_arity,
        "internal fold node must have exactly fold_arity children"
    );
    let _t_node = std::time::Instant::now();
    let mut context = build_node_context(children, config, NodeKind::Fold);

    let circuit_proof = match pre.fold_precompute.as_ref() {
        Some(pc) => prove_with_precompute(context.values(), pc),
        None => {
            let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
            prove_circuit_assignment(
                context.values(),
                &preprocessed,
                &BaseColumnPool::<SimdBackend>::new(),
                config.node_pcs_config,
            )
        }
    }
    .expect("node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_node(h={height})={:.3}s",
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: config.fold_preprocessed_root.clone(),
        output_values,
    }
}

/// Proves one SHORT fold-node (arity `2..=k`) verifying `children` nodes — used for the short ROOT
/// (terminal fold step). Its distinct shape can't reuse `fold_precompute`, so it rebuilds; the
/// reported `preprocessed_root` is the circuit's real root (recomputed here, matching the unpacker's
/// [`short_fold_preprocessed_root`]). At `m == k` this is exactly the full-`k` shape and root.
fn prove_short_fold_node(
    children: &[TreeProof],
    config: &AggregateConfig,
    height: usize,
) -> TreeProof {
    assert!(
        (2..=config.fold_arity).contains(&children.len()),
        "short/root fold node must have 2..=fold_arity children (got {})",
        children.len()
    );
    let _t_node = std::time::Instant::now();
    let mut context = build_node_context(children, config, NodeKind::Fold);

    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let short_preprocessed_root =
        preprocessed_root(&preprocessed, config.node_pcs_config.fri_config.log_blowup_factor);
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
        config.node_pcs_config,
    )
    .expect("short/root node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("short/root node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_short_node(arity={},h={height})={:.3}s",
        children.len(),
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: short_preprocessed_root,
        output_values,
    }
}

/// The `NoValue` node `ProofConfig` a multiverifier NODE circuit is built/proved with. Shared by the
/// two NoValue node builders so they derive the config identically.
fn noval_node_proof_config(n_preprocessed_columns: usize, pcs_config: &PcsConfig) -> ProofConfig {
    ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        n_preprocessed_columns,
        pcs_config,
        INTERACTION_POW_BITS,
    )
}

/// A placeholder `NoValue` child input for building the witness-independent node shape.
fn empty_node_input(proof_config: &ProofConfig) -> MultiverifierInput<NoValue> {
    MultiverifierInput {
        proof: empty_proof(proof_config),
        preprocessed_root: HashValue::from([0u32; N_RESERVED]),
        output_values: [QM31::zero(); N_RESERVED],
    }
}

/// The preprocessed root a SHORT fold-node (the short ROOT) of the given `arity` reports.
fn short_fold_preprocessed_root(config: &AggregateConfig, arity: usize) -> HashValue<QM31> {
    short_node_preprocessed_root_at_kind(config, NodeKind::Fold, arity)
}
