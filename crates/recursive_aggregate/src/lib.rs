//! N-leaf k-to-1 multiverifier recursion: fold N leaf proofs into one root, then prove the
//! root verification (`crate::root_prover`). Each node verifies its k children and emits a Blake
//! hash of their [ppRoot, outs]; the parent consumes that digest.
//!
//! SOUNDNESS: every node's arity/shape/preprocessed_root is a deterministic function of the public
//! N (never prover-chosen), so one SharedConfig + fixed root serve all internal levels. Two-phase
//! fold: level 0 consumes ALL leaves into height-1 nodes (a leaf surviving higher fails the
//! in-circuit Merkle height check); levels >=1 fold nodes k-ary into the (possibly short) root.

pub mod leaf;
pub mod pinned_configs;
pub mod pools;
pub mod precomputes;
pub mod prove;
pub mod prove_streaming;
pub mod root_prover;
#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;
#[cfg(test)]
mod tests;

use std::collections::BTreeMap;

use crate::precomputes::{PreprocessedTree, RecursionPrecompute};

use circuit_common::N_RESERVED;
use circuit_common::finalize::{ComponentSizes, pad_to_targets};
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_prover::prover::{
    CircuitProof, prepare_circuit_proof_for_circuit_verifier, prove_circuit_with_precompute,
};
use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuit_verifier::verify::CircuitConfig;
use circuits::blake::HashValue;
use circuits::context::FinalizedContext;
use circuits_stark_verifier::proof::{Proof, ProofConfig};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sM31MerkleChannel, Blake2sMerkleHasher};
use stwo::prover::ProvingError;

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
/// Short internal nodes (arity `2..=k-1`) have a distinct root per (level, arity), not stored —
/// recomputed on the fly from the public (level, arity). All internal nodes pad to a common
/// `node_target_padding_sizes` so their output proofs share one shape; leaf padding is decoupled
/// (see `leaf_target_padding_sizes`).
pub struct AggregateConfig {
    /// Verifier/prover config for a fold-node whose children are NODES (and for verifying the root
    /// in the unpacker) — the multiverifier's self-verifying fixed point.
    pub fold_shared_config: SharedConfig,
    /// Padding targets applied to every node's trace, so all node proofs share one shape.
    pub node_target_padding_sizes: ComponentSizes,
    /// PCS config to prove each NODE and to verify the root; carries the node-sized lifting.
    pub node_pcs_config: PcsConfig,
    /// Fold arity `k`. The single source of truth read by every fold fn, the unpacker, and the
    /// in-circuit node hash.
    pub fold_arity: usize,
    /// Verifier/prover config for a level-1 node whose children are LEAVES (from
    /// `shared_config_for_leaf`).
    pub leaf_shared_config: SharedConfig,
    /// Per-arity preprocessed root a height-1 (leaf-verifying) level1-node of that arity reports,
    /// keyed by child count `2..=k`. SUPPLIED by the caller (the pinned consts) — never
    /// recomputed.
    pub level1_roots: BTreeMap<usize, HashValue<QM31>>,
    /// Per-arity preprocessed root a height-≥2 (node-verifying) fold-node of that arity reports,
    /// keyed by child count `2..=k`. SUPPLIED by the caller (the pinned consts) — never
    /// recomputed.
    pub fold_roots: BTreeMap<usize, HashValue<QM31>>,
    /// Trusted preprocessed root of the leaf circuit; the unpacker uses this one constant for ALL
    /// leaves (forces a shared leaf AIR).
    pub leaf_preprocessed_root: HashValue<QM31>,
    /// Padding targets for every LEAF's trace — the leaf's own (~2^20), decoupled from node size
    /// so `t_leaf` is pinned independent of the fold arity.
    pub leaf_target_padding_sizes: ComponentSizes,
    /// PCS config to prove each LEAF (leaf lifting ~24, below the node's ~25).
    pub leaf_pcs_config: PcsConfig,
}

impl AggregateConfig {
    /// The reported root of a height-1 (leaf-verifying) level1-node of `arity`. Panics for an arity
    /// the caller did not pin (unsupported).
    pub fn level1_root(&self, arity: usize) -> HashValue<QM31> {
        self.level1_roots
            .get(&arity)
            .unwrap_or_else(|| panic!("no level1 root for arity {arity}"))
            .clone()
    }

    /// The reported root of a height-≥2 (node-verifying) fold-node of `arity`. Panics for an arity
    /// the caller did not pin (unsupported).
    pub fn fold_root(&self, arity: usize) -> HashValue<QM31> {
        self.fold_roots
            .get(&arity)
            .unwrap_or_else(|| panic!("no fold root for arity {arity}"))
            .clone()
    }
}

/// Result of folding the tree.
pub struct AggregateOutput {
    pub root: TreeProof,
    /// Number of recursion levels above the leaves.
    pub n_levels: usize,
}

/// The `SharedConfig` a multiverifier needs to verify children of a pinned child [`CircuitConfig`]
/// (its `config` = child PCS, its `preprocessed_column_log_sizes` = child columns). The pure-const
/// twin of `test_utils::shared_config_for_leaf`: equal to it when the child `CircuitConfig` mirrors
/// the child's `PreprocessedCircuit`. Lets the prover reconstruct a node's child-verifier config
/// from a pinned config alone (no `PreprocessedCircuit` at hand).
pub(crate) fn shared_config_from_circuit_config(child_config: &CircuitConfig) -> SharedConfig {
    let proof_config = ProofConfig::new(
        &all_circuit_components::<QM31>(),
        child_config.preprocessed_column_log_sizes.len(),
        &child_config.config,
        INTERACTION_POW_BITS,
    );
    SharedConfig {
        pcs_config: child_config.config,
        proof_config,
        preprocessed_column_log_sizes: child_config.preprocessed_column_log_sizes.clone(),
    }
}

// Per-node building blocks used by every fold path: the shape helpers and single-node provers
// (level-0 leaf-verifying layer, the shared fold provers, the `reported_root` selector). The fold
// drivers that sequence these into a tree live in `crate::prove`, `crate::prove_streaming`, and the
// unpacker in `crate::root_prover`.

/// What a node's children are (fixed by the public topology). A **level-1** node verifies LEAVES
/// (`leaf_shared_config`) and reports its arity's `level1_roots` entry; a **fold** node (height-≥2)
/// verifies NODES (`fold_shared_config`) and reports its arity's `fold_roots` entry. Only the
/// bottom layer is `Level1`; the up-tree fold is `Fold`.
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

    /// The trusted preprocessed root a node of this kind + `arity` reports (level1-node vs
    /// fold-node).
    fn preprocessed_root(self, config: &AggregateConfig, arity: usize) -> HashValue<QM31> {
        match self {
            NodeKind::Level1 => config.level1_root(arity),
            NodeKind::Fold => config.fold_root(arity),
        }
    }

    /// The held committed tree for this kind's node circuit at `arity`.
    fn tree(self, pre: &RecursionPrecompute, arity: usize) -> &PreprocessedTree {
        match self {
            NodeKind::Level1 => pre.level1_tree(arity),
            NodeKind::Fold => pre.fold_tree(arity),
        }
    }
}

/// The arities of the LEVEL-0 (leaf-verifying) nodes for `n_leaves`, left-to-right — a
/// deterministic function of the public `N` and `k`. Contiguous groups, each arity `2..=k`, NEVER a
/// lone leaf; `r == 1` splits the trailing `k+1` leaves into `(k-1)` and `2` so no arity falls
/// below 2. Consuming ALL leaves here is the leaf↔node padding-decoupling fix (a carried-up leaf
/// would fail the up-tree Merkle height check). Panics if `n_leaves < 2`.
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

/// Proves one LEVEL-0 (height-1, leaf-verifying) node over `children` leaves, reusing the held
/// level1 tree for the node's arity and reporting that arity's pinned level1 root. `height` is
/// always 1.
fn prove_leaf_or_short(
    children: &[TreeProof],
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    height: usize,
) -> TreeProof {
    debug_assert_eq!(height, 1, "level-0 leaf nodes are always height 1");
    let kind = NodeKind::Level1;
    let arity = children.len();
    let _t_node = std::time::Instant::now();
    let context = build_node_context(children, config, kind);

    let circuit_proof = prove_with_tree(context.values(), pre, kind.tree(pre, arity))
        .expect("leaf-node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("leaf-node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_leaf_node(arity={arity},h={height})={:.3}s",
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: kind.preprocessed_root(config, arity),
        output_values,
    }
}

/// The ONE reported-root selector: the trusted preprocessed root a fold node of the given public
/// `(height, arity)` reports, read from the caller-supplied per-arity root table. Both the prover's
/// per-node report and the unpacker's baked constant go through here, so they cannot diverge.
fn reported_root(config: &AggregateConfig, height: usize, arity: usize) -> HashValue<QM31> {
    NodeKind::from_height(height).preprocessed_root(config, arity)
}

/// Proves a padded circuit's `values` against a held [`PreprocessedTree`], reusing its committed
/// tree0 and the shared `twiddles`/`base_column_pool` instead of rebuilding them.
fn prove_with_tree(
    values: &[QM31],
    pre: &RecursionPrecompute,
    tree: &PreprocessedTree,
) -> Result<CircuitProof<Blake2sMerkleHasher>, ProvingError> {
    prove_circuit_with_precompute::<Blake2sM31MerkleChannel>(
        &pre.base_column_pool,
        &pre.twiddles,
        &tree.preprocessed,
        MaybeOwned::Borrowed(&tree.tree),
        values,
        tree.pcs_config,
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

/// Proves one exactly-`k` INTERNAL fold-node verifying `children` nodes. Reports the full-`k`
/// fold-node root and reuses the held fold tree. `height` (≥ 2) is for the measurement log only.
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
    let context = build_node_context(children, config, NodeKind::Fold);

    let circuit_proof = prove_with_tree(context.values(), pre, pre.fold_tree(config.fold_arity))
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
        preprocessed_root: config.fold_root(config.fold_arity),
        output_values,
    }
}

/// Proves one SHORT fold-node (arity `2..=k`) verifying `children` nodes — used for the short ROOT
/// (terminal fold step). Reuses the held fold tree for its arity and reports that arity's pinned
/// fold root. At `m == k` this is exactly the full-`k` shape and root.
fn prove_short_fold_node(
    children: &[TreeProof],
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    height: usize,
) -> TreeProof {
    assert!(
        (2..=config.fold_arity).contains(&children.len()),
        "short/root fold node must have 2..=fold_arity children (got {})",
        children.len()
    );
    let arity = children.len();
    let _t_node = std::time::Instant::now();
    let context = build_node_context(children, config, NodeKind::Fold);

    let circuit_proof = prove_with_tree(context.values(), pre, pre.fold_tree(arity))
        .expect("short/root node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("short/root node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_short_node(arity={arity},h={height})={:.3}s",
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: config.fold_root(arity),
        output_values,
    }
}
