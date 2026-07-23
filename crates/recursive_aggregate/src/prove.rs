//! Non-streaming (collect-then-fold) recursion tree entry point
//! ([`recursive_aggregate_prove_leaves`]): does level 0 then delegates to the private shared
//! up-tree fold ([`recursive_aggregate_prove`]). See the crate root for the tree-shape contract;
//! the streaming variant is in [`crate::prove_streaming`].

use crate::leaf::prove_leaf;
use crate::pools::PoolSet;
use crate::precomputes::RecursionPrecompute;
use crate::{
    AggregateConfig, AggregateOutput, TreeProof, level0_group_sizes, prove_fold_node,
    prove_leaf_or_short, prove_short_fold_node,
};

use circuits::context::FinalizedContext;
use stwo::core::fields::qm31::QM31;

/// Builds+proves one leaf per `inputs` entry (via `build` then [`prove_leaf`], dropping each
/// context right after proving so the N leaf witnesses are never all resident), then folds the
/// resulting leaves into a single root. Level 0 consumes ALL leaves into height-1 level1-nodes via
/// [`level0_group_sizes`], then the shared [`recursive_aggregate_prove`] folds those up. `build` is
/// the AIR-specific leaf-circuit build, run in a pool worker per input. Returns the ordered leaves
/// (for the caller's unpacker) alongside the [`AggregateOutput`]; `n_leaves == 1` ⇒ the lone leaf
/// is the root (`n_levels == 0`).
pub fn recursive_aggregate_prove_leaves<W: Send>(
    inputs: Vec<W>,
    build: impl Fn(W) -> FinalizedContext<QM31> + Sync,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> (Vec<TreeProof>, AggregateOutput) {
    assert!(!inputs.is_empty(), "need at least one leaf");

    // Build+prove+drop each leaf in a pool worker (never hold all N contexts at once).
    let build = &build;
    let leaf_jobs: Vec<_> = inputs
        .into_iter()
        .map(|w| {
            move || {
                prove_leaf(
                    build(w),
                    config.leaf_target_padding_sizes.clone(),
                    pre,
                    config.leaf_preprocessed_root.clone(),
                )
            }
        })
        .collect();
    let leaves: Vec<TreeProof> = pools.map(leaf_jobs);

    (
        leaves.clone(),
        recursive_aggregate_fold_leaves(leaves, config, pre, pools),
    )
}

/// Folds already-proved `leaves` into a single root: level 0 consumes ALL leaves into height-1
/// level1-nodes via [`level0_group_sizes`], then the shared [`recursive_aggregate_prove`] folds
/// those up. `n_leaves == 1` ⇒ the lone leaf is the root (`n_levels == 0`). The fold-only entry for
/// callers holding pre-proved leaves (the build+prove step is theirs); byte-identical to the fold
/// [`recursive_aggregate_prove_leaves`] runs internally.
pub(crate) fn recursive_aggregate_fold_leaves(
    leaves: Vec<TreeProof>,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    let k = config.fold_arity;

    // n_leaves == 1: the lone leaf is itself the root (no fold, height 0).
    if leaves.len() == 1 {
        return AggregateOutput {
            root: leaves.into_iter().next().unwrap(),
            n_levels: 0,
        };
    }

    // Level 0: consume ALL leaves into height-1 level1-nodes (so the up-tree fold sees only nodes).
    let sizes = level0_group_sizes(leaves.len(), k);
    let mut leaves_iter = leaves.into_iter();
    let groups: Vec<Vec<TreeProof>> = sizes
        .iter()
        .map(|&m| leaves_iter.by_ref().take(m).collect())
        .collect();
    let jobs: Vec<_> = groups
        .iter()
        .map(|children| move || prove_leaf_or_short(children, config, pre, 1))
        .collect();
    let leaf_nodes: Vec<TreeProof> = pools.map(jobs);

    // Levels ≥ 1: shared up-tree fold over the height-1 leaf-nodes.
    recursive_aggregate_prove(leaf_nodes, config, pre, pools)
}

/// The SHARED up-tree fold: folds `bottom_nodes` (the fold's height-1 bottom node proofs) into a
/// single root by the `k`-ary group+carry loop — leading full-`k` runs become exactly-`k`
/// fold-nodes, the `< k` remainder carries up unchanged, and the first level `≤ k` folds whole into
/// the (possibly short) root. `M == 1` ⇒ the lone node IS the root. Sibling groups are proved
/// concurrently across `pools`.
fn recursive_aggregate_prove(
    bottom_nodes: Vec<TreeProof>,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!bottom_nodes.is_empty(), "need at least one bottom-node");
    let k = config.fold_arity;

    // M == 1: the lone bottom-node is itself the root (no fold). Its height is 1.
    if bottom_nodes.len() == 1 {
        return AggregateOutput {
            root: bottom_nodes.into_iter().next().unwrap(),
            n_levels: 1,
        };
    }

    // Seed with bottom-nodes at height 1 (a node's height is `max(child heights) + 1`).
    let mut level: Vec<(usize, TreeProof)> =
        bottom_nodes.into_iter().map(|bn| (1usize, bn)).collect();

    while level.len() > 1 {
        if level.len() <= k {
            // Terminal step: fold the whole (2..=k) level into the single (possibly short) root.
            let height = level.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children: Vec<TreeProof> = level.into_iter().map(|(_, p)| p).collect();
            let root = prove_short_fold_node(&children, config, pre, height);
            return AggregateOutput {
                root,
                n_levels: height,
            };
        }
        // len > k: carry the trailing `< k` remainder up; group the leading full-k runs.
        let remainder = level.len() % k;
        let carry: Vec<(usize, TreeProof)> = level.split_off(level.len() - remainder);
        let mut groups: Vec<(usize, Vec<TreeProof>)> = Vec::with_capacity(level.len() / k);
        let mut iter = level.into_iter().peekable();
        while iter.peek().is_some() {
            let group: Vec<(usize, TreeProof)> = iter.by_ref().take(k).collect();
            let height = group.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children: Vec<TreeProof> = group.into_iter().map(|(_, p)| p).collect();
            groups.push((height, children));
        }
        let jobs: Vec<_> = groups
            .iter()
            .map(|(height, children)| {
                move || (*height, prove_fold_node(children, config, pre, *height))
            })
            .collect();
        let mut next: Vec<(usize, TreeProof)> = pools.map(jobs);
        next.extend(carry);
        level = next;
    }

    // M >= 2 folds to a root via the loop's terminal step; reaching here means a single carried
    // entry.
    let (height, root) = level.into_iter().next().unwrap();
    AggregateOutput {
        root,
        n_levels: height,
    }
}
