//! Non-streaming (collect-then-fold) recursion tree entry points: the shared up-tree fold
//! ([`recursive_aggregate_prove`]) and the standalone-leaf entry point
//! ([`recursive_aggregate_prove_leaves`], which does level 0 then delegates to it). See the crate root
//! for the tree-shape contract; streaming variants in [`crate::prove_streaming`].

use crate::pools::PoolSet;
use crate::precomputes::RecursionPrecompute;
use crate::{
    AggregateConfig, AggregateOutput, TreeProof, level0_group_sizes, prove_fold_node,
    prove_leaf_or_short, prove_short_fold_node,
};

/// The SHARED up-tree fold: folds `base_nodes` (height-1 node proofs) into a single root by the
/// `k`-ary group+carry loop — leading full-`k` runs become exactly-`k` fold-nodes, the `< k` remainder
/// carries up unchanged, and the first level `≤ k` folds whole into the (possibly short) root. `M ==
/// 1` ⇒ the lone node IS the root. Sibling groups are proved concurrently across `pools`.
pub fn recursive_aggregate_prove(
    base_nodes: Vec<TreeProof>,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!base_nodes.is_empty(), "need at least one base-node");
    let k = config.fold_arity;

    // M == 1: the lone base-node is itself the root (no fold). Its height is 1.
    if base_nodes.len() == 1 {
        return AggregateOutput {
            root: base_nodes.into_iter().next().unwrap(),
            n_levels: 1,
        };
    }

    // Seed with base-nodes at height 1 (a node's height is `max(child heights) + 1`).
    let mut level: Vec<(usize, TreeProof)> =
        base_nodes.into_iter().map(|bn| (1usize, bn)).collect();

    while level.len() > 1 {
        if level.len() <= k {
            // Terminal step: fold the whole (2..=k) level into the single (possibly short) root.
            let height = level.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children: Vec<TreeProof> = level.into_iter().map(|(_, p)| p).collect();
            let root = prove_short_fold_node(&children, config, height);
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
            .map(|(height, children)| move || (*height, prove_fold_node(children, config, pre, *height)))
            .collect();
        let mut next: Vec<(usize, TreeProof)> = pools.map(jobs);
        next.extend(carry);
        level = next;
    }

    // M >= 2 folds to a root via the loop's terminal step; reaching here means a single carried entry.
    let (height, root) = level.into_iter().next().unwrap();
    AggregateOutput {
        root,
        n_levels: height,
    }
}

/// Folds standalone `leaves` into a single root. Level 0 consumes ALL leaves into height-1
/// level1-nodes via [`level0_group_sizes`], then the shared [`recursive_aggregate_prove`] folds those
/// up. `n_leaves == 1` ⇒ the lone leaf is the root (`n_levels == 0`).
pub fn recursive_aggregate_prove_leaves(
    leaves: Vec<TreeProof>,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!leaves.is_empty(), "need at least one leaf");
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
