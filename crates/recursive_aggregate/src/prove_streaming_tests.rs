use super::{Child, FoldTask, build_fold_topology};
use crate::level0_group_sizes;

/// The arity these topology tests run at — k=8 (the production default). The k=8-pinned expectations
/// below assert `K == 8` so they trip if the default ever changes.
const K: usize = 8;

/// A symbolic, index-aware tree shape — the byte-identity-relevant structure of the node-node fold
/// (each node's ordered children). `Leaf(i)` is base-node `i`.
#[derive(PartialEq, Eq, Debug)]
enum Shape {
    Leaf(usize),
    Node(Vec<Shape>),
}

/// The arity (`∈ 2..=k`) of the ROOT node of the fold over `m` base-nodes — a deterministic function
/// of the public `m`. `m == 1` ⇒ returns `1` (the lone base-node is the root, no fold).
fn root_arity(m_base_nodes: usize, k: usize) -> usize {
    if m_base_nodes == 1 {
        return 1;
    }
    let mut len = m_base_nodes;
    while len > k {
        len = len / k + len % k;
    }
    len
}

/// The shape `recursive_aggregate_prove`'s fold builds over `m` base-nodes — the reference the
/// topology must match. `m == 1` ⇒ the lone base-node is the root.
fn sequential_shape(m: usize) -> Shape {
    if m == 1 {
        return Shape::Leaf(0);
    }
    let mut level: Vec<Shape> = (0..m).map(Shape::Leaf).collect();
    while level.len() > 1 {
        if level.len() <= K {
            return Shape::Node(level);
        }
        let remainder = level.len() % K;
        let carry: Vec<Shape> = level.split_off(level.len() - remainder);
        let mut next: Vec<Shape> = Vec::new();
        let mut iter = level.into_iter().peekable();
        while iter.peek().is_some() {
            let group: Vec<Shape> = iter.by_ref().take(K).collect();
            next.push(Shape::Node(group));
        }
        next.extend(carry);
        level = next;
    }
    level.into_iter().next().unwrap()
}

/// Reference count of fold-nodes the fold proves over `m` base-nodes (`m == 1` ⇒ 0).
fn sequential_node_count(m: usize) -> usize {
    if m == 1 {
        return 0;
    }
    let mut count = 0usize;
    let mut len = m;
    while len > 1 {
        if len <= K {
            count += 1;
            break;
        }
        count += len / K;
        len = len / K + len % K;
    }
    count
}

/// Reference root height of the fold over `m` base-nodes (base-nodes height 1, each level adds 1).
fn sequential_height(m: usize) -> usize {
    if m == 1 {
        return 1;
    }
    let mut height = 1usize; // base-nodes
    let mut len = m;
    while len > 1 {
        height += 1;
        if len <= K {
            break;
        }
        len = len / K + len % K;
    }
    height
}

/// The shape the streaming scheduler realizes, reconstructed from `build_fold_topology`.
fn streaming_shape(m: usize) -> Shape {
    let (tasks, root) = build_fold_topology(m, K);
    fn resolve(c: Child, tasks: &[FoldTask]) -> Shape {
        match c {
            Child::Input(i) => Shape::Leaf(i),
            Child::Fold(j) => Shape::Node(
                tasks[j].children.iter().map(|&ch| resolve(ch, tasks)).collect(),
            ),
        }
    }
    resolve(root, &tasks)
}

/// The streamed tree is byte-identical to the sequential one because it has the identical shape.
/// Sweeps `m` to 260 (all `m mod k` residues across several levels, plus power-of-k boundaries).
#[test]
fn streaming_topology_matches_sequential() {
    for m in 1..=260usize {
        assert_eq!(
            streaming_shape(m),
            sequential_shape(m),
            "fold topology diverges from the level loop at m={m}"
        );
    }
}

/// Pins k=8 group+carry examples: m=9 → `node([node([0..8]), Leaf(8)])` (carried base-node 8);
/// m=17 → root over `node([0..8]), node([8..16]), Leaf(16)`.
#[test]
fn streaming_topology_m9_m17_example_k8() {
    assert_eq!(K, 8, "this pinned example is written for k=8 (the production default)");
    use Shape::{Leaf, Node};
    let m9 = Node(vec![Node((0..8).map(Leaf).collect()), Leaf(8)]);
    assert_eq!(streaming_shape(9), m9);
    let m17 = Node(vec![
        Node((0..8).map(Leaf).collect()),
        Node((8..16).map(Leaf).collect()),
        Leaf(16),
    ]);
    assert_eq!(streaming_shape(17), m17);
}

/// `build_fold_topology`'s fold-node count and root height match the reference over `m` base-nodes.
#[test]
fn topology_node_count_and_height() {
    for m in 1..=260usize {
        let (tasks, root) = build_fold_topology(m, K);
        assert_eq!(
            tasks.len(),
            sequential_node_count(m),
            "m={m}: node count diverges from the fold loop"
        );
        let h = match root {
            Child::Fold(j) => tasks[j].height,
            Child::Input(_) => 1, // the lone base-node (m == 1) is height 1
        };
        assert_eq!(
            h,
            sequential_height(m),
            "m={m}: root height diverges from the fold loop"
        );
    }
}

/// Arity invariants: every non-root fold-node is exactly-`k`; the root may be short (arity ==
/// `root_arity(m)`). All arities `2..=k`, every fold task height ≥ 2.
#[test]
fn arities_valid_shorts_at_root() {
    for m in 2..=260usize {
        let (tasks, root) = build_fold_topology(m, K);
        let root_idx = match root {
            Child::Fold(j) => j,
            Child::Input(_) => unreachable!("m>1 root is a fold node"),
        };
        for (ti, t) in tasks.iter().enumerate() {
            assert!(
                (2..=K).contains(&t.children.len()),
                "m={m}: node {ti} arity {} out of 2..=k",
                t.children.len()
            );
            assert!(t.height >= 2, "m={m}: fold node {ti} must be height >= 2");
            if ti == root_idx {
                assert_eq!(
                    t.children.len(),
                    root_arity(m, K),
                    "m={m}: root arity must equal root_arity(m)"
                );
            } else {
                assert_eq!(
                    t.children.len(),
                    K,
                    "m={m}: non-root fold node {ti} is not exactly-k"
                );
            }
        }
    }
}

/// Pins k=8 root arities + total fold-node count for m ∈ {8, 9, 35, 69} (m=8 clean, the rest exercise
/// the carry).
#[test]
fn fold_pins_key_m() {
    assert_eq!(K, 8, "these pinned expectations are for k=8 (the production default)");
    let cases = [(8usize, 8usize), (9, 2), (35, 7), (69, 6)]; // (m, root_arity)
    for (m, want_root_arity) in cases {
        let (tasks, root) = build_fold_topology(m, K);
        let root_idx = match root {
            Child::Fold(j) => j,
            Child::Input(_) => unreachable!(),
        };
        assert_eq!(
            tasks[root_idx].children.len(),
            want_root_arity,
            "m={m}: unexpected root arity"
        );
        assert_eq!(root_arity(m, K), want_root_arity, "m={m}: root_arity mismatch");
        assert_eq!(
            tasks.len(),
            sequential_node_count(m),
            "m={m}: node count mismatch"
        );
    }
}

// Two-tier (leaf→level1-node→fold-node) streaming DAG topology tests for `recursive_aggregate_prove_leaves_streaming`.
// SYMBOLIC — assert the coordinator's fixed DAG folds the same tree, same child ordering, as
// `recursive_aggregate_prove_leaves` (the byte-identity invariant).

/// A symbolic two-tier tree shape over leaves: `Leaf(i)`, `Level1(children)` (a leaf-verifying node),
/// `Fold(children)` (a node-node fold). Index-aware to capture per-node child ordering.
#[derive(PartialEq, Eq, Debug, Clone)]
enum LeafShape {
    Leaf(usize),
    Level1(Vec<LeafShape>),
    Fold(Vec<LeafShape>),
}

/// The tree `recursive_aggregate_prove_leaves` realizes over `n` leaves (level 0 → level1-nodes, then the
/// up-tree fold) — the reference for the streaming DAG. `n == 1` ⇒ the lone leaf is the root.
fn sequential_leaf_shape(n: usize) -> LeafShape {
    if n == 1 {
        return LeafShape::Leaf(0);
    }
    // Tier 0: contiguous leaf groups → level1-nodes.
    let sizes = level0_group_sizes(n, K);
    let mut next_leaf = 0usize;
    let level1_nodes: Vec<LeafShape> = sizes
        .iter()
        .map(|&sz| {
            let children = (0..sz)
                .map(|_| {
                    let l = LeafShape::Leaf(next_leaf);
                    next_leaf += 1;
                    l
                })
                .collect();
            LeafShape::Level1(children)
        })
        .collect();
    assert_eq!(next_leaf, n);
    let m = level1_nodes.len();
    // Tier ≥ 1: group+carry over the m level1-nodes. m == 1 ⇒ that level1-node IS the root.
    if m == 1 {
        return level1_nodes.into_iter().next().unwrap();
    }
    let mut level: Vec<LeafShape> = level1_nodes;
    while level.len() > 1 {
        if level.len() <= K {
            return LeafShape::Fold(level);
        }
        let remainder = level.len() % K;
        let carry: Vec<LeafShape> = level.split_off(level.len() - remainder);
        let mut nxt: Vec<LeafShape> = Vec::new();
        let mut iter = level.into_iter().peekable();
        while iter.peek().is_some() {
            let group: Vec<LeafShape> = iter.by_ref().take(K).collect();
            nxt.push(LeafShape::Fold(group));
        }
        nxt.extend(carry);
        level = nxt;
    }
    level.into_iter().next().unwrap()
}

/// The tree the STREAMING coordinator realizes over `n` leaves, from the two fixed topology functions
/// (tier 0 = `level0_group_sizes`, tier ≥ 1 = `build_fold_topology` with `Child::Input(g)` = level1-node g).
fn streaming_leaf_shape(n: usize) -> LeafShape {
    if n == 1 {
        return LeafShape::Leaf(0);
    }
    let sizes = level0_group_sizes(n, K);
    // level1-node g's children are the contiguous leaf range [off, off+sz).
    let mut off = 0usize;
    let level1_shapes: Vec<LeafShape> = sizes
        .iter()
        .map(|&sz| {
            let children = (off..off + sz).map(LeafShape::Leaf).collect();
            off += sz;
            LeafShape::Level1(children)
        })
        .collect();
    assert_eq!(off, n);
    let m = level1_shapes.len();
    let (tasks, root) = build_fold_topology(m, K);
    fn resolve(c: Child, tasks: &[FoldTask], level1: &[LeafShape]) -> LeafShape {
        match c {
            Child::Input(g) => level1[g].clone(),
            Child::Fold(j) => LeafShape::Fold(
                tasks[j]
                    .children
                    .iter()
                    .map(|&ch| resolve(ch, tasks, level1))
                    .collect(),
            ),
        }
    }
    resolve(root, &tasks, &level1_shapes)
}

/// The streaming two-tier DAG folds the identical tree `recursive_aggregate_prove_leaves` realizes.
/// Swept over required edge cases plus a dense 1..=260 sweep (all residues, power-of-k boundaries).
#[test]
fn streaming_leaf_topology_matches_sequential() {
    let required = [1usize, 2, K, K + 1, 2 * K + 1, 2 * K + 3];
    for &n in required.iter() {
        assert_eq!(
            streaming_leaf_shape(n),
            sequential_leaf_shape(n),
            "two-tier leaf DAG diverges from recursive_aggregate_prove_leaves at n={n}"
        );
    }
    for n in 1..=260usize {
        assert_eq!(
            streaming_leaf_shape(n),
            sequential_leaf_shape(n),
            "two-tier leaf DAG diverges from recursive_aggregate_prove_leaves at n={n}"
        );
    }
}

/// Tier-0 grouping IS `level0_group_sizes` slicing: leaves land contiguously, each level1-node consuming
/// its group size, every index once in order. Pins n=k+1 (r==1 splits into k-1 and 2).
#[test]
fn tier0_group_assignment_matches_level0_sizes() {
    assert_eq!(K, 8, "the k+1 (r==1) pin is written for k=8 (the production default)");
    // n=9 (r==1): level0_group_sizes → [7, 2], so level1-node 0 = leaves 0..7, level1-node 1 = leaves 7..9.
    use LeafShape::{Leaf, Level1};
    assert_eq!(
        streaming_leaf_shape(9),
        LeafShape::Fold(vec![
            Level1((0..7).map(Leaf).collect()),
            Level1((7..9).map(Leaf).collect()),
        ]),
        "n=9 (r==1) tier-0 grouping wrong"
    );

    // Every leaf index 0..n appears once, contiguous per group; group sizes == level0_group_sizes.
    for n in 2..=260usize {
        let sizes = level0_group_sizes(n, K);
        let shape = streaming_leaf_shape(n);
        let mut collected: Vec<usize> = Vec::new();
        collect_leaf_indices(&shape, &mut collected);
        let expected: Vec<usize> = (0..n).collect();
        assert_eq!(collected, expected, "n={n}: leaves not consumed contiguously in order");
        let mut level1_sizes: Vec<usize> = Vec::new();
        collect_level1_sizes(&shape, &mut level1_sizes);
        assert_eq!(level1_sizes, sizes, "n={n}: level1 group sizes != level0_group_sizes");
    }
}

/// Depth-first collect of leaf indices (left-to-right).
fn collect_leaf_indices(s: &LeafShape, out: &mut Vec<usize>) {
    match s {
        LeafShape::Leaf(i) => out.push(*i),
        LeafShape::Level1(c) | LeafShape::Fold(c) => {
            for ch in c {
                collect_leaf_indices(ch, out);
            }
        }
    }
}

/// Depth-first collect of each level1-node's arity (left-to-right) — the tier-0 group sizes.
fn collect_level1_sizes(s: &LeafShape, out: &mut Vec<usize>) {
    match s {
        LeafShape::Leaf(_) => {}
        LeafShape::Level1(c) => out.push(c.len()),
        LeafShape::Fold(c) => {
            for ch in c {
                collect_level1_sizes(ch, out);
            }
        }
    }
}
