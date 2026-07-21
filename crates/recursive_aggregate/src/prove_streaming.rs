//! Streaming (overlapped) recursion tree entry points: fold-as-you-go variants of [`crate::prove`]
//! that dispatch each fold to a [`PoolSet`] worker the instant its children are ready, so the CPU
//! fold overlaps the upstream (GPU) producer feeding the channel.
//!
//! BYTE-IDENTITY (the invariant every streaming path relies on): each realizes the SAME fixed tree as
//! its non-streaming counterpart — topology fixed up front by [`build_fold_topology`] (and
//! [`level0_group_sizes`]) with each node's children in the sequential order. Since every per-node
//! prover is a pure function of its ordered children, identical shape ⇒ identical root proof and
//! `recursion_fingerprint`; completion order only changes WHEN a slot fills, never the result.

use crate::pools::PoolSet;
use crate::precomputes::RecursionPrecompute;
use crate::{
    AggregateConfig, AggregateOutput, TreeProof, level0_group_sizes, prove_fold_node,
    prove_leaf_or_short, prove_short_fold_node,
};

/// Streaming variant of [`crate::prove::recursive_aggregate_prove`]: folds base-nodes as they arrive
/// on `rx`, dispatching each fold the instant its children are ready so the fold overlaps the upstream
/// producer. The producer sends completed base-node proofs in canonical order (base-node `i` = the
/// `i`-th `recv()`), keeping this crate leaf-type-agnostic. Result is byte-identical to the sequential
/// path (see the module doc). `m_base_nodes == 1` ⇒ the single base-node as root (`n_levels = 1`).
pub fn recursive_aggregate_prove_streaming(
    rx: std::sync::mpsc::Receiver<TreeProof>,
    m_base_nodes: usize,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(m_base_nodes >= 1, "need at least one base-node");
    let k = config.fold_arity;

    let (tasks, root_ref) = build_fold_topology(m_base_nodes, k);

    if m_base_nodes == 1 {
        let root = rx.recv().expect("streaming fold: missing base-node 0");
        return AggregateOutput { root, n_levels: 1 };
    }

    let n_tasks = tasks.len();
    let (state, input_parent, node_parent) = build_state(&tasks, m_base_nodes);
    let state = std::sync::Mutex::new(state);
    // Signalled when a fold becomes ready or all folds are done.
    let cv = std::sync::Condvar::new();

    let n_workers = pools.n_pools().max(1);
    std::thread::scope(|s| {
        // Workers: one per pool. Pull a ready task, prove it, deliver to the parent, signal.
        for pool in pools.pools.iter().take(n_workers) {
            let state = &state;
            let cv = &cv;
            let node_parent = &node_parent;
            let tasks = &tasks;
            s.spawn(move || {
                // On panic, mark aborted so parked siblings wake and `thread::scope` join won't hang.
                let _abort = AbortGuard {
                    set_aborted: || {
                        let mut st = state.lock().unwrap_or_else(|e| e.into_inner());
                        st.aborted = true;
                    },
                    cv,
                };
                while let Some(ti) = next_ready(state, cv, n_tasks) {
                    // Take ownership of the resolved inputs and prove off-lock. Children are `take()`n
                    // out, so once the result is delivered they are dropped: peak host memory holds
                    // only the N leaves (caller-owned) + the O(log_k N) in-flight fold path, not all
                    // node proofs.
                    let children: Vec<TreeProof> = {
                        let mut st = state.lock().unwrap();
                        st.inputs[ti]
                            .iter_mut()
                            .map(|slot| slot.take().unwrap())
                            .collect()
                    };
                    let is_root = node_parent[ti].is_none();
                    let height = tasks[ti].height;
                    let result =
                        pool.install(|| run_fold_task(&children, is_root, height, config, pre));
                    {
                        let mut st = state.lock().unwrap();
                        match node_parent[ti] {
                            Some(parent) => deliver(&mut st, Some(parent), result),
                            None => st.root = Some(result), // the root fold (no parent)
                        }
                        st.done += 1;
                        cv.notify_all();
                    }
                }
            });
        }

        // Coordinator: drain base-nodes in canonical order, delivering each to its consumer (which
        // may enqueue a now-ready fold), so folds overlap the still-arriving base-nodes.
        for &parent in &input_parent {
            let base_node = rx
                .recv()
                .expect("streaming fold: fewer base-nodes than m_base_nodes");
            let mut st = state.lock().unwrap();
            deliver(&mut st, parent, base_node);
            cv.notify_all();
        }
    });

    let root_idx = match root_ref {
        Child::Fold(j) => j,
        Child::Input(_) => unreachable!("m_base_nodes > 1 ⇒ root is a fold node"),
    };
    let root = state
        .into_inner()
        .unwrap()
        .root
        .expect("root not produced");
    AggregateOutput {
        root,
        n_levels: tasks[root_idx].height,
    }
}

/// Overlapped variant of [`crate::prove::recursive_aggregate_prove_leaves`]: wraps streamed producer
/// inputs into leaves AND folds the whole tree (level-0 leaf→level1-node layer + up-tree fold)
/// progressively, as leaves and nodes become ready — overlapping the still-arriving producer.
///
/// LEAF-AGNOSTIC: the AIR-specific leaf-wrap is injected as `wrap: impl Fn(W) -> TreeProof` over a
/// generic input `W`, keeping this crate leaf-type-agnostic; `wrap` runs inside a pool worker. One
/// coordinator feeds `pools.n_pools()` symmetric pull-workers off a single ready-queue of [`Job`]s,
/// Fold-priority to bound host RAM (byte-irrelevant, per the module doc).
///
/// Byte-identical to [`crate::prove::recursive_aggregate_prove_leaves`]: topology fixed by the same
/// [`level0_group_sizes`] + [`build_fold_topology`], child ordering by index. Consumes exactly
/// `n_leaves` items from `rx` in ARBITRARY order (each tagged with its canonical index) and returns
/// the ordered leaves (for the `LeafBottom` unpacker) plus the [`AggregateOutput`]. `n_leaves == 1` ⇒
/// the wrapped leaf is the root (`n_levels == 0`); `2 <= n_leaves <= k` ⇒ the single level1-node is
/// the root (`n_levels == 1`). Panics on a duplicate/out-of-range leaf index; a `wrap`/fold panic
/// re-panics on the parent via `thread::scope`.
pub fn recursive_aggregate_prove_leaves_streaming<W: Send>(
    rx: std::sync::mpsc::Receiver<(usize, W)>,
    n_leaves: usize,
    wrap: impl Fn(W) -> TreeProof + Sync,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> (Vec<TreeProof>, AggregateOutput) {
    assert!(n_leaves >= 1, "need at least one leaf");
    let k = config.fold_arity;

    // n_leaves == 1: the lone wrapped leaf is itself the root (no fold, height 0). No workers.
    if n_leaves == 1 {
        let (idx, w) = rx.recv().expect("streaming leaves fold: missing leaf 0");
        assert_eq!(idx, 0, "single-leaf stream must carry index 0");
        let leaf = wrap(w);
        let out = AggregateOutput { root: leaf.clone(), n_levels: 0 };
        return (vec![leaf], out);
    }

    // Tier 0 (leaf→level1-node) topology: contiguous leaf groups.
    let sizes = level0_group_sizes(n_leaves, k);
    let m = sizes.len(); // number of level1-nodes (= build_fold_topology's base-node count)
    debug_assert_eq!(
        sizes.iter().sum::<usize>(),
        n_leaves,
        "level0 groups must cover all leaves"
    );

    // Tier ≥ 1 (up-tree fold) topology over the m level1-nodes: the same fixed DAG the sequential
    // fold realizes. Here a `Child::Input(g)` denotes level1-node g (not a base-node).
    let (tasks, root_ref) = build_fold_topology(m, k);

    // Total scheduled jobs: n_leaves wraps + m level1-nodes + fold tasks.
    let n_jobs = n_leaves + m + tasks.len();
    let (state, topo) = build_leaves_state::<W>(&sizes, &tasks, n_leaves);
    let LeavesTopo { leaf_group, level1_parent, node_parent } = topo;
    let state = std::sync::Mutex::new(state);
    let cv = std::sync::Condvar::new();

    let n_workers = pools.n_pools().max(1);
    std::thread::scope(|s| {
        for pool in pools.pools.iter().take(n_workers) {
            let state = &state;
            let cv = &cv;
            let level1_parent = &level1_parent;
            let node_parent = &node_parent;
            let leaf_group = &leaf_group;
            let sizes = &sizes;
            let tasks = &tasks;
            let wrap = &wrap;
            s.spawn(move || {
                // On panic, mark aborted so parked siblings wake and `thread::scope` join won't hang.
                let _abort = AbortGuard {
                    set_aborted: || {
                        let mut st = state.lock().unwrap_or_else(|e| e.into_inner());
                        st.aborted = true;
                    },
                    cv,
                };
                while let Some(job) = next_job(state, cv, n_jobs) {
                    match job {
                        // Tier 0a: wrap producer input `i` into leaf `i`.
                        Job::Wrap(i) => {
                            let w = {
                                let mut st = state.lock().unwrap();
                                st.wrap_inputs[i].take().expect("wrap input missing")
                            };
                            let leaf = pool.install(|| wrap(w));
                            let (g, slot) = leaf_group[i];
                            let mut st = state.lock().unwrap();
                            // Record the ordered leaf for the caller + slot it into its level1 group by index.
                            st.leaves_out[i] = Some(leaf.clone());
                            st.level1_inputs[g][slot] = Some(leaf);
                            st.level1_remaining[g] -= 1;
                            if st.level1_remaining[g] == 0 {
                                st.ready_level1.push_back(g);
                            }
                            st.done += 1;
                            cv.notify_all();
                        }
                        // Tier 0b: prove level-0 (leaf→level1-node) group `g`.
                        Job::Level1(g) => {
                            let children: Vec<TreeProof> = {
                                let mut st = state.lock().unwrap();
                                st.level1_inputs[g]
                                    .iter_mut()
                                    .map(|slot| slot.take().unwrap())
                                    .collect()
                            };
                            debug_assert_eq!(children.len(), sizes[g]);
                            // level1-nodes are always height 1.
                            let result =
                                pool.install(|| prove_leaf_or_short(&children, config, pre, 1));
                            let mut st = state.lock().unwrap();
                            deliver_node(&mut st, level1_parent[g], result);
                            st.done += 1;
                            cv.notify_all();
                        }
                        // Tier ≥ 1: shared node-node fold task.
                        Job::Fold(ti) => {
                            let children: Vec<TreeProof> = {
                                let mut st = state.lock().unwrap();
                                st.fold_inputs[ti]
                                    .iter_mut()
                                    .map(|slot| slot.take().unwrap())
                                    .collect()
                            };
                            let is_root = node_parent[ti].is_none();
                            let height = tasks[ti].height;
                            let result = pool
                                .install(|| run_fold_task(&children, is_root, height, config, pre));
                            let mut st = state.lock().unwrap();
                            deliver_node(&mut st, node_parent[ti], result);
                            st.done += 1;
                            cv.notify_all();
                        }
                    }
                }
            });
        }

        // Coordinator: drain the producer inputs (arbitrary order) and enqueue a Wrap job each, so
        // wrap + level1 + fold overlap the still-arriving producer.
        for _ in 0..n_leaves {
            let (idx, w) = rx
                .recv()
                .expect("streaming leaves fold: fewer inputs than n_leaves");
            assert!(idx < n_leaves, "leaf index {idx} out of range");
            let mut st = state.lock().unwrap();
            assert!(st.wrap_inputs[idx].is_none(), "leaf index {idx} arrived twice");
            st.wrap_inputs[idx] = Some(w);
            st.ready_wrap.push_back(idx);
            cv.notify_all();
        }
    });

    // Assemble the ordered leaves + the root.
    let mut st = state.into_inner().unwrap();
    let leaves: Vec<TreeProof> = st
        .leaves_out
        .iter_mut()
        .enumerate()
        .map(|(i, l)| l.take().unwrap_or_else(|| panic!("leaf {i} missing after streaming fold")))
        .collect();
    let root = st.root.take().expect("root not produced");
    let n_levels = match root_ref {
        Child::Input(_) => 1, // m == 1: the single level-0 level1-node is the root
        Child::Fold(j) => tasks[j].height,
    };
    (leaves, AggregateOutput { root, n_levels })
}

/// A reference to one input of a streaming fold node: a fold INPUT supplied from below (by index — a
/// base-node in the base-node streamer, a level1-node in the leaves streamer) or the output of an
/// earlier fold node (by task index).
#[derive(Clone, Copy)]
enum Child {
    Input(usize),
    Fold(usize),
}

/// One fold in the fixed tree: a fold-node over `children` (left-to-right). Internal tasks are
/// exactly-`k`; the single ROOT task may be short (`2..=k`). Every fold task is height ≥ 2.
struct FoldTask {
    children: Vec<Child>,
    /// Height above the bases (bases are height 0; base-nodes height 1; the first fold height 2).
    height: usize,
}

/// The FIXED node-node fold topology for `m_base_nodes` base-nodes — the up-front tree the BYTE-IDENTITY
/// invariant refers to (same tree + child order as [`crate::prove::recursive_aggregate_prove`]'s level
/// loop). Runs the group+carry loop over the height-1 base-nodes. The returned [`Child`] is the root
/// (`Fold` for `m > 1`, else `Input(0)`); `Child::Input(i)` denotes base-node `i`.
fn build_fold_topology(m_base_nodes: usize, k: usize) -> (Vec<FoldTask>, Child) {
    if m_base_nodes == 1 {
        return (Vec::new(), Child::Input(0));
    }
    let mut tasks: Vec<FoldTask> = Vec::new();

    // Seed with the `m` base-nodes at height 1.
    let mut level: Vec<(usize, Child)> = (0..m_base_nodes).map(|i| (1, Child::Input(i))).collect();

    while level.len() > 1 {
        if level.len() <= k {
            // Terminal step: the whole (2..=k) level folds into the single (possibly short) root.
            let height = level.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children = level.iter().map(|(_, c)| *c).collect();
            let idx = tasks.len();
            tasks.push(FoldTask { children, height });
            return (tasks, Child::Fold(idx));
        }
        let remainder = level.len() % k;
        let carry: Vec<(usize, Child)> = level.split_off(level.len() - remainder);
        let mut next: Vec<(usize, Child)> = Vec::with_capacity(level.len() / k + remainder);
        for group in level.chunks(k) {
            let height = group.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children = group.iter().map(|(_, c)| *c).collect();
            let idx = tasks.len();
            tasks.push(FoldTask { children, height });
            next.push((height, Child::Fold(idx)));
        }
        next.extend(carry);
        level = next;
    }
    (tasks, level[0].1)
}

/// Proves ONE tier-≥1 fold task over its ordered `children`, dispatching EXACTLY as the sequential
/// fold: the ROOT ⇒ [`prove_short_fold_node`] even at full arity (the sequential terminal step always
/// does), else full-`k` ⇒ [`prove_fold_node`]. Pure function of its inputs, so completion order cannot
/// affect the result; shared by both streaming coordinators so their dispatch cannot diverge.
fn run_fold_task(
    children: &[TreeProof],
    is_root: bool,
    height: usize,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
) -> TreeProof {
    let k = config.fold_arity;
    if is_root {
        prove_short_fold_node(children, config, height)
    } else if children.len() == k {
        prove_fold_node(children, config, pre, height)
    } else {
        prove_short_fold_node(children, config, height)
    }
}

/// Dataflow state shared between the coordinator and the worker threads.
struct State {
    // Resolved child inputs per task (one slot per child, left-to-right), filled as children arrive.
    inputs: Vec<Vec<Option<TreeProof>>>,
    pending: Vec<usize>,
    ready: std::collections::VecDeque<usize>,
    done: usize,
    root: Option<TreeProof>,
    // Set by a panicking worker's drop-guard so parked siblings wake and exit (see `AbortGuard`).
    aborted: bool,
}

/// Records `proof` as the value of `child`, wiring it into its consuming task and enqueuing that task
/// once all its inputs are present. Mutates `st` under its lock.
fn deliver(st: &mut State, parent: Option<(usize, usize)>, proof: TreeProof) {
    if let Some((ti, slot)) = parent {
        st.inputs[ti][slot] = Some(proof);
        st.pending[ti] -= 1;
        if st.pending[ti] == 0 {
            st.ready.push_back(ti);
        }
    }
    // No parent ⇒ root value; the root is always a Fold here (n_leaves > 1).
}

/// Drop-guard that, ONLY when its thread is unwinding from a panic, runs `set_aborted` under the
/// (poison-recovered) lock and wakes parked siblings — so a panic inside `pool.install` cannot strand
/// workers in `cv.wait` forever and hang `thread::scope` join. Fires nothing on normal drop, so the
/// normal path never sets `aborted` and proofs stay byte-identical.
struct AbortGuard<'a, F: Fn()> {
    set_aborted: F,
    cv: &'a std::sync::Condvar,
}

impl<F: Fn()> Drop for AbortGuard<'_, F> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            (self.set_aborted)();
            self.cv.notify_all();
        }
    }
}

/// Acquires the lock and runs the base-node streamer's pull predicate-loop: pop a ready task, else
/// `None` when all tasks are done or a sibling aborted, else park on `cv`. Returns with the guard
/// dropped so the caller proves off-lock. Keeps invariant 1 (re-check + wait stay under the lock).
fn next_ready(state: &std::sync::Mutex<State>, cv: &std::sync::Condvar, n_tasks: usize) -> Option<usize> {
    let mut st = state.lock().unwrap();
    loop {
        if let Some(ti) = st.ready.pop_front() {
            return Some(ti);
        }
        if st.done == n_tasks || st.aborted {
            return None;
        }
        st = cv.wait(st).unwrap();
    }
}

/// Builds the base-node streamer's initial dataflow (pure, no locks) from the fixed `tasks`: per-value
/// consumer wiring (`input_parent` for base-nodes, `node_parent` for fold outputs) and the initial
/// [`State`] (empty slots + pending counts). `m_base_nodes` = number of base-node inputs.
fn build_state(
    tasks: &[FoldTask],
    m_base_nodes: usize,
) -> (State, Vec<Option<(usize, usize)>>, Vec<Option<(usize, usize)>>) {
    // Per producible value, record which task+slot consumes it (slot = left-to-right child position,
    // so inputs reassemble in the fold's exact order) and each task's pending-child count.
    let mut input_parent: Vec<Option<(usize, usize)>> = vec![None; m_base_nodes];
    let mut node_parent: Vec<Option<(usize, usize)>> = vec![None; tasks.len()];
    let mut pending: Vec<usize> = vec![0; tasks.len()];
    let arity: Vec<usize> = tasks.iter().map(|t| t.children.len()).collect();
    for (ti, t) in tasks.iter().enumerate() {
        for (slot, ch) in t.children.iter().enumerate() {
            pending[ti] += 1;
            match ch {
                Child::Input(i) => input_parent[*i] = Some((ti, slot)),
                Child::Fold(j) => node_parent[*j] = Some((ti, slot)),
            }
        }
    }
    let state = State {
        inputs: arity.iter().map(|&k| (0..k).map(|_| None).collect()).collect(),
        pending,
        ready: std::collections::VecDeque::new(),
        done: 0,
        root: None,
        aborted: false,
    };
    (state, input_parent, node_parent)
}

/// The three job kinds the [`recursive_aggregate_prove_leaves_streaming`] coordinator schedules onto
/// one worker pool. Symmetric pull-workers off a single ready-queue, so ordering has no hazard and
/// (per the byte-identity invariant) does not affect the result.
#[derive(Clone, Copy)]
enum Job {
    /// Wrap producer input at leaf index `i` into leaf `i` (the injected AIR wrap closure).
    Wrap(usize),
    /// Prove level-0 (leaf→level1-node) group `g`. Ready when all its leaves are wrapped.
    Level1(usize),
    /// Prove tier-≥1 fold task `t` ([`build_fold_topology`]). Ready when all its children are available.
    Fold(usize),
}

/// Dataflow state shared between the coordinator and the workers. Three ready sub-queues, popped
/// Fold > Level1 > Wrap (drains sub-trees first to bound host RAM; ordering is byte-irrelevant).
struct LeavesState<W> {
    // Tier 0: pending producer inputs, per-group remaining leaf count, and resolved leaf inputs.
    wrap_inputs: Vec<Option<W>>,
    level1_remaining: Vec<usize>,
    level1_inputs: Vec<Vec<Option<TreeProof>>>,
    // Tier ≥ 1: resolved child inputs + pending child counts (as in the base-node streamer).
    fold_inputs: Vec<Vec<Option<TreeProof>>>,
    fold_pending: Vec<usize>,
    ready_fold: std::collections::VecDeque<usize>,
    ready_level1: std::collections::VecDeque<usize>,
    ready_wrap: std::collections::VecDeque<usize>,
    // Ordered leaves to return (leaf i = wrap of input streamed with index i).
    leaves_out: Vec<Option<TreeProof>>,
    done: usize,
    root: Option<TreeProof>,
    // Set by a panicking worker's drop-guard so parked siblings wake and exit (see `AbortGuard`).
    aborted: bool,
}

/// Deliver a completed fold/level1-node output into its consuming tier-≥1 task (or capture the root
/// when there is no parent). Mutates `st` under its lock.
fn deliver_node<W>(st: &mut LeavesState<W>, parent: Option<(usize, usize)>, proof: TreeProof) {
    match parent {
        Some((ti, slot)) => {
            st.fold_inputs[ti][slot] = Some(proof);
            st.fold_pending[ti] -= 1;
            if st.fold_pending[ti] == 0 {
                st.ready_fold.push_back(ti);
            }
        }
        None => st.root = Some(proof), // the root (m == 1 ⇒ level1-node 0; else the root fold task)
    }
}

/// Acquires the lock and runs the leaves streamer's pull predicate-loop, popping Fold > Level1 > Wrap;
/// else `None` when all jobs are done or a sibling aborted, else parks on `cv`. Returns with the
/// guard dropped so the caller proves off-lock. Keeps invariant 1 (re-check + wait stay under the lock).
fn next_job<W>(
    state: &std::sync::Mutex<LeavesState<W>>,
    cv: &std::sync::Condvar,
    n_jobs: usize,
) -> Option<Job> {
    let mut st = state.lock().unwrap();
    loop {
        if let Some(t) = st.ready_fold.pop_front() {
            return Some(Job::Fold(t));
        }
        if let Some(g) = st.ready_level1.pop_front() {
            return Some(Job::Level1(g));
        }
        if let Some(i) = st.ready_wrap.pop_front() {
            return Some(Job::Wrap(i));
        }
        if st.done == n_jobs || st.aborted {
            return None;
        }
        st = cv.wait(st).unwrap();
    }
}

/// Aux wiring the leaves coordinator + workers need alongside the [`LeavesState`].
struct LeavesTopo {
    /// leaf i -> (group g, slot within group), contiguous left-to-right.
    leaf_group: Vec<(usize, usize)>,
    /// level1-node g -> its consuming fold task+slot (or None if it is the root).
    level1_parent: Vec<Option<(usize, usize)>>,
    /// Fold task j -> its consuming fold task+slot (or None if it is the root).
    node_parent: Vec<Option<(usize, usize)>>,
}

/// Builds the leaves streamer's initial dataflow (pure, no locks) from the tier-0 group `sizes` and the
/// fixed tier-≥1 `tasks`: the leaf→group map, per-value consumer wiring, and the initial
/// [`LeavesState`] (empty slots + pending/remaining counts).
fn build_leaves_state<W>(sizes: &[usize], tasks: &[FoldTask], n_leaves: usize) -> (LeavesState<W>, LeavesTopo) {
    let m = sizes.len();
    // leaf i -> (group g, slot within group), contiguous left-to-right.
    let leaf_group: Vec<(usize, usize)> = sizes
        .iter()
        .enumerate()
        .flat_map(|(g, &sz)| (0..sz).map(move |s| (g, s)))
        .collect();
    debug_assert_eq!(leaf_group.len(), n_leaves);

    // Per-task readiness (as in `build_state`). Here `Child::Input(g)` denotes level1-node g.
    let mut level1_parent: Vec<Option<(usize, usize)>> = vec![None; m];
    let mut node_parent: Vec<Option<(usize, usize)>> = vec![None; tasks.len()];
    let mut fold_pending: Vec<usize> = vec![0; tasks.len()];
    let fold_arity_of: Vec<usize> = tasks.iter().map(|t| t.children.len()).collect();
    for (ti, t) in tasks.iter().enumerate() {
        for (slot, ch) in t.children.iter().enumerate() {
            fold_pending[ti] += 1;
            match ch {
                Child::Input(g) => level1_parent[*g] = Some((ti, slot)),
                Child::Fold(j) => node_parent[*j] = Some((ti, slot)),
            }
        }
    }

    let state = LeavesState::<W> {
        wrap_inputs: (0..n_leaves).map(|_| None).collect(),
        level1_remaining: sizes.to_vec(),
        level1_inputs: sizes.iter().map(|&s| (0..s).map(|_| None).collect()).collect(),
        fold_inputs: fold_arity_of.iter().map(|&a| (0..a).map(|_| None).collect()).collect(),
        fold_pending,
        ready_fold: std::collections::VecDeque::new(),
        ready_level1: std::collections::VecDeque::new(),
        ready_wrap: std::collections::VecDeque::new(),
        leaves_out: (0..n_leaves).map(|_| None).collect(),
        done: 0,
        root: None,
        aborted: false,
    };
    (state, LeavesTopo { leaf_group, level1_parent, node_parent })
}

#[cfg(test)]
#[path = "prove_streaming_tests.rs"]
mod prove_streaming_tests;
