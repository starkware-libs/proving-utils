//! In-binary N-leaf 2-to-1 multiverifier recursion tree.
//!
//! Given an ordered list of `N` leaf circuit proofs, this crate folds the entire recursion tree
//! above them into a single root proof by repeatedly proving a 2-to-1
//! [`build_multiverifier_circuit`] node on pairs of children. Each node verifies its two child
//! proofs and emits a Blake hash binding `[ppRoot_L, outs_L, ppRoot_R, outs_R]` as its own two
//! output values; that hash is what the parent node (and, at the top, the
//! [`circuit_unpacker`](https://docs.rs/circuit-unpacker)) consumes.
//!
//! Because the multiverifier *self-verifies* (a multiverifier proof has the same circuit shape as
//! the proof it verifies), a single [`SharedConfig`] built from `all_circuit_components` works for
//! every level — the leaf level and all internal levels alike — and every internal node reports
//! the same fixed `preprocessed_root` ([`AggregateConfig::node_preprocessed_root`]).
//!
//! This crate folds the multiverifier tree, then proves the **root verification**
//! ([`prove_root_verification`]) — the only published, and only zk-blinded, proof. Every
//! multiverifier proof, the root included, is internal: consumed (guessed into the witness) by the
//! next circuit up, never published; no multiverifier node is ever blinded.
//!
//! The root verification (1) runs the STARK verifier on the root multiverifier proof in-circuit,
//! and (2) **unpacks** it: it reconstructs the tree's root hash in-circuit from prover-supplied
//! per-leaf output hints — via the same per-node `blake([ppR_L, outs_L, ppR_R, outs_R])` binding
//! the nodes used — binds the reconstructed root to the verified root output, and emits the leaf
//! outputs. The unpack is inherently **O(N)** (it touches every leaf). Using one trusted
//! `leaf_preprocessed_root` for all leaves also forces them to share an AIR.
//!
//! Each leaf's output will be `H_i = blake(H_P ‖ x_i ‖ y_i)` (program commitment + input + output)
//! once gate_air leaves exist; rehashing every leaf against one shared `H_P` during the unpack is
//! what enforces same-program. With the current cairo stand-in leaves the output is just the leaf
//! circuit's `output_values`, so the unpack exercises the plumbing but not that encoding yet.
//!
//! Any `N >= 1` is supported: the fold and the unpacker both pair entries left-to-right and carry
//! an odd trailing entry up unchanged, building one deterministic unbalanced tree of real proofs
//! (no power-of-two padding, no dummies). A dynamic permutation-argument unpacker that handles an
//! arbitrary tree shape unknown at circuit-build time is a later optimization.

use std::sync::Arc;

use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_common::N_RESERVED;
use circuit_common::finalize::{
    ComponentSizes, add_zk_blinding, compute_padded_sizes, pad_context, pad_to_targets,
};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_prover::prover::{
    CircuitProof, prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
    prove_circuit_with_precompute,
};
use circuit_verifier::statement::CircuitStatement;
use circuit_verifier::verify::CircuitConfig;
use circuits::blake::{ReducedHashValue, blake2s_m31};
use circuits::context::{Context, Var};
use circuits::ops::{Guess, eq, guess};
use circuits_stark_verifier::proof::Proof;
use circuits_stark_verifier::verify::verify;
use rayon::ThreadPool;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sM31MerkleChannel, Blake2sM31MerkleHasher};
use stwo::prover::ProvingError;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::twiddles::TwiddleTree;

/// A proven node carried up the tree.
///
/// Bundles a circuit proof with the two pieces the parent multiverifier needs to reconstruct the
/// inner [`circuits::context`] statement it verifies: the preprocessed root of the circuit that
/// produced the proof, and its two output values.
#[derive(Clone)]
pub struct TreeProof {
    pub proof: Proof<QM31>,
    pub preprocessed_root: ReducedHashValue<QM31>,
    pub output_values: [QM31; N_RESERVED],
}

/// zk-blinding parameters for the root verification (the only blinded proof).
#[derive(Clone, Copy)]
pub struct ZkBlind {
    /// Seed for the ChaCha20 RNG that draws the blinding values.
    pub seed: [u8; 32],
    /// Number of blinding rows per witness component — must be the root proof's `n_queries`.
    pub n_padding: usize,
}

/// Static configuration shared by every node in the tree.
pub struct AggregateConfig {
    /// Verifier/prover config used to build and prove each 2-to-1 node. Because the multiverifier
    /// self-verifies, this single config (built from `all_circuit_components`) deserializes both
    /// the leaf proofs and the multiverifier proofs at every level.
    pub shared_config: SharedConfig,
    /// The preprocessed root of the multiverifier circuit itself — the fixed point every internal
    /// node reports as its `preprocessed_root` to its parent.
    pub node_preprocessed_root: ReducedHashValue<QM31>,
    /// The trusted preprocessed root of the leaf circuit (the same AIR for every leaf). The root
    /// verification's unpacker uses this single constant for *all* leaves, which both reconstructs
    /// the tree and forces every leaf to share this AIR (a leaf with a different `pp_root` makes
    /// the reconstruction miss the verified root).
    pub leaf_preprocessed_root: ReducedHashValue<QM31>,
    /// Padding targets applied to every node's trace. Must be identical across the tree so all
    /// nodes share one circuit shape (hence one `node_preprocessed_root`).
    pub target_padding_sizes: ComponentSizes,
    /// PCS config used to prove each node.
    pub pcs_config: PcsConfig,
    /// Witness-independent precompute for the internal multiverifier node circuit (its preprocessed
    /// circuit, committed preprocessed tree, twiddles, and column pool). All internal nodes share
    /// one fixed circuit shape, so this is built once and reused for every [`prove_node`] call,
    /// skipping the per-node interpolate + Merkle-commit of the constant (tree0) columns. `None`
    /// falls back to the self-contained [`prove_circuit_assignment`] path (rebuilds tree0 each call).
    pub node_precompute: Option<Arc<CircuitPrecompute>>,
    /// Witness-independent precompute for the leaf circuit (same AIR for every leaf). Reused for
    /// every [`prove_gate_air_leaf`] call. `None` falls back to [`prove_circuit_assignment`].
    pub leaf_precompute: Option<Arc<CircuitPrecompute>>,
}

/// Witness-independent proving precompute for one fixed circuit shape: its preprocessed circuit, the
/// twiddles, and the committed preprocessed (tree0) commitment tree, plus a shared column pool.
///
/// The preprocessed trace, its interpolation, and its Merkle commitment depend only on the circuit's
/// gate structure (constants/multiplicities), not on the witness, so for the recursion's repeated
/// fixed shapes (the multiverifier node, the leaf) they are computed once here and reused across all
/// proves via [`prove_circuit_with_precompute`] — host-resident on the [`SimdBackend`] and shared
/// (read-only) across the [`PoolSet`] workers via `Arc`.
pub struct CircuitPrecompute {
    /// The fixed preprocessed circuit (preprocessed trace + structural params) for this shape.
    pub preprocessed: PreprocessedCircuit,
    /// Twiddles sized for this shape's `trace_log_size + max(log_blowup, 1)` (the prove's largest
    /// domain), reused for both this tree and the per-proof base/interaction interpolation.
    pub twiddles: TwiddleTree<SimdBackend>,
    /// The committed preprocessed (tree0) commitment tree for this shape.
    pub tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>,
    /// Shared memory pool for the prover's SIMD columns.
    pub base_column_pool: BaseColumnPool<SimdBackend>,
    /// PCS config for proving this shape, with `lifting_log_size` pinned to the cached tree's
    /// `trace_log_size + log_blowup` (so [`prove_circuit_with_precompute`] uses the same domain the
    /// cached tree was committed over).
    pub pcs_config: PcsConfig,
}

impl CircuitPrecompute {
    /// Builds the precompute for a fixed `preprocessed` circuit shape at `log_blowup_factor`,
    /// mirroring exactly what [`prove_circuit_assignment`] would build internally (same column order,
    /// `store_polynomials_coefficients = true`, `lifting_log_size = trace_log_size + log_blowup`,
    /// twiddles over `trace_log_size + max(log_blowup, 1)`).
    ///
    /// SOUNDNESS GUARD: asserts once, at build time, that the freshly committed tree's root equals
    /// the already-trusted `expected_root`. Because every later prove reuses this same tree, this one
    /// check transfers the trust in `expected_root` to all of them; a mismatch (wrong column order /
    /// blowup / shape) aborts before any proof is produced.
    ///
    /// `pcs_config` is the prove config for this shape (pow/n_queries/blowup); its `lifting_log_size`
    /// is (re)pinned to `trace_log_size + log_blowup` to match the cached tree.
    pub fn new(
        preprocessed: PreprocessedCircuit,
        pcs_config: PcsConfig,
        expected_root: ReducedHashValue<QM31>,
    ) -> Self {
        let log_blowup_factor = pcs_config.fri_config.log_blowup_factor;
        let trace_log_size = preprocessed.trace_log_size;
        let lifting_log_size = trace_log_size + log_blowup_factor;
        let pcs_config = PcsConfig {
            lifting_log_size: Some(lifting_log_size),
            ..pcs_config
        };
        let base_column_pool = BaseColumnPool::<SimdBackend>::new();

        // Match `prove_circuit_assignment`'s twiddle domain: max(blowup, composition degree bound=1).
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(trace_log_size + log_blowup_factor.max(1))
                .circle_domain()
                .half_coset,
        );

        let preprocessed_trace = preprocessed.preprocessed_trace.get_trace::<SimdBackend>();
        let preprocessed_trace_polys =
            SimdBackend::interpolate_columns(preprocessed_trace, &twiddles);
        let tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
            preprocessed_trace_polys,
            log_blowup_factor,
            &twiddles,
            true,
            Some(lifting_log_size),
            &base_column_pool,
        );

        let root: ReducedHashValue<QM31> = tree.commitment.root().into();
        assert_eq!(
            root, expected_root,
            "precomputed preprocessed (tree0) root must equal the trusted preprocessed_root \
             (column order / log_blowup / shape mismatch)"
        );

        Self {
            preprocessed,
            twiddles,
            tree,
            base_column_pool,
            pcs_config,
        }
    }
}

/// Result of folding the tree.
pub struct AggregateOutput {
    /// The single root proof, with its preprocessed root and output values.
    pub root: TreeProof,
    /// Number of recursion levels above the leaves (`ceil(log2(n_leaves))`).
    pub n_levels: usize,
}

/// A fixed set of rayon thread pools for partitioning prove work across the cores of a *single*
/// machine.
///
/// Each prove already saturates rayon's default global pool (stwo's NTT/Merkle/FRI loops fan over
/// all logical CPUs), so running independent proves on the *same* pool just makes them contend. A
/// [`PoolSet`] of `K` pools with `M` threads each lets `K` proves run concurrently, one per pool,
/// each confined to its own `M` cores (via [`ThreadPool::install`]) — turning the tree's
/// independent leaves / sibling nodes into real single-machine speedup when per-prove scaling
/// plateaus below the full core count.
///
/// Build it once and reuse it for every level (pool creation spawns OS threads, so it is not free).
pub struct PoolSet {
    pools: Vec<Arc<ThreadPool>>,
}

impl PoolSet {
    /// Creates `n_pools` pools of `threads_per_pool` worker threads each. On a 96-core machine with
    /// a measured sweet spot of 48 threads/prove, use `PoolSet::new(2, 48)`.
    pub fn new(n_pools: usize, threads_per_pool: usize) -> Self {
        let pools = (0..n_pools.max(1))
            .map(|_| {
                Arc::new(
                    rayon::ThreadPoolBuilder::new()
                        .num_threads(threads_per_pool)
                        .build()
                        .expect("build rayon pool"),
                )
            })
            .collect();
        Self { pools }
    }

    /// Number of pools (the max concurrency this set can run).
    pub fn n_pools(&self) -> usize {
        self.pools.len()
    }

    /// Runs `jobs` across the pools, preserving input order. Jobs are assigned round-robin to pools
    /// and the pools run concurrently, so up to `n_pools()` jobs are in flight at once; each job's
    /// internal rayon work runs on its assigned pool. A single job runs on the global pool (all
    /// cores) — there is nothing to run alongside it, so it should use the whole machine.
    pub fn map<T, F>(&self, jobs: Vec<F>) -> Vec<T>
    where
        F: FnOnce() -> T + Send,
        T: Send,
    {
        if jobs.len() <= 1 {
            return jobs.into_iter().map(|f| f()).collect();
        }
        let k = self.pools.len();
        let mut buckets: Vec<Vec<(usize, F)>> = (0..k).map(|_| Vec::new()).collect();
        for (i, f) in jobs.into_iter().enumerate() {
            buckets[i % k].push((i, f));
        }
        let n: usize = buckets.iter().map(Vec::len).sum();
        let mut slots: Vec<Option<T>> = (0..n).map(|_| None).collect();
        std::thread::scope(|s| {
            let handles: Vec<_> = buckets
                .into_iter()
                .zip(self.pools.iter())
                .map(|(bucket, pool)| {
                    s.spawn(move || {
                        bucket
                            .into_iter()
                            .map(|(i, f)| (i, pool.install(f)))
                            .collect::<Vec<(usize, T)>>()
                    })
                })
                .collect();
            for h in handles {
                for (i, r) in h.join().expect("pool job panicked") {
                    slots[i] = Some(r);
                }
            }
        });
        slots.into_iter().map(Option::unwrap).collect()
    }
}

/// Folds `leaves` into a single root proof by repeatedly proving 2-to-1 multiverifier nodes.
///
/// Any `N >= 1` is supported: each level pairs entries left-to-right and an odd trailing entry is
/// **carried up unchanged** to the next level, so the tree is an unbalanced binary tree of real
/// proofs — no power-of-two padding, no dummies. (A carried leaf paired with an internal node at a
/// higher level is fine: `prove_node` verifies each child under its own `preprocessed_root`, and
/// leaf and node proofs share one circuit shape.)
///
/// Sibling pairs at each level are independent and are proved concurrently across `pools` (a lone
/// pair — e.g. the last fold step — runs on the full machine).
///
/// # Panics
/// If `leaves` is empty.
pub fn recursive_aggregate_prove(
    leaves: Vec<TreeProof>,
    config: &AggregateConfig,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!leaves.is_empty(), "need at least one leaf");

    let mut level = leaves;
    let mut n_levels = 0usize;
    while level.len() > 1 {
        // Carry an odd trailing entry up unchanged; pair the rest. Prove the pairs concurrently
        // across the pools; a single pair runs on the full machine.
        let carry = if level.len() % 2 == 1 {
            level.pop()
        } else {
            None
        };
        let jobs: Vec<_> = level
            .chunks(2)
            .map(|pair| move || prove_node(&pair[0], &pair[1], config))
            .collect();
        let mut next = pools.map(jobs);
        if let Some(c) = carry {
            next.push(c);
        }
        level = next;
        n_levels += 1;
    }

    AggregateOutput {
        root: level.into_iter().next().unwrap(),
        n_levels,
    }
}

/// A reference to one input of a streaming fold node: either a base/leaf proof (by shard index, the
/// canonical arrival order) or the output of an earlier fold node (by node index).
#[derive(Clone, Copy)]
enum Child {
    Leaf(usize),
    Node(usize),
}

/// One 2-to-1 fold in the fixed tree: `prove_node(a, b)`, with `a` the left child and `b` the right.
struct FoldTask {
    a: Child,
    b: Child,
    /// Height above the leaves of this node's output (leaves are height 0).
    height: usize,
}

/// Computes the FIXED fold topology for `n_leaves`, decided up front and independent of completion
/// order, **byte-identical** to the tree [`recursive_aggregate_prove`]'s level loop builds.
///
/// It runs the level loop's algorithm over *indices* instead of proofs: each level pairs entries
/// left-to-right into `prove_node(pair[0], pair[1])` and carries an odd trailing entry up unchanged.
/// The returned `Vec<FoldTask>` is in the same order the level loop would prove them (level by level,
/// left to right); the returned [`Child`] is the root (a `Node` for `n_leaves > 1`, else `Leaf(0)`).
///
/// Equivalent to the binary-counter merge (push leaf at height 0, fold equal-height tops, then
/// finish-from-smallest) the inline streaming MVP used, but materialized explicitly so the scheduler
/// can dispatch folds eagerly. The left/right child order matches `prove_node(&pair[0], &pair[1])`
/// exactly, so each node sees the same `(a, b)` inputs as the sequential fold ⇒ same proof bytes.
fn build_fold_topology(n_leaves: usize) -> (Vec<FoldTask>, Child) {
    if n_leaves == 1 {
        return (Vec::new(), Child::Leaf(0));
    }
    let mut tasks: Vec<FoldTask> = Vec::with_capacity(n_leaves - 1);
    // Current level as (height, child-ref), mirroring the level loop's `Vec<TreeProof>`.
    let mut level: Vec<(usize, Child)> = (0..n_leaves).map(|i| (0, Child::Leaf(i))).collect();
    while level.len() > 1 {
        let carry = if level.len() % 2 == 1 {
            level.pop()
        } else {
            None
        };
        let mut next: Vec<(usize, Child)> = Vec::with_capacity(level.len() / 2 + 1);
        for pair in level.chunks(2) {
            let (ha, a) = pair[0];
            let (hb, b) = pair[1];
            let idx = tasks.len();
            let height = ha.max(hb) + 1;
            tasks.push(FoldTask { a, b, height });
            next.push((height, Child::Node(idx)));
        }
        if let Some(c) = carry {
            next.push(c);
        }
        level = next;
    }
    (tasks, level[0].1)
}

/// Streaming variant of [`recursive_aggregate_prove`]: folds leaves as they arrive over a channel,
/// dispatching each fold to a [`PoolSet`] worker the instant both its children are ready — so the
/// fold/recursion runs concurrently with (and overlaps) the base-proof producer that feeds `rx`.
///
/// This exists so the GPU base-proving producer can overlap with the CPU leaf-wrap + fold consumer
/// (see the `GATE_AIR_PIPELINE` path in gate-air-leaf). The base producer is modelled as a stream of
/// completed leaf proofs sent over `rx` in **canonical shard order** (leaf `i` is the `i`-th
/// `recv()`), NOT as GPU calls — this crate stays leaf-type-agnostic.
///
/// BYTE-IDENTITY: the result is byte-identical to [`recursive_aggregate_prove`] for the same ordered
/// leaves. The topology is FIXED up front by [`build_fold_topology`] (the level loop's balanced+carry
/// tree, e.g. for N=7 the root is `node(node(node(0,1),node(2,3)), node(node(4,5),6))`) and does not
/// depend on completion order; every [`FoldTask`] sees the same `(a, b)` left/right inputs the
/// sequential fold gives its matching `prove_node`. Because [`prove_node`] is a pure function of
/// `(a, b)`, identical topology + identical per-node inputs ⇒ identical root proof and
/// `recursion_fingerprint`, which the unchanged [`prove_root_verification`] unpacker still binds.
///
/// Streaming schedule: one coordinator owns the dataflow state; `pools.n_pools()` workers (one per
/// pool) pull ready folds and run `prove_node` via [`ThreadPool::install`] (so each fold gets its own
/// pool's cores, matching the sequential fold's per-prove parallelism). As leaves arrive on `rx`,
/// any fold whose two children are now available becomes ready; a fold completing makes its parent's
/// child available in turn. Up to `n_pools()` folds run at once while later leaves are still being
/// produced. Folds never starve: the tree is CPU-fold-bound, so a backlog of ready folds always
/// exists once base proofs outpace the single CPU consumer.
///
/// Consumes exactly `n_leaves` from `rx` in arrival order. Returns the same [`AggregateOutput`] as
/// the level loop (root + `n_levels = ceil(log2(n_leaves))`). For `n_leaves == 1` returns the single
/// leaf as root with `n_levels = 0`.
///
/// # Panics
/// If `n_leaves == 0`, or if `rx` yields fewer than `n_leaves` entries.
pub fn recursive_aggregate_prove_streaming(
    rx: std::sync::mpsc::Receiver<TreeProof>,
    n_leaves: usize,
    config: &AggregateConfig,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(n_leaves >= 1, "need at least one leaf");

    let (tasks, root_ref) = build_fold_topology(n_leaves);

    if n_leaves == 1 {
        let root = rx.recv().expect("streaming fold: missing leaf 0");
        return AggregateOutput { root, n_levels: 0 };
    }

    // For each task, count its not-yet-available children and record which task consumes each
    // produced value, so completing a fold (or receiving a leaf) can decrement the right parent.
    //   parent_of[Leaf i] / parent_of_node[Node j] = Some((task_idx, slot)), slot 0=a, 1=b.
    let mut leaf_parent: Vec<Option<(usize, u8)>> = vec![None; n_leaves];
    let mut node_parent: Vec<Option<(usize, u8)>> = vec![None; tasks.len()];
    let mut pending: Vec<u8> = vec![0; tasks.len()];
    for (ti, t) in tasks.iter().enumerate() {
        for (slot, ch) in [(0u8, t.a), (1u8, t.b)] {
            pending[ti] += 1;
            match ch {
                Child::Leaf(i) => leaf_parent[i] = Some((ti, slot)),
                Child::Node(j) => node_parent[j] = Some((ti, slot)),
            }
        }
    }

    // Dataflow state shared between the coordinator and the worker threads.
    struct State {
        // Resolved (a, b) inputs for each task, filled as children become available.
        inputs: Vec<[Option<TreeProof>; 2]>,
        pending: Vec<u8>,
        ready: std::collections::VecDeque<usize>,
        done: usize,
        // The root proof, captured when the root fold (the one with no parent) completes.
        root: Option<TreeProof>,
    }
    let n_tasks = tasks.len();
    let state = std::sync::Mutex::new(State {
        inputs: (0..n_tasks).map(|_| [None, None]).collect(),
        pending,
        ready: std::collections::VecDeque::new(),
        done: 0,
        root: None,
    });
    // Signalled when a fold becomes ready or all folds are done (so idle workers wake up).
    let cv = std::sync::Condvar::new();

    // Records that `proof` is the value of `child`, wiring it into the consuming task and enqueuing
    // that task if both its inputs are now present. Returns nothing; mutates `st` under its lock.
    let deliver = |st: &mut State, parent: Option<(usize, u8)>, proof: TreeProof| {
        if let Some((ti, slot)) = parent {
            st.inputs[ti][slot as usize] = Some(proof);
            st.pending[ti] -= 1;
            if st.pending[ti] == 0 {
                st.ready.push_back(ti);
            }
        }
        // No parent ⇒ this is the root value; the root is always a Node here (n_leaves > 1).
    };

    let n_workers = pools.n_pools().max(1);
    std::thread::scope(|s| {
        // Workers: one per pool. Each pulls a ready task, proves it on its pool's cores, then
        // delivers the result to the parent and signals.
        for pool in pools.pools.iter().take(n_workers) {
            let state = &state;
            let cv = &cv;
            let deliver = &deliver;
            let node_parent = &node_parent;
            s.spawn(move || {
                loop {
                    let ti = {
                        let mut st = state.lock().unwrap();
                        loop {
                            if let Some(ti) = st.ready.pop_front() {
                                break ti;
                            }
                            if st.done == n_tasks {
                                return;
                            }
                            st = cv.wait(st).unwrap();
                        }
                    };
                    // Take ownership of this task's resolved inputs and prove off-lock. Both child
                    // `TreeProof`s are `take()`n out of `inputs` here, so once this node's result is
                    // delivered to its parent the two children have no remaining references and are
                    // freed (dropped when `a`/`b` leave scope). Nothing retains proved node proofs:
                    // peak host memory therefore holds only the N leaves (owned by the caller for
                    // `prove_root_verification`) + the O(log N) in-flight fold path, never all N-1
                    // node proofs.
                    let (a, b) = {
                        let mut st = state.lock().unwrap();
                        let ins = &mut st.inputs[ti];
                        (ins[0].take().unwrap(), ins[1].take().unwrap())
                    };
                    let result = pool.install(|| prove_node(&a, &b, config));
                    {
                        let mut st = state.lock().unwrap();
                        match node_parent[ti] {
                            Some(parent) => deliver(&mut st, Some(parent), result),
                            None => st.root = Some(result), // the root fold (no parent)
                        }
                        st.done += 1;
                        // Wake idle workers: either a new fold is ready, or all folds are done.
                        cv.notify_all();
                    }
                }
            });
        }

        // Coordinator: drain leaves in canonical shard order, delivering each to its consumer. A
        // leaf that completes a fold's inputs enqueues it; workers pick it up immediately, so folds
        // overlap with the still-arriving later leaves.
        for i in 0..n_leaves {
            let leaf = rx
                .recv()
                .expect("streaming fold: fewer leaves than n_leaves");
            let mut st = state.lock().unwrap();
            deliver(&mut st, leaf_parent[i], leaf);
            cv.notify_all();
        }
    });

    // All folds complete; pull the root the root fold captured.
    let root_idx = match root_ref {
        Child::Node(j) => j,
        Child::Leaf(_) => unreachable!("n_leaves > 1 ⇒ root is a fold node"),
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

/// The published root-verification proof.
pub struct RootVerificationOutput {
    /// The root verification's STARK proof — the single public artifact of the whole aggregation.
    pub proof: Proof<QM31>,
    /// The unpacked leaf outputs, in tree-position order — the result the proof exposes.
    pub leaf_outputs: Vec<[QM31; N_RESERVED]>,
    /// The root-verification circuit's trace log size (from which its PCS config was derived).
    pub trace_log_size: u32,
}

/// Builds and proves the **root verification** — the only published, only zk-blinded proof.
///
/// In-circuit it (1) reconstructs the root multiverifier statement and runs the STARK verifier on
/// the root proof, then (2) **unpacks**: it guesses each leaf's `output_values`, reconstructs the
/// tree's root hash via the same per-node `blake([ppR_L, outs_L, ppR_R, outs_R])` binding the nodes
/// used (with one trusted `leaf_preprocessed_root` for every leaf and `node_preprocessed_root` for
/// internal nodes), `eq`-binds the reconstructed root to the verified root output, and (3) emits
/// the leaf outputs as public outputs. The unpack is **O(N)** — it touches every leaf — and using
/// one `leaf_preprocessed_root` for all leaves forces them to share an AIR.
///
/// `leaves` must be the same ordered leaves passed to [`recursive_aggregate_prove`] and `root` its
/// returned root (any `N >= 1`); the unpacker reconstructs the same carry-odd shape the fold built.
/// The circuit's own prove config is derived from its actual trace size.
///
/// If `zk_blind` is `Some`, the circuit is zk-blinded before proving — this is where hiding lives,
/// since this is the only published proof and its trace transitively encodes the whole tree.
pub fn prove_root_verification(
    root: &TreeProof,
    leaves: &[TreeProof],
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_blind: Option<ZkBlind>,
) -> RootVerificationOutput {
    let n = leaves.len();
    assert!(!leaves.is_empty());

    // Exposes every leaf's N_RESERVED outputs.
    let mut context = Context::<QM31>::new(n * N_RESERVED);

    // (1) Verify the root multiverifier proof in-circuit.
    let circuit_config = CircuitConfig {
        config: config.pcs_config,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: config.shared_config.preprocessed_column_log_sizes.clone(),
        preprocessed_root: root.preprocessed_root,
    };
    let statement = CircuitStatement::new(&mut context, &circuit_config, &root.output_values);
    let proof_vars = root.proof.guess(&mut context);
    verify(
        &mut context,
        &proof_vars,
        &config.shared_config.proof_config,
        &statement,
    );
    let root_out_vars: Vec<Var> = statement.get_output_values().to_vec();

    // (2) Unpack: reconstruct the tree root from guessed leaf outputs and bind it to the verified
    //     root. One trusted leaf_preprocessed_root for every leaf (forces a shared AIR); produced
    //     internal nodes report node_preprocessed_root.
    let leaf_pp = ReducedHashValue(
        context.constant(config.leaf_preprocessed_root.0),
        context.constant(config.leaf_preprocessed_root.1),
    );
    let node_pp = ReducedHashValue(
        context.constant(config.node_preprocessed_root.0),
        context.constant(config.node_preprocessed_root.1),
    );
    let mut leaf_output_vars: Vec<Vec<Var>> = Vec::with_capacity(n);
    let mut level: Vec<(ReducedHashValue<Var>, Vec<Var>)> = leaves
        .iter()
        .map(|l| {
            let outs: Vec<Var> = l
                .output_values
                .iter()
                .map(|v| guess(&mut context, *v))
                .collect();
            leaf_output_vars.push(outs.clone());
            (leaf_pp, outs)
        })
        .collect();
    while level.len() > 1 {
        // Carry an odd trailing entry up unchanged (keeping its own preprocessed root), exactly as
        // the fold does, so the reconstructed shape matches the verified root for any N.
        let carry = if level.len() % 2 == 1 {
            level.pop()
        } else {
            None
        };
        let mut next = Vec::with_capacity(level.len() / 2 + 1);
        let mut iter = level.into_iter();
        while let (Some(a), Some(b)) = (iter.next(), iter.next()) {
            let preimage = vec![a.0.0, a.0.1, a.1[0], a.1[1], b.0.0, b.0.1, b.1[0], b.1[1]];
            let h = blake2s_m31(&mut context, &preimage, 16 * preimage.len());
            next.push((node_pp, vec![h.0, h.1]));
        }
        if let Some(c) = carry {
            next.push(c);
        }
        level = next;
    }
    let computed_root = &level[0].1;
    eq(&mut context, computed_root[0], root_out_vars[0]);
    eq(&mut context, computed_root[1], root_out_vars[1]);

    // (3) Emit the unpacked leaf outputs as public outputs.
    let flat_outputs: Vec<Var> = leaf_output_vars.iter().flatten().copied().collect();
    context.set_outputs(&flat_outputs);

    // (4) Finalize, (optionally) blind, pad to power-of-two sizes, derive prove config, prove.
    //     Blinding runs before padding so the extra rows are absorbed into the padding.
    let mut context = context.finalize(false);
    context.validate_circuit();
    if let Some(zk) = zk_blind {
        add_zk_blinding(&mut context, zk.seed, zk.n_padding);
        context.validate_circuit();
    }
    pad_context(&mut context);
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
    let (proof, _public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    RootVerificationOutput {
        proof,
        leaf_outputs: leaves.iter().map(|l| l.output_values).collect(),
        trace_log_size,
    }
}

/// Proves a padded circuit's `values` against a prebuilt witness-independent [`CircuitPrecompute`],
/// reusing its committed preprocessed (tree0) tree and twiddles instead of rebuilding them.
fn prove_with_precompute(
    values: &[QM31],
    pc: &CircuitPrecompute,
) -> Result<CircuitProof<Blake2sM31MerkleHasher>, ProvingError> {
    prove_circuit_with_precompute::<Blake2sM31MerkleChannel>(
        &pc.base_column_pool,
        &pc.twiddles,
        &pc.preprocessed,
        MaybeOwned::Borrowed(&pc.tree),
        values,
        pc.pcs_config,
    )
}

/// Proves one 2-to-1 node verifying children `a` and `b`.
fn prove_node(a: &TreeProof, b: &TreeProof, config: &AggregateConfig) -> TreeProof {
    let _t_node = std::time::Instant::now();
    let input = |c: &TreeProof| MultiverifierInput {
        proof: c.proof.clone(),
        preprocessed_root: c.preprocessed_root,
        output_values: c.output_values,
    };

    let mut context =
        build_multiverifier_circuit::<QM31>(input(a), input(b), &config.shared_config);
    pad_to_targets(&mut context, config.target_padding_sizes.clone());
    context.validate_circuit();

    let circuit_proof = match &config.node_precompute {
        Some(pc) => prove_with_precompute(context.values(), pc),
        None => {
            let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
            prove_circuit_assignment(
                context.values(),
                &preprocessed,
                &BaseColumnPool::<SimdBackend>::new(),
                config.pcs_config,
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
        "recursive_aggregate: MEASURE t_node={:.3}s",
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: config.node_preprocessed_root,
        output_values,
    }
}

// ---------------------------------------------------------------------------
// Config-derivation helpers (general): build an `AggregateConfig` whose multiverifier verifies
// leaves of a given circuit's config. Replicate stwo-circuits' test-only helpers (not exported).
// ---------------------------------------------------------------------------

use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuits::ivalue::NoValue;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use num_traits::Zero;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::poly::circle::PolyOps;

/// Merkle root of a circuit's preprocessed trace.
pub fn preprocessed_root(
    preprocessed: &PreprocessedCircuit,
    log_blowup_factor: u32,
) -> ReducedHashValue<QM31> {
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

/// Builds + preprocesses the NoValue multiverifier node circuit for a given `shared` config (the one
/// a node is proved with) padded to `target_padding`. This is the fixed shape every internal node
/// proves, so its [`PreprocessedCircuit`] is the one to cache in a node [`CircuitPrecompute`].
///
/// Mirrors the node-shape construction inside [`multiverifier_node_preprocessed`], but keyed on the
/// already-built `SharedConfig` (so a caller holding only a [`AggregateConfig`] can rebuild the cache
/// without the leaf's `PreprocessedCircuit`).
pub fn node_preprocessed_from_shared(
    shared: &SharedConfig,
    target_padding: ComponentSizes,
) -> PreprocessedCircuit {
    // Build the same node circuit `prove_node` does, with NoValue witnesses (the preprocessed trace
    // is witness-independent). The verification topology is sized from a NoValue `proof_config` over
    // the shared `n_preprocessed_columns`, mirroring stwo-circuits' node-shape construction.
    let proof_config = ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        shared.proof_config.n_preprocessed_columns,
        &shared.pcs_config,
        INTERACTION_POW_BITS,
    );
    let node_shared = SharedConfig {
        pcs_config: shared.pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: shared.preprocessed_column_log_sizes.clone(),
    };
    let empty = || MultiverifierInput {
        proof: empty_proof(&proof_config),
        preprocessed_root: ReducedHashValue(QM31::zero(), QM31::zero()),
        output_values: [QM31::zero(); N_RESERVED],
    };
    let mut ctx = build_multiverifier_circuit::<NoValue>(empty(), empty(), &node_shared);
    pad_to_targets(&mut ctx, target_padding);
    PreprocessedCircuit::preprocess_circuit(&mut ctx)
}

/// Builds + preprocesses the NoValue multiverifier node that verifies two leaves of
/// `leaf_preprocessed`'s config (optionally padded), to recompute the node's `preprocessed_root`
/// and component sizes for a given leaf circuit. Also returns the node's *unpadded* component sizes
/// (for deriving the shared `TARGET_PADDING_SIZES = max(leaf, node)`).
pub fn multiverifier_node_preprocessed(
    leaf_preprocessed: &PreprocessedCircuit,
    pcs_config: PcsConfig,
    target_padding: Option<ComponentSizes>,
) -> (PreprocessedCircuit, ComponentSizes) {
    let proof_config = ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        leaf_preprocessed.preprocessed_trace.n_columns(),
        &pcs_config,
        INTERACTION_POW_BITS,
    );
    let shared = SharedConfig {
        pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: leaf_preprocessed.preprocessed_trace.log_sizes(),
    };
    let empty = || MultiverifierInput {
        proof: empty_proof(&proof_config),
        preprocessed_root: ReducedHashValue(QM31::zero(), QM31::zero()),
        output_values: [QM31::zero(); N_RESERVED],
    };
    let mut ctx = build_multiverifier_circuit::<NoValue>(empty(), empty(), &shared);
    let unpadded_sizes = compute_padded_sizes(&ctx);
    if let Some(t) = target_padding {
        pad_to_targets(&mut ctx, t);
    }
    (
        PreprocessedCircuit::preprocess_circuit(&mut ctx),
        unpadded_sizes,
    )
}

#[cfg(test)]
mod topology_tests {
    use super::{Child, build_fold_topology};

    /// A symbolic tree shape, leaf-index aware — the byte-identity-relevant structure of a fold tree
    /// (which leaf/node is each node's left vs right child, and the resulting nesting).
    #[derive(PartialEq, Eq, Debug)]
    enum Shape {
        Leaf(usize),
        Node(Box<Shape>, Box<Shape>),
    }

    /// The shape `recursive_aggregate_prove`'s level loop builds, computed over indices — the exact
    /// `prove_node(&pair[0], &pair[1])` pairing with an odd trailing entry carried up unchanged.
    fn sequential_shape(n: usize) -> Shape {
        let mut level: Vec<Shape> = (0..n).map(Shape::Leaf).collect();
        while level.len() > 1 {
            let carry = if level.len() % 2 == 1 {
                level.pop()
            } else {
                None
            };
            let mut next = Vec::with_capacity(level.len() / 2 + 1);
            let mut iter = level.into_iter();
            while let (Some(a), Some(b)) = (iter.next(), iter.next()) {
                next.push(Shape::Node(Box::new(a), Box::new(b)));
            }
            if let Some(c) = carry {
                next.push(c);
            }
            level = next;
        }
        level.into_iter().next().unwrap()
    }

    /// The shape the streaming scheduler realizes, reconstructed from `build_fold_topology`'s task
    /// list + root reference. Each task's `(a, b)` children resolve to the same `Shape` nodes,
    /// proving the streaming dataflow folds the identical tree with the identical left/right inputs.
    fn streaming_shape(n: usize) -> Shape {
        let (tasks, root) = build_fold_topology(n);
        fn resolve(c: Child, tasks: &[super::FoldTask]) -> Shape {
            match c {
                Child::Leaf(i) => Shape::Leaf(i),
                Child::Node(j) => Shape::Node(
                    Box::new(resolve(tasks[j].a, tasks)),
                    Box::new(resolve(tasks[j].b, tasks)),
                ),
            }
        }
        resolve(root, &tasks)
    }

    /// The streamed tree is byte-identical to the sequential one because it has the IDENTICAL shape:
    /// same nesting, same leaf-index-to-(left/right)-slot assignment for every node. Since
    /// `prove_node` is a pure function of `(a, b)`, identical shape + identical per-node inputs ⇒
    /// identical proof bytes and `recursion_fingerprint`. Checks every N up to 130 (covers all
    /// odd-carry cases and several power-of-two boundaries) plus the doc's N=7 example.
    #[test]
    fn streaming_topology_matches_sequential() {
        for n in 1..=130usize {
            assert_eq!(
                streaming_shape(n),
                sequential_shape(n),
                "fold topology diverges from the level loop at n={n}"
            );
        }
    }

    /// Pins the documented N=7 root: node(node(node(0,1),node(2,3)), node(node(4,5),6)).
    #[test]
    fn streaming_topology_n7_example() {
        use Shape::{Leaf, Node};
        let n = |a: Shape, b: Shape| Node(Box::new(a), Box::new(b));
        let expected = n(
            n(n(Leaf(0), Leaf(1)), n(Leaf(2), Leaf(3))),
            n(n(Leaf(4), Leaf(5)), Leaf(6)),
        );
        assert_eq!(streaming_shape(7), expected);
    }

    /// Every fold tree over N>1 leaves has exactly N-1 internal nodes; the root height equals
    /// ceil(log2(N)) (the level loop's `n_levels`).
    #[test]
    fn topology_node_count_and_height() {
        for n in 2..=130usize {
            let (tasks, root) = build_fold_topology(n);
            assert_eq!(tasks.len(), n - 1, "n={n}: expected N-1 folds");
            let h = match root {
                Child::Node(j) => tasks[j].height,
                Child::Leaf(_) => 0,
            };
            let expected_levels = (usize::BITS - (n - 1).leading_zeros()) as usize;
            assert_eq!(h, expected_levels, "n={n}: root height = ceil(log2 N)");
        }
    }
}
