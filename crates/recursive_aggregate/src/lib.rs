//! In-binary N-leaf `k`-to-1 multiverifier recursion tree.
//!
//! Given an ordered list of `N` leaf circuit proofs, this crate folds the entire recursion tree
//! above them into a single root proof by repeatedly proving a `FOLD_ARITY`-to-1
//! [`build_multiverifier_circuit`] node on groups of `k` children. Each node verifies its `k` child
//! proofs and emits a Blake hash binding `[ppRoot_i, outs_i for i in 0..k]` (children left-to-right)
//! as its own `N_RESERVED` (eight) output digest words; that hash is what the parent node (and, at
//! the top, the [`circuit_unpacker`](https://docs.rs/circuit-unpacker)) consumes. As of stwo #1425
//! the preprocessed root is the full eight-word Blake2s digest (`HashValue`), not the old reduced
//! two-QM31 form, and the node preimage is hashed with `blake2s_u32s`.
//!
//! Arity is the named constant [`FOLD_ARITY`]. Every full-`k` node is exactly-`k` (full-`k` nodes at
//! a level share one precompute / `preprocessed_root`); SHORT nodes (the level-0 leaf-remainder
//! groups and the ROOT) are `m`-child with `m ∈ 2..=k` — their arity, and hence circuit shape and
//! `preprocessed_root`, is a deterministic function of the public `N` alone, never prover-chosen.
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
//! per-leaf output hints — via the same per-node `blake2s_u32s([ppR_i words, outs_i words] for the
//! k children)` binding the nodes used — binds the reconstructed root to the verified root output,
//! and emits the leaf
//! outputs. The unpack is inherently **O(N)** (it touches every leaf). Using one trusted
//! `leaf_preprocessed_root` for all leaves also forces them to share an AIR.
//!
//! Each leaf's output will be `H_i = blake(H_P ‖ x_i ‖ y_i)` (program commitment + input + output)
//! once gate_air leaves exist; rehashing every leaf against one shared `H_P` during the unpack is
//! what enforces same-program. With the current cairo stand-in leaves the output is just the leaf
//! circuit's `output_values`, so the unpack exercises the plumbing but not that encoding yet.
//!
//! Any `N >= 1` is supported via a two-phase deterministic fold (byte-identical in the sequential
//! and streaming paths, and reconstructed identically by the unpacker):
//!   - **Level 0** consumes ALL `N` leaves into height-1 leaf-verifying nodes (arities from
//!     `level0_group_sizes`, each `2..=k`, never a lone leaf). This is the LEAF↔NODE DECOUPLING FIX:
//!     leaves (lift24) and nodes (lift25) differ in proof shape, so a carried-up leaf under a
//!     height-≥2 (lift25) fold panics the in-circuit Merkle height check. Consuming every leaf at
//!     level 0 guarantees no leaf ever survives above height 1.
//!   - **Levels ≥ 1** group the height-1 nodes left-to-right into exactly-`k` node-verifying nodes,
//!     carry the `< k` remainder up unchanged (carrying a NODE is safe — all are lift25), and fold a
//!     final `2..=k` level into the (possibly short) root. Every height-≥2 fold is homogeneous.
//! One deterministic unbalanced `k`-ary tree of real proofs (no power-of-`k` padding, no dummies). A
//! dynamic permutation-argument unpacker that handles an arbitrary tree shape unknown at
//! circuit-build time is a later optimization.

use std::sync::Arc;

/// Fold arity `k`: each internal node verifies exactly this many children (`k`-to-1 fold).
///
/// This is the single source of truth for the arity across the whole recursion pipeline — the
/// tree/streaming fold, the topology, `prove_node`, and (critically) the unpacker's per-node hash
/// preimage in [`prove_root_verification`] all read it, so the out-of-circuit unpacker and the
/// in-circuit node hash ([`build_multiverifier_circuit`]) stay byte-identical. Re-sweep the arity
/// (e.g. `4` vs `8`) by changing only this constant; nothing else hard-codes the child count.
///
/// A level's `len() % FOLD_ARITY` (< k) remainder is carried up unchanged (mirroring the old
/// carry-one), so nodes are always exactly `k` children — never variable-child.
pub const FOLD_ARITY: usize = 8;

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
use circuit_verifier::verify::{CircuitConfig, CircuitPublicData, verify_circuit};
use circuits::blake::{HashValue, blake2s_u32s, unpack_qm31s_to_u32_words};
use circuits::wrappers::U32Wrapper;
use circuits::context::{Context, FinalizedContext, Var};
use circuits::ops::{Guess, eq, guess};
use circuits_stark_verifier::proof::Proof;
use circuits_stark_verifier::verify::verify;
use rayon::ThreadPool;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sM31MerkleChannel, Blake2sMerkleHasher};
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
    pub preprocessed_root: HashValue<QM31>,
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
///
/// LEAF↔NODE PADDING DECOUPLING (the k-ary salvage): the leaf is padded to its OWN
/// `leaf_target_padding_sizes` (its natural ~2^20), NOT dragged up to the k-child node size, so
/// `t_leaf` stays pinned across `FOLD_ARITY`. Because the multiverifier self-verifies, decoupling
/// creates two full-`k` node shapes / two trusted roots, selected by the node's level (a public
/// function of `N` via [`FoldTask::height`]), never authenticated inputs:
///   - **R1** ([`level1_preprocessed_root`]) — height-1 full-`k` nodes, which verify `FOLD_ARITY`
///     LEAVES (child config [`leaf_shared_config`], the leaf's ~2^20 shape).
///   - **R2** ([`node_preprocessed_root`]) — height-≥2 full-`k` nodes, which verify `FOLD_ARITY`
///     NODES (child config [`node_shared_config`], the multiverifier's own shape — the
///     self-verifying fixed point).
/// SHORT nodes (arity `2..=k-1`: the level-0 leaf-remainder groups and the short root) have a
/// structurally different circuit ⇒ a DISTINCT preprocessed root per (level, arity). These are not
/// stored here; they are recomputed on the fly (`prove_short_node` when proving, and
/// `short_node_preprocessed_root` in the unpacker) from the public (level, arity) — never
/// prover-chosen. All node variants pad to a COMMON `node_target_padding_sizes` so their *output*
/// proofs share one shape (one [`node_shared_config`], one node PCS); they differ only in gate
/// structure. If the two full-`k` padded shapes coincide, R1 == R2 (a 1-root collapse) — handled but
/// not assumed.
pub struct AggregateConfig {
    /// Verifier/prover config for a node whose CHILDREN are LEAVES (level-1 nodes). Built from the
    /// leaf circuit's preprocessed shape (`shared_config_for_leaf`). Also deserializes the leaf
    /// proofs a level-1 node verifies.
    pub leaf_shared_config: SharedConfig,
    /// Verifier/prover config for a node whose CHILDREN are NODES (level-≥2 nodes) and for
    /// verifying the ROOT proof in the unpacker. Built from the multiverifier node's own
    /// preprocessed shape (the self-verifying fixed point); level-independent because both node
    /// variants pad to the common `node_target_padding_sizes`.
    pub node_shared_config: SharedConfig,
    /// **R2** — the preprocessed root of a level-≥2 (node-verifying) multiverifier node. Reported by
    /// every internal node of height ≥ 2 to its parent.
    pub node_preprocessed_root: HashValue<QM31>,
    /// **R1** — the preprocessed root of a level-1 (leaf-verifying) multiverifier node. Reported by
    /// every internal node of height 1 to its parent. Equals `node_preprocessed_root` iff the two
    /// padded node shapes coincide.
    pub level1_preprocessed_root: HashValue<QM31>,
    /// The trusted preprocessed root of the leaf circuit (the same AIR for every leaf). The root
    /// verification's unpacker uses this single constant for *all* leaves, which both reconstructs
    /// the tree and forces every leaf to share this AIR (a leaf with a different `pp_root` makes
    /// the reconstruction miss the verified root).
    pub leaf_preprocessed_root: HashValue<QM31>,
    /// Padding targets applied to a level-≥2 node's trace AND (via the common target) a level-1
    /// node's trace, so all node *proofs* share one circuit shape (hence one `node_shared_config`).
    pub node_target_padding_sizes: ComponentSizes,
    /// Padding targets applied to every LEAF's trace — the leaf's OWN target (~2^20), decoupled from
    /// the node size so `t_leaf` is pinned independent of `FOLD_ARITY`.
    pub leaf_target_padding_sizes: ComponentSizes,
    /// PCS config used to prove each LEAF (and to describe the leaf proof shape a level-1 node
    /// verifies). Its `lifting_log_size` is the leaf trace's `log_size + log_blowup` (~24 for the
    /// gate_air leaf's 2^21 trace).
    pub leaf_pcs_config: PcsConfig,
    /// PCS config used to prove each NODE and to VERIFY the root (a node proof) in
    /// [`prove_root_verification`]. Under leaf↔node padding decoupling the node trace (2^22) is
    /// larger than the leaf trace (2^21), so a node proof's Merkle auth-path height is
    /// `node_log_size + log_blowup` (~25) — distinct from the leaf's (~24). Using the leaf PCS to
    /// describe a node proof mis-sizes the lifting and makes the root fold's Merkle check panic
    /// (`left 25 != right 24`); this field carries the node-sized lifting instead.
    pub node_pcs_config: PcsConfig,
    /// Witness-independent precompute for the level-≥2 (node-verifying) multiverifier node circuit.
    /// Reused for every [`prove_node`] call at height ≥ 2. `None` falls back to the self-contained
    /// [`prove_circuit_assignment`] path (rebuilds tree0 each call).
    pub node_precompute: Option<Arc<CircuitPrecompute>>,
    /// Witness-independent precompute for the level-1 (leaf-verifying) multiverifier node circuit.
    /// Reused for every [`prove_node`] call at height 1. `None` falls back to
    /// [`prove_circuit_assignment`].
    pub level1_precompute: Option<Arc<CircuitPrecompute>>,
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
        expected_root: HashValue<QM31>,
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

        let root: HashValue<QM31> = tree.commitment.root().into();
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
    /// Number of recursion levels above the leaves (the level loop's `k`-ary depth over `N`).
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

/// The arities of the LEVEL-0 (leaf-verifying) nodes for `n_leaves`, left-to-right — a deterministic
/// function of the public `N` (SOUNDNESS: the topology is public, never prover-chosen).
///
/// LEAF↔NODE DECOUPLING FIX: leaves (lift24) and nodes (lift25) have different proof shapes, so a
/// carried-up leaf landing under a height-≥2 (node-verifying, lift25) fold panics the in-circuit
/// Merkle height check. To prevent that, ALL leaves are consumed at level 0 into height-1 leaf-nodes
/// (so after level 0 every entry is a node, and every height-≥2 fold is homogeneous). This function
/// partitions the `N` leaves into contiguous groups, each an arity in `2..=FOLD_ARITY`, NEVER a lone
/// leaf:
///   - `N <= k`: one group of arity `N` (that node IS the root).
///   - `N > k`, `r = N % k`:
///       - `r == 0`: `N/k` groups of arity `k`.
///       - `r >= 2`: `N/k` groups of arity `k`, then ONE short group of arity `r`.
///       - `r == 1`: `(N/k - 1)` groups of arity `k`, then two short groups of arity `(k-1, 2)`
///         (the `k+1` trailing leaves cannot be a single `≤k` node, so they split — the unique
///         minimal-node way to keep every arity in `2..=k` with no lone leaf).
///
/// # Panics
/// If `n_leaves == 0`, or (unreachable) if `n_leaves == 1` — callers handle the lone-leaf case
/// (no fold) before calling this.
fn level0_group_sizes(n_leaves: usize) -> Vec<usize> {
    assert!(n_leaves >= 2, "level0_group_sizes needs n_leaves >= 2");
    if n_leaves <= FOLD_ARITY {
        return vec![n_leaves];
    }
    let full = n_leaves / FOLD_ARITY;
    let r = n_leaves % FOLD_ARITY;
    match r {
        0 => vec![FOLD_ARITY; full],
        1 => {
            let mut v = vec![FOLD_ARITY; full - 1];
            v.push(FOLD_ARITY - 1);
            v.push(2);
            v
        }
        _ => {
            let mut v = vec![FOLD_ARITY; full];
            v.push(r);
            v
        }
    }
}

/// Folds `leaves` into a single root proof by repeatedly proving `FOLD_ARITY`-to-1 multiverifier
/// nodes.
///
/// Any `N >= 1` is supported in two phases, byte-identical to [`build_fold_topology`]:
///   - **Level 0** (leaves → height-1 leaf-verifying nodes): partition the `N` leaves via
///     [`level0_group_sizes`] into contiguous groups (each arity `2..=k`, never a lone leaf) and
///     prove one leaf-verifying node per group. This CONSUMES every leaf at level 0, so no leaf ever
///     survives above height 1 — the leaf↔node decoupling fix (a carried leaf under a lift25 node
///     panics the Merkle height check). Full-`k` groups use [`prove_node`] (reusing
///     `level1_precompute`); short groups use [`prove_short_node`] (recomputes its real root R1'(m)).
///     For `N <= k` the single group is itself the root.
///   - **Levels ≥ 1** (nodes → nodes): the classic group+carry loop over the height-1 nodes — group
///     leading full-`k` runs into exactly-`k` node-verifying nodes and carry the `< k` remainder up
///     unchanged (carrying a NODE up is safe: all are lift25); the first level to reach `2..=k`
///     entries folds whole into the (possibly short) root. Every internal node-node is exactly-`k`
///     (shares `node_precompute` / R2); the root may be short (arity `root_arity(m1)`, a function of
///     the public leaf count), proved via the self-contained [`prove_short_node`].
///
/// Sibling groups at each level are independent and are proved concurrently across `pools` (a lone
/// group — e.g. the last fold step — runs on the full machine).
///
/// # Panics
/// If `leaves` is empty.
pub fn recursive_aggregate_prove(
    leaves: Vec<TreeProof>,
    config: &AggregateConfig,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!leaves.is_empty(), "need at least one leaf");

    // n_leaves == 1: the lone leaf is itself the root (no fold).
    if leaves.len() == 1 {
        return AggregateOutput {
            root: leaves.into_iter().next().unwrap(),
            n_levels: 0,
        };
    }

    // --- Level 0: consume ALL leaves into height-1 leaf-verifying nodes. ---
    // After this, every entry is a NODE (height 1), so every height-≥2 fold below is homogeneous
    // and no leaf can land under a lift25 node.
    let sizes = level0_group_sizes(leaves.len());
    // Slice `leaves` into contiguous groups (moving, no clone) and prove one leaf-node each.
    let mut leaves_iter = leaves.into_iter();
    let mut groups: Vec<Vec<TreeProof>> = sizes
        .iter()
        .map(|&m| leaves_iter.by_ref().take(m).collect())
        .collect();
    // `N <= k`: the single group is the root — a (possibly short) leaf-verifying node at height 1.
    if groups.len() == 1 {
        let children = groups.pop().unwrap();
        let root = prove_leaf_or_short(&children, config, 1);
        return AggregateOutput { root, n_levels: 1 };
    }
    let jobs: Vec<_> = groups
        .iter()
        .map(|children| move || (1usize, prove_leaf_or_short(children, config, 1)))
        .collect();
    // Track each entry's height above the leaves (level-0 nodes are height 1). A node's height is
    // `max(child heights) + 1` — byte-identical to `build_fold_topology`'s per-task `height`, which
    // selects R1 (height 1, verifies leaves) vs R2 (height ≥ 2, verifies nodes) under decoupling.
    let mut level: Vec<(usize, TreeProof)> = pools.map(jobs);

    // --- Levels ≥ 1: classic group+carry over NODES only. ---
    while level.len() > 1 {
        if level.len() <= FOLD_ARITY {
            // Terminal step: fold the whole (2..=k) level into the single (possibly short) root.
            let height = level.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children: Vec<TreeProof> = level.into_iter().map(|(_, p)| p).collect();
            let root = prove_short_node(&children, config, height);
            return AggregateOutput {
                root,
                n_levels: height,
            };
        }
        // `len > k`: carry the trailing `< k` remainder up unchanged; group the leading full-k runs
        // into exactly-k internal nodes. Prove the groups concurrently across the pools.
        let remainder = level.len() % FOLD_ARITY;
        let carry: Vec<(usize, TreeProof)> = level.split_off(level.len() - remainder);
        // Consume `level` into exactly-k groups, computing each group's height (max child + 1)
        // before moving its proofs into a prove closure — no proof is cloned.
        let mut groups: Vec<(usize, Vec<TreeProof>)> = Vec::with_capacity(level.len() / FOLD_ARITY);
        let mut iter = level.into_iter().peekable();
        while iter.peek().is_some() {
            let group: Vec<(usize, TreeProof)> = iter.by_ref().take(FOLD_ARITY).collect();
            let height = group.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children: Vec<TreeProof> = group.into_iter().map(|(_, p)| p).collect();
            groups.push((height, children));
        }
        let jobs: Vec<_> = groups
            .iter()
            .map(|(height, children)| move || (*height, prove_node(children, config, *height)))
            .collect();
        let mut next: Vec<(usize, TreeProof)> = pools.map(jobs);
        next.extend(carry);
        level = next;
    }

    // A single level-0 node with n>k impossible; the loop always folds to a root above.
    let (height, root) = level.into_iter().next().unwrap();
    AggregateOutput {
        root,
        n_levels: height,
    }
}

/// Proves one LEVEL-0 (height-1, leaf-verifying) node over `children` leaves: full-`FOLD_ARITY`
/// groups go through [`prove_node`] (reusing `level1_precompute`), short groups (`2..=k-1`) through
/// [`prove_short_node`] (which recomputes its real preprocessed root R1'(m)). `height` is always 1.
fn prove_leaf_or_short(children: &[TreeProof], config: &AggregateConfig, height: usize) -> TreeProof {
    debug_assert_eq!(height, 1, "level-0 leaf nodes are always height 1");
    if children.len() == FOLD_ARITY {
        prove_node(children, config, height)
    } else {
        prove_short_node(children, config, height)
    }
}

/// The arity of the ROOT node of the fold tree over `n_leaves` — a deterministic function of the
/// public leaf count `N` (SOUNDNESS: the root shape is public, never prover-chosen).
///
/// Mirrors [`recursive_aggregate_prove`]/[`build_fold_topology`] under the two-phase topology: level
/// 0 consumes the `N` leaves into `m1 = level0_group_sizes(N).len()` height-1 leaf-nodes, then the
/// classic group+carry loop folds those `m1` NODES (levels with `> k` entries carry the `< k`
/// remainder and emit `len / k` exactly-`k` node-nodes; the first level to reach `2..=k` folds whole
/// into the root). Returns that terminal size (`∈ 2..=k`). For `n_leaves == 1` there is no fold
/// (returns `1`); for `2 <= n_leaves <= k` the single level-0 node IS the root (returns `N`).
pub fn root_arity(n_leaves: usize) -> usize {
    if n_leaves == 1 {
        return 1;
    }
    // Level 0 collapses N leaves into m1 nodes. If m1 == 1 that single level-0 node IS the root, so
    // its arity is that group's size (N, since N <= k). Otherwise the root folds over the m1 nodes.
    let sizes = level0_group_sizes(n_leaves);
    if sizes.len() == 1 {
        return sizes[0];
    }
    let mut len = sizes.len();
    while len > FOLD_ARITY {
        len = len / FOLD_ARITY + len % FOLD_ARITY;
    }
    len
}

/// A reference to one input of a streaming fold node: either a base/leaf proof (by shard index, the
/// canonical arrival order) or the output of an earlier fold node (by node index).
#[derive(Clone, Copy)]
enum Child {
    Leaf(usize),
    Node(usize),
}

/// One fold in the fixed tree: prove a node over `children`, children left-to-right. A node-node
/// internal task has `children.len() == FOLD_ARITY`; a level-0 (height-1) leaf-node task may be short
/// (`2..=k`, from [`level0_group_sizes`]); the single ROOT task may be short (`2..=k`). The arity is
/// `children.len()` and the level (verifies leaves vs nodes) is `NodeLevel::from_height(height)`.
struct FoldTask {
    children: Vec<Child>,
    /// Height above the leaves of this node's output (leaves are height 0; level-0 nodes are 1).
    height: usize,
}

/// Computes the FIXED fold topology for `n_leaves`, decided up front and independent of completion
/// order, **byte-identical** to the tree [`recursive_aggregate_prove`]'s level loop builds.
///
/// It runs the level loop's algorithm over *indices* instead of proofs: while a level has `> k`
/// entries it groups the leading full-`k` runs left-to-right into `prove_node(group)` and carries
/// the trailing `< k` remainder up unchanged; a level of `2..=k` entries is folded whole into the
/// root. The returned `Vec<FoldTask>` is in the same order the level loop would prove them (level by
/// level, left to right); the returned [`Child`] is the root (a `Node` for `n_leaves > 1`, else
/// `Leaf(0)`). Each task's `children` order matches `prove_node`'s exactly, so each node sees the
/// same inputs as the sequential fold ⇒ same proof bytes.
fn build_fold_topology(n_leaves: usize) -> (Vec<FoldTask>, Child) {
    if n_leaves == 1 {
        return (Vec::new(), Child::Leaf(0));
    }
    let mut tasks: Vec<FoldTask> = Vec::new();

    // --- Level 0: consume ALL leaves into height-1 leaf-verifying nodes (per `level0_group_sizes`),
    //     so no leaf ever survives above height 1. Groups are contiguous, left-to-right. ---
    let sizes = level0_group_sizes(n_leaves);
    let mut next_leaf = 0usize;
    // Current level (height, child-ref), mirroring the level loop's `Vec<TreeProof>`.
    let mut level: Vec<(usize, Child)> = Vec::with_capacity(sizes.len());
    for &m in &sizes {
        let children: Vec<Child> = (next_leaf..next_leaf + m).map(Child::Leaf).collect();
        next_leaf += m;
        let idx = tasks.len();
        tasks.push(FoldTask { children, height: 1 });
        level.push((1, Child::Node(idx)));
    }
    // `N <= k`: the single level-0 node is the root.
    if level.len() == 1 {
        return (tasks, level[0].1);
    }

    // --- Levels ≥ 1: classic group+carry over NODES only. ---
    while level.len() > 1 {
        if level.len() <= FOLD_ARITY {
            // Terminal step: the whole (2..=k) level folds into the single (possibly short) root.
            let height = level.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children = level.iter().map(|(_, c)| *c).collect();
            let idx = tasks.len();
            tasks.push(FoldTask { children, height });
            return (tasks, Child::Node(idx));
        }
        let remainder = level.len() % FOLD_ARITY;
        let carry: Vec<(usize, Child)> = level.split_off(level.len() - remainder);
        let mut next: Vec<(usize, Child)> = Vec::with_capacity(level.len() / FOLD_ARITY + remainder);
        for group in level.chunks(FOLD_ARITY) {
            let height = group.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children = group.iter().map(|(_, c)| *c).collect();
            let idx = tasks.len();
            tasks.push(FoldTask { children, height });
            next.push((height, Child::Node(idx)));
        }
        // Carry the `< k` remainder up unchanged (all NODES now — safe under decoupling).
        next.extend(carry);
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
/// leaves. The topology is FIXED up front by [`build_fold_topology`] (the two-phase tree: level 0
/// consumes leaves into leaf-nodes per `level0_group_sizes`, then group+carry over nodes; e.g. at
/// k=8 the N=9 root is `node([node([0..7]), node([7..9])])`) and does not depend on completion order;
/// every [`FoldTask`] sees the same ordered children the sequential fold gives its matching
/// `prove_node`/`prove_short_node`. Because those are pure functions of their ordered children,
/// identical topology + identical per-node inputs ⇒ identical root proof and `recursion_fingerprint`,
/// which the [`prove_root_verification`] unpacker still binds.
///
/// Streaming schedule: one coordinator owns the dataflow state; `pools.n_pools()` workers (one per
/// pool) pull ready folds and run the fold via [`ThreadPool::install`] (so each fold gets its own
/// pool's cores, matching the sequential fold's per-prove parallelism). As leaves arrive on `rx`,
/// any fold whose `k` children are now available becomes ready; a fold completing makes its parent's
/// child available in turn. Up to `n_pools()` folds run at once while later leaves are still being
/// produced. Folds never starve: the tree is CPU-fold-bound, so a backlog of ready folds always
/// exists once base proofs outpace the single CPU consumer.
///
/// Consumes exactly `n_leaves` from `rx` in arrival order. Returns the same [`AggregateOutput`] as
/// the level loop (root + the `k`-ary depth `n_levels`). For `n_leaves == 1` returns the single leaf
/// as root with `n_levels = 0`.
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
    //   parent_of[Leaf i] / parent_of_node[Node j] = Some((task_idx, slot)), slot = child position
    //   in the task's `children` (left-to-right), so inputs reassemble in the fold's exact order.
    let mut leaf_parent: Vec<Option<(usize, usize)>> = vec![None; n_leaves];
    let mut node_parent: Vec<Option<(usize, usize)>> = vec![None; tasks.len()];
    let mut pending: Vec<usize> = vec![0; tasks.len()];
    let arity: Vec<usize> = tasks.iter().map(|t| t.children.len()).collect();
    for (ti, t) in tasks.iter().enumerate() {
        for (slot, ch) in t.children.iter().enumerate() {
            pending[ti] += 1;
            match ch {
                Child::Leaf(i) => leaf_parent[*i] = Some((ti, slot)),
                Child::Node(j) => node_parent[*j] = Some((ti, slot)),
            }
        }
    }

    // Dataflow state shared between the coordinator and the worker threads.
    struct State {
        // Resolved child inputs for each task (one `Option` slot per child, left-to-right), filled
        // as children become available.
        inputs: Vec<Vec<Option<TreeProof>>>,
        pending: Vec<usize>,
        ready: std::collections::VecDeque<usize>,
        done: usize,
        // The root proof, captured when the root fold (the one with no parent) completes.
        root: Option<TreeProof>,
    }
    let n_tasks = tasks.len();
    let state = std::sync::Mutex::new(State {
        inputs: arity.iter().map(|&k| (0..k).map(|_| None).collect()).collect(),
        pending,
        ready: std::collections::VecDeque::new(),
        done: 0,
        root: None,
    });
    // Signalled when a fold becomes ready or all folds are done (so idle workers wake up).
    let cv = std::sync::Condvar::new();

    // Records that `proof` is the value of `child`, wiring it into the consuming task and enqueuing
    // that task once all its child inputs are present. Returns nothing; mutates `st` under its lock.
    let deliver = |st: &mut State, parent: Option<(usize, usize)>, proof: TreeProof| {
        if let Some((ti, slot)) = parent {
            st.inputs[ti][slot] = Some(proof);
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
            let tasks = &tasks;
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
                    // Take ownership of this task's resolved inputs and prove off-lock. All child
                    // `TreeProof`s are `take()`n out of `inputs` here, so once this node's result is
                    // delivered to its parent the children have no remaining references and are freed
                    // (dropped when `children` leaves scope). Nothing retains proved node proofs:
                    // peak host memory therefore holds only the N leaves (owned by the caller for
                    // `prove_root_verification`) + the O(log_k N) in-flight fold path, never all the
                    // node proofs.
                    let children: Vec<TreeProof> = {
                        let mut st = state.lock().unwrap();
                        st.inputs[ti]
                            .iter_mut()
                            .map(|slot| slot.take().unwrap())
                            .collect()
                    };
                    // Dispatch EXACTLY as the sequential fold, so the two paths stay byte-identical:
                    //   - the phase-B ROOT (no parent, height ≥ 2) ⇒ `prove_short_node` (the
                    //     self-contained recompute path) even when its arity is `FOLD_ARITY` — the
                    //     sequential terminal step always uses it, so the streaming root must too;
                    //   - otherwise (all level-0 nodes incl. the N≤k single-group root at height 1,
                    //     and every non-root internal node): full-`k` ⇒ `prove_node` (precompute,
                    //     fixed R1/R2), short ⇒ `prove_short_node` (recomputed real root). This is the
                    //     same rule the sequential level-0 `prove_leaf_or_short` + phase-B loop apply.
                    let is_root = node_parent[ti].is_none();
                    let height = tasks[ti].height;
                    let result = pool.install(|| {
                        if is_root && height >= 2 {
                            prove_short_node(&children, config, height)
                        } else if children.len() == FOLD_ARITY {
                            prove_node(&children, config, height)
                        } else {
                            prove_short_node(&children, config, height)
                        }
                    });
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

    // (1) Verify the root multiverifier proof in-circuit. The root is a NODE proof, so it is
    //     verified with `node_shared_config` (the node's own shape). Both node variants (R1 and R2)
    //     pad to the common `node_target_padding_sizes`, so a node proof's shape
    //     (preprocessed_column_log_sizes, n_columns, PCS) is level-independent; only the root's
    //     `preprocessed_root` (R1 for a height-1 root, R2 above) differs, and that is guessed here
    //     from `root.preprocessed_root`, not part of the topology.
    let circuit_config = CircuitConfig {
        // The root is a NODE proof, so it is described/verified with the node-sized PCS (node
        // lifting ~25), not the leaf PCS (~24). Using the leaf PCS here mis-sizes the Merkle
        // lifting and panics the R2 root fold.
        config: config.node_pcs_config,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: config
            .node_shared_config
            .preprocessed_column_log_sizes
            .clone(),
        preprocessed_root: root.preprocessed_root.clone(),
    };
    let statement = CircuitStatement::new(&mut context, &circuit_config, &root.output_values);
    let proof_vars = root.proof.guess(&mut context);
    verify(
        &mut context,
        &proof_vars,
        &config.node_shared_config.proof_config,
        &statement,
    );
    let root_out_vars: Vec<Var> = statement.get_output_values().to_vec();

    // (2) Unpack: reconstruct the tree root from guessed leaf outputs and bind it to the verified
    //     root. One trusted leaf_preprocessed_root for every leaf (forces a shared AIR); produced
    //     internal nodes report node_preprocessed_root.
    //
    // Each level entry is `(pp_root: HashValue<Var>, outs: Vec<Var>)`, where `pp_root` is the eight
    // guessed digest words of the child's preprocessed root and `outs` is the child's `N_RESERVED`
    // output QM31 values (for a leaf: its raw outputs; for a produced node: the eight words of its
    // Blake digest, each a QM31 `(lo, hi, 0, 0)`). This matches what the in-circuit node consumes:
    // `statement.preprocessed_root` (a guessed `HashValue<Var>`) and `statement.get_output_values()`
    // (the `N_RESERVED` output QM31s). Guessing the pp_root here mirrors `CircuitStatement::new`,
    // which also guesses the eight root words.
    let guess_pp = |context: &mut Context<QM31>, pp: &HashValue<QM31>| -> HashValue<Var> {
        pp.guess(context)
    };
    let leaf_pp = guess_pp(&mut context, &config.leaf_preprocessed_root);
    let mut leaf_output_vars: Vec<Vec<Var>> = Vec::with_capacity(n);
    // Each level entry is `(height, pp_root, outs)`. Leaves are height 0 and carry `leaf_pp`; a
    // produced node's height is `max(child heights) + 1` and it carries the root its shape reported
    // when the fold proved it: a full-`k` node reports the fixed R1 (`level1_preprocessed_root`,
    // height 1) / R2 (`node_preprocessed_root`, height ≥ 2); a short node (level-0 short leaf group
    // or the short root) reports its recomputed real root via `short_node_preprocessed_root`. This
    // selection MUST be byte-identical to what `prove_node`/`prove_short_node` reported (all select by
    // the same public (height, arity)); otherwise the reconstructed root misses the verified root and
    // the proof is REJECTED (caught by the final-proof sanity check / byte-identity), never
    // accepted-invalid. Every reported root is a trusted value fixed by public (height, arity).
    let mut leaf_entries: Vec<(usize, HashValue<Var>, Vec<Var>)> = leaves
        .iter()
        .map(|l| {
            let outs: Vec<Var> = l
                .output_values
                .iter()
                .map(|v| guess(&mut context, *v))
                .collect();
            leaf_output_vars.push(outs.clone());
            (0usize, leaf_pp.clone(), outs)
        })
        .collect();
    // Reconstruct the tree exactly as the two-phase fold builds it (see `recursive_aggregate_prove`):
    // LEVEL 0 consumes ALL leaves into height-1 leaf-nodes (per `level0_group_sizes`); LEVELS ≥ 1
    // group the leading full-`k` runs of NODES into nodes and carry the `< k` remainder up unchanged;
    // a `2..=k` level folds whole into the (possibly short) root. Each node's Blake preimage MUST be
    // byte-identical to the in-circuit node hash in `build_multiverifier_circuit`: concatenate the
    // children left-to-right, per child emitting `chain!(preprocessed_root.into_iter() [8 digest
    // words], unpack_qm31s_to_u32_words(outputs))` and hashing the whole payload with `blake2s_u32s`
    // over `4 * n_words` bytes. THIS IS THE ONE ORDERING SPEC shared with the node circuit; both
    // derive from it (#1425 8-word root format).
    //
    // `fold_group` produces one node from an ordered group of children and guesses the SAME reported
    // preprocessed root the prover reported for that node — selected by public (height, arity):
    //   - arity == k         -> the fixed R1 (height 1) / R2 (height ≥ 2) via `NodeLevel`.
    //   - arity  <  k (short)-> the recomputed short-node root R1'(m) / short-root real root, matching
    //                           `prove_short_node` byte-for-byte via `short_node_preprocessed_root`.
    // A wrong selection makes the reconstructed root miss the verified root ⇒ the proof is REJECTED
    // (final-proof sanity check / byte-identity), never accepted-invalid.
    let fold_group = |context: &mut Context<QM31>,
                      group: &[(usize, HashValue<Var>, Vec<Var>)]|
     -> (usize, HashValue<Var>, Vec<Var>) {
        let mut preimage: Vec<U32Wrapper<Var>> = Vec::new();
        for (_, pp, outs) in group {
            let output_words = unpack_qm31s_to_u32_words(context, outs.iter().copied());
            preimage.extend(pp.iter().copied().chain(output_words));
        }
        let n_bytes = 4 * preimage.len();
        let h = blake2s_u32s(context, preimage, n_bytes);
        let height = group.iter().map(|(h, _, _)| *h).max().unwrap() + 1;
        let level = NodeLevel::from_height(height);
        let reported_root = if group.len() == FOLD_ARITY {
            level.preprocessed_root(config)
        } else {
            short_node_preprocessed_root(config, level, group.len())
        };
        let node_pp = guess_pp(context, &reported_root);
        let outs: Vec<Var> = h.iter().map(|w| *w.get()).collect();
        (height, node_pp, outs)
    };

    // --- LEVEL 0: consume ALL leaves into height-1 leaf-nodes (no leaf survives above height 1). ---
    // n == 1: the lone leaf is itself the root (no fold), matching `recursive_aggregate_prove`.
    let mut level: Vec<(usize, HashValue<Var>, Vec<Var>)> = if n == 1 {
        leaf_entries
    } else {
        let sizes = level0_group_sizes(n);
        let mut leaves_iter = leaf_entries.drain(..);
        let level0: Vec<(usize, HashValue<Var>, Vec<Var>)> = sizes
            .iter()
            .map(|&m| {
                let group: Vec<(usize, HashValue<Var>, Vec<Var>)> =
                    (0..m).map(|_| leaves_iter.next().unwrap()).collect();
                fold_group(&mut context, &group)
            })
            .collect();
        drop(leaves_iter);
        level0
    };

    // --- LEVELS ≥ 1: classic group+carry over NODES only. ---
    while level.len() > 1 {
        if level.len() <= FOLD_ARITY {
            // Terminal step: fold the whole (2..=k) level into the single (possibly short) root.
            let root = fold_group(&mut context, &level);
            level = vec![root];
            break;
        }
        let remainder = level.len() % FOLD_ARITY;
        let carry: Vec<(usize, HashValue<Var>, Vec<Var>)> =
            level.split_off(level.len() - remainder);
        let mut next = Vec::with_capacity(level.len() / FOLD_ARITY + remainder);
        for group in level.chunks(FOLD_ARITY) {
            next.push(fold_group(&mut context, group));
        }
        next.extend(carry);
        level = next;
    }
    // Bind the reconstructed root's eight digest words to the verified root's eight output words.
    // The verified root's `output_values` are the eight QM31 digest words; `root_out_vars` holds
    // them directly (same encoding as `computed_root`), so the eight `eq`s are word-for-word.
    let computed_root = &level[0].2;
    for i in 0..N_RESERVED {
        eq(&mut context, computed_root[i], root_out_vars[i]);
    }

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
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    // SANITY CHECK: verify the final published proof natively before returning it. Mirrors
    // `privacy_circuit_verify::verify_recursive_circuit` — the root-verification proof is a
    // `prepare_circuit_proof_for_circuit_verifier` (circuit_verifier-family) proof, so it is checked
    // with `verify_circuit(CircuitConfig, proof, CircuitPublicData)`. Every input is derived from the
    // circuit that produced this proof: the same `pcs_config`, its real output count (`n *
    // N_RESERVED` flat leaf-output wires), the just-built preprocessed trace's column log sizes, and
    // its real preprocessed root. `CircuitPublicData` is the `public_data` returned alongside the
    // proof (the flat leaf outputs). Asserts the produced proof actually verifies.
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

/// Proves a padded circuit's `values` against a prebuilt witness-independent [`CircuitPrecompute`],
/// reusing its committed preprocessed (tree0) tree and twiddles instead of rebuilding them.
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

/// A node's tree level, which selects its shape under leaf↔node padding decoupling.
///
/// A **level-1** node verifies `FOLD_ARITY` LEAVES (child config `leaf_shared_config`); it reports
/// **R1** (`level1_preprocessed_root`). A **level-≥2** node verifies `FOLD_ARITY` NODES (child
/// config `node_shared_config`); it reports **R2** (`node_preprocessed_root`). The level is fixed by
/// the public topology ([`FoldTask::height`]), never prover-chosen. This is the one selector the
/// decoupling threads through the fold + the unpacker; keep it byte-identical in both.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeLevel {
    /// Children are leaves (node height == 1).
    VerifiesLeaves,
    /// Children are nodes (node height >= 2).
    VerifiesNodes,
}

impl NodeLevel {
    /// The node level for a node of the given height above the leaves (leaves are height 0).
    fn from_height(height: usize) -> Self {
        if height == 1 {
            NodeLevel::VerifiesLeaves
        } else {
            NodeLevel::VerifiesNodes
        }
    }

    /// The child-verifier config (`leaf_shared_config` for leaf children, `node_shared_config` for
    /// node children).
    fn shared_config(self, config: &AggregateConfig) -> &SharedConfig {
        match self {
            NodeLevel::VerifiesLeaves => &config.leaf_shared_config,
            NodeLevel::VerifiesNodes => &config.node_shared_config,
        }
    }

    /// The trusted preprocessed root a node of this level reports (R1 vs R2).
    fn preprocessed_root(self, config: &AggregateConfig) -> HashValue<QM31> {
        match self {
            NodeLevel::VerifiesLeaves => config.level1_preprocessed_root.clone(),
            NodeLevel::VerifiesNodes => config.node_preprocessed_root.clone(),
        }
    }

    /// The witness-independent precompute for this level's node circuit, if built.
    fn precompute(self, config: &AggregateConfig) -> Option<&Arc<CircuitPrecompute>> {
        match self {
            NodeLevel::VerifiesLeaves => config.level1_precompute.as_ref(),
            NodeLevel::VerifiesNodes => config.node_precompute.as_ref(),
        }
    }
}

/// Builds and pads (to the common `node_target_padding_sizes`) the multiverifier circuit that
/// verifies `children`, using the child-verifier config for the node's `level`.
fn build_node_context(
    children: &[TreeProof],
    config: &AggregateConfig,
    level: NodeLevel,
) -> FinalizedContext<QM31> {
    let inputs: Vec<MultiverifierInput<QM31>> = children.iter().map(child_input).collect();
    let mut context = build_multiverifier_circuit::<QM31>(inputs, level.shared_config(config));
    pad_to_targets(&mut context, config.node_target_padding_sizes.clone());
    context.validate_circuit();
    context
}

/// Proves one exactly-`FOLD_ARITY` INTERNAL node verifying `children` (`children.len() ==
/// FOLD_ARITY`). `height` is the node's height above the leaves (1 ⇒ verifies leaves ⇒ R1;
/// ≥2 ⇒ verifies nodes ⇒ R2), which selects the child config, precompute, and reported root.
fn prove_node(children: &[TreeProof], config: &AggregateConfig, height: usize) -> TreeProof {
    debug_assert_eq!(
        children.len(),
        FOLD_ARITY,
        "internal fold node must have exactly FOLD_ARITY children"
    );
    let level = NodeLevel::from_height(height);
    let _t_node = std::time::Instant::now();
    let mut context = build_node_context(children, config, level);

    let circuit_proof = match level.precompute(config) {
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
        preprocessed_root: level.preprocessed_root(config),
        output_values,
    }
}

/// Proves one SHORT node (arity `m ∈ 2..=FOLD_ARITY`) verifying `children`. Used for the short ROOT
/// AND for short LEVEL-0 leaf groups (arity `2..=k-1` from [`level0_group_sizes`]).
///
/// A short node's circuit shape differs from the exactly-`k` internal shape (fewer child-verify
/// sub-circuits), so it cannot reuse `node_precompute`/`level1_precompute`; it is proved via the
/// self-contained rebuild path. Its reported `preprocessed_root` is the circuit's *real* preprocessed
/// root (recomputed here from the just-built preprocessed circuit) — a value fixed by the node's
/// arity and level, both deterministic functions of the public leaf count, hence verifier-derivable
/// (the unpacker recomputes the identical value via [`short_node_preprocessed_root`]) and never
/// prover-chosen. The node's `level` (height 1 ⇒ verifies leaves, R1'(m); height ≥ 2 ⇒ verifies
/// nodes) selects the child-verifier config. When `m == FOLD_ARITY` this yields exactly the same
/// shape (and root) as the matching full-`k` internal node.
fn prove_short_node(children: &[TreeProof], config: &AggregateConfig, height: usize) -> TreeProof {
    assert!(
        (2..=FOLD_ARITY).contains(&children.len()),
        "short/root fold node must have 2..=FOLD_ARITY children (got {})",
        children.len()
    );
    let level = NodeLevel::from_height(height);
    let _t_node = std::time::Instant::now();
    let mut context = build_node_context(children, config, level);

    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    // The node's real preprocessed root — pinned by the (public) arity + level, not prover-chosen.
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
/// `shared` config (the one a node is proved with) padded to `target_padding`. For `arity ==
/// FOLD_ARITY` this is the fixed shape every internal node proves (the one to cache in a node
/// [`CircuitPrecompute`]); for `arity < FOLD_ARITY` it is a SHORT node (a level-0 short leaf group or
/// the short root), whose preprocessed root the unpacker recomputes to match `prove_short_node`.
///
/// Mirrors the node-shape construction inside [`multiverifier_node_preprocessed`], but keyed on the
/// already-built `SharedConfig` (so a caller holding only a [`AggregateConfig`] can rebuild the cache
/// without the leaf's `PreprocessedCircuit`).
pub fn node_preprocessed_from_shared(
    shared: &SharedConfig,
    target_padding: ComponentSizes,
    arity: usize,
) -> PreprocessedCircuit {
    // Build the same node circuit `prove_node`/`prove_short_node` does, with NoValue witnesses (the
    // preprocessed trace is witness-independent). The verification topology is sized from a NoValue
    // `proof_config` over the shared `n_preprocessed_columns`, mirroring stwo-circuits' node-shape
    // construction.
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
        preprocessed_root: HashValue::from([0u32; N_RESERVED]),
        output_values: [QM31::zero(); N_RESERVED],
    };
    let inputs: Vec<MultiverifierInput<NoValue>> = (0..arity).map(|_| empty()).collect();
    let mut ctx = build_multiverifier_circuit::<NoValue>(inputs, &node_shared);
    pad_to_targets(&mut ctx, target_padding);
    PreprocessedCircuit::preprocess_circuit(&mut ctx)
}

/// The preprocessed root a SHORT node of the given `level` and `arity` (`2..=FOLD_ARITY-1`) reports —
/// recomputed witness-independently, byte-identical to what [`prove_short_node`] recomputes for the
/// same shape. Pure function of the public `(level, arity)`, so the unpacker binds the same value the
/// prover reported. `VerifiesLeaves` builds over the leaf child config (R1'(m)); `VerifiesNodes`
/// builds over the node child config (short-root real root).
fn short_node_preprocessed_root(
    config: &AggregateConfig,
    level: NodeLevel,
    arity: usize,
) -> HashValue<QM31> {
    let shared = level.shared_config(config);
    let pp = node_preprocessed_from_shared(shared, config.node_target_padding_sizes.clone(), arity);
    preprocessed_root(&pp, config.node_pcs_config.fri_config.log_blowup_factor)
}

impl AggregateConfig {
    /// Defense-in-depth consistency check (exercised by the `decoupled_roots_consistent` test in the
    /// genuinely decoupled R1 != R2 regime, NOT called at config-build — this is intentionally not a
    /// runtime assert). The unpacker binds full-`FOLD_ARITY` nodes to the trusted roots stored here —
    /// R2 (`node_preprocessed_root`) for node-verifying, R1 (`level1_preprocessed_root`) for
    /// leaf-verifying — while short nodes and the root are bound to the witness-independent recompute
    /// [`short_node_preprocessed_root`]. Those two must agree at full arity (they do by construction:
    /// the same node circuit shape, built via `node_preprocessed_from_shared`). A divergence is
    /// fail-closed (the fold / root verification would reject via the missing-root reconstruction), so
    /// this only turns the one otherwise-unasserted recompute equivalence into a loud check. (The
    /// cached full-arity precompute already asserts tree0 == root in [`CircuitPrecompute::new`].)
    pub fn assert_full_arity_roots_consistent(&self) {
        assert_eq!(
            short_node_preprocessed_root(self, NodeLevel::VerifiesNodes, FOLD_ARITY),
            self.node_preprocessed_root,
            "full-{FOLD_ARITY} node-node preprocessed root recompute != trusted R2",
        );
        assert_eq!(
            short_node_preprocessed_root(self, NodeLevel::VerifiesLeaves, FOLD_ARITY),
            self.level1_preprocessed_root,
            "full-{FOLD_ARITY} leaf-node preprocessed root recompute != trusted R1",
        );
    }
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
        preprocessed_root: HashValue::from([0u32; N_RESERVED]),
        output_values: [QM31::zero(); N_RESERVED],
    };
    // The internal node shape is exactly-FOLD_ARITY children (matches `prove_node`).
    let inputs: Vec<MultiverifierInput<NoValue>> = (0..FOLD_ARITY).map(|_| empty()).collect();
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

#[cfg(test)]
mod topology_tests {
    use super::{Child, FOLD_ARITY, NodeLevel, build_fold_topology, level0_group_sizes, root_arity};

    /// A symbolic tree shape, leaf-index aware — the byte-identity-relevant structure of a fold tree
    /// (each node's ordered children and the resulting nesting).
    #[derive(PartialEq, Eq, Debug)]
    enum Shape {
        Leaf(usize),
        Node(Vec<Shape>),
    }

    /// The shape `recursive_aggregate_prove`'s two-phase fold builds, computed over indices — LEVEL 0
    /// partitions the leaves into leaf-nodes via `level0_group_sizes` (every leaf consumed, no lone
    /// leaf), then LEVELS ≥ 1 do the classic `k`-ary group+carry over NODES (leading full-`k` runs
    /// into nodes, `< k` remainder carried up, a `2..=k` level folded whole into the root). The single
    /// source of truth the topology must match.
    fn sequential_shape(n: usize) -> Shape {
        if n == 1 {
            return Shape::Leaf(0);
        }
        // LEVEL 0: leaves -> leaf-nodes per level0_group_sizes.
        let mut next_leaf = 0usize;
        let mut level: Vec<Shape> = level0_group_sizes(n)
            .into_iter()
            .map(|m| {
                let node = Shape::Node((next_leaf..next_leaf + m).map(Shape::Leaf).collect());
                next_leaf += m;
                node
            })
            .collect();
        // LEVELS >= 1: group+carry over nodes.
        while level.len() > 1 {
            if level.len() <= FOLD_ARITY {
                return Shape::Node(level);
            }
            let remainder = level.len() % FOLD_ARITY;
            let carry: Vec<Shape> = level.split_off(level.len() - remainder);
            let mut next: Vec<Shape> = Vec::new();
            let mut iter = level.into_iter().peekable();
            while iter.peek().is_some() {
                let group: Vec<Shape> = iter.by_ref().take(FOLD_ARITY).collect();
                next.push(Shape::Node(group));
            }
            next.extend(carry);
            level = next;
        }
        level.into_iter().next().unwrap()
    }

    /// Reference count of nodes the two-phase fold proves (one per node): the `m1` level-0 leaf-nodes
    /// plus the phase-B nodes folded over those `m1` nodes.
    fn sequential_node_count(n: usize) -> usize {
        if n == 1 {
            return 0;
        }
        let m1 = level0_group_sizes(n).len();
        let mut count = m1; // level-0 leaf-nodes
        if m1 == 1 {
            return count; // the single level-0 node is the root
        }
        // Phase B: classic group+carry over the m1 nodes.
        let mut len = m1;
        while len > 1 {
            if len <= FOLD_ARITY {
                count += 1;
                break;
            }
            count += len / FOLD_ARITY;
            len = len / FOLD_ARITY + len % FOLD_ARITY;
        }
        count
    }

    /// Reference root height of the two-phase fold: level 0 is height 1, then the phase-B levels over
    /// the `m1` level-0 nodes add on top (if `m1 == 1` the level-0 node IS the root, height 1).
    fn sequential_height(n: usize) -> usize {
        if n == 1 {
            return 0;
        }
        let m1 = level0_group_sizes(n).len();
        let mut height = 1usize; // level 0
        if m1 == 1 {
            return height;
        }
        let mut len = m1;
        while len > 1 {
            height += 1;
            if len <= FOLD_ARITY {
                break;
            }
            len = len / FOLD_ARITY + len % FOLD_ARITY;
        }
        height
    }

    /// The shape the streaming scheduler realizes, reconstructed from `build_fold_topology`'s task
    /// list + root reference. Each task's ordered `children` resolve to the same `Shape` nodes,
    /// proving the streaming dataflow folds the identical tree with the identical child inputs.
    fn streaming_shape(n: usize) -> Shape {
        let (tasks, root) = build_fold_topology(n);
        fn resolve(c: Child, tasks: &[super::FoldTask]) -> Shape {
            match c {
                Child::Leaf(i) => Shape::Leaf(i),
                Child::Node(j) => Shape::Node(
                    tasks[j].children.iter().map(|&ch| resolve(ch, tasks)).collect(),
                ),
            }
        }
        resolve(root, &tasks)
    }

    /// The streamed tree is byte-identical to the sequential one because it has the IDENTICAL shape:
    /// same nesting, same leaf-index-to-child-slot assignment for every node. Since `prove_node` is a
    /// pure function of its ordered children, identical shape + identical per-node inputs ⇒ identical
    /// proof bytes and `recursion_fingerprint`. Checks every N up to 260 — covers ALL `N mod k`
    /// residues at k=FOLD_ARITY across several levels, plus power-of-k boundaries.
    #[test]
    fn streaming_topology_matches_sequential() {
        for n in 1..=260usize {
            assert_eq!(
                streaming_shape(n),
                sequential_shape(n),
                "fold topology diverges from the level loop at n={n}"
            );
        }
    }

    /// Pins the k=8 examples the decoupling-fix bug used to panic on. Under the two-phase topology NO
    /// leaf ever survives above height 1: level 0 consumes all leaves into leaf-nodes, then the root
    /// folds only NODES.
    ///   - N=9 (`r=1`): level 0 → leaf-nodes [0..7) and [7..9); root over those two NODES. (Old buggy
    ///     shape was `node([0..8]) + carried Leaf(8)` — a leaf under the lift25 root ⇒ panic.)
    ///   - N=17 (`r=1`): level 0 → [0..8), [8..15), [15..17); root over three NODES.
    #[test]
    fn streaming_topology_n9_n17_example_k8() {
        assert_eq!(FOLD_ARITY, 8, "this pinned example is written for k=8");
        use Shape::{Leaf, Node};
        // N=9: level0_group_sizes = [7, 2] -> two leaf-nodes, root over them; no bare leaf.
        let n9 = Node(vec![
            Node((0..7).map(Leaf).collect()),
            Node((7..9).map(Leaf).collect()),
        ]);
        assert_eq!(streaming_shape(9), n9);
        // N=17: level0_group_sizes = [8, 7, 2] -> three leaf-nodes, root over them.
        let n17 = Node(vec![
            Node((0..8).map(Leaf).collect()),
            Node((8..15).map(Leaf).collect()),
            Node((15..17).map(Leaf).collect()),
        ]);
        assert_eq!(streaming_shape(17), n17);
    }

    /// `build_fold_topology`'s node count and root height match the level loop's actual counts across
    /// every `N mod k` residue. (The count is the level loop's own — a per-level-balanced k-ary carry
    /// tree — NOT the packed-tree `ceil((N-1)/(k-1))`; the loop is the byte-identity source of truth.)
    #[test]
    fn topology_node_count_and_height() {
        for n in 1..=260usize {
            let (tasks, root) = build_fold_topology(n);
            assert_eq!(
                tasks.len(),
                sequential_node_count(n),
                "n={n}: node count diverges from the level loop"
            );
            let h = match root {
                Child::Node(j) => tasks[j].height,
                Child::Leaf(_) => 0,
            };
            assert_eq!(
                h,
                sequential_height(n),
                "n={n}: root height diverges from the level loop"
            );
        }
    }

    /// Arity invariants under the two-phase topology:
    ///   - LEVEL-0 (height-1) leaf-nodes may be short (`2..=k`) — that is how the leaf remainder is
    ///     absorbed instead of carried up.
    ///   - Every height-≥2 (node-verifying) node is exactly-`k` EXCEPT the root, which may be short
    ///     (`2..=k`) with arity == `root_arity(N)` (a deterministic function of the public N).
    /// All arities are in `2..=k` — never a lone (arity-1) node, never 0.
    #[test]
    fn arities_valid_shorts_at_level0_and_root() {
        for n in 2..=260usize {
            let (tasks, root) = build_fold_topology(n);
            let root_idx = match root {
                Child::Node(j) => j,
                Child::Leaf(_) => unreachable!("n>1 root is a node"),
            };
            for (ti, t) in tasks.iter().enumerate() {
                assert!(
                    (2..=FOLD_ARITY).contains(&t.children.len()),
                    "n={n}: node {ti} arity {} out of 2..=k",
                    t.children.len()
                );
                if ti == root_idx {
                    assert_eq!(
                        t.children.len(),
                        root_arity(n),
                        "n={n}: root arity must equal root_arity(N)"
                    );
                } else if t.height >= 2 {
                    // Non-root, node-verifying (height ≥ 2) nodes are always exactly-k.
                    assert_eq!(
                        t.children.len(),
                        FOLD_ARITY,
                        "n={n}: non-root height-≥2 node {ti} is not exactly-k"
                    );
                }
            }
        }
    }

    /// Pins the decoupling-fix invariants on the benchmark-relevant N (the shots the bug hit): the
    /// root arity, that NO leaf appears at height ≥ 1 (every height-≥2 node has only NODE children —
    /// the exact condition whose violation panicked the Merkle height check), and the total node
    /// count. N=64 is a clean power of k (all full-8, no short nodes); N∈{9,35,69} are the previously
    /// broken non-powers.
    #[test]
    fn decoupling_fix_pins_key_n() {
        assert_eq!(FOLD_ARITY, 8, "these pinned expectations are for k=8");
        // (N, expected root_arity, expected total node count).
        // level0_group_sizes: N=9->[7,2] (m1=2); N=35->[8,8,8,6,5]? no: r=3>=2 -> [8,8,8,8,3] (m1=5);
        //   N=64->[8]*8 (m1=8); N=69: r=5>=2 -> [8]*8 + [5] (m1=9).
        // Root fold over m1 nodes: root_arity = phase-B terminal size.
        let cases = [(9usize, 2usize), (35, 5), (64, 8), (69, 2)];
        for (n, want_root_arity) in cases {
            let (tasks, root) = build_fold_topology(n);
            let root_idx = match root {
                Child::Node(j) => j,
                Child::Leaf(_) => unreachable!(),
            };
            assert_eq!(
                tasks[root_idx].children.len(),
                want_root_arity,
                "n={n}: unexpected root arity"
            );
            assert_eq!(root_arity(n), want_root_arity, "n={n}: root_arity mismatch");
            // NO leaf above height 1: every height-≥2 node's children are all Node refs.
            for t in &tasks {
                if t.height >= 2 {
                    assert!(
                        t.children.iter().all(|c| matches!(c, Child::Node(_))),
                        "n={n}: height-{} node has a LEAF child (the decoupling bug)",
                        t.height
                    );
                }
            }
            assert_eq!(
                tasks.len(),
                sequential_node_count(n),
                "n={n}: node count mismatch"
            );
        }
    }

    /// LEAF↔NODE DECOUPLING topology (the fix's core invariant): every height-1 node verifies LEAVES
    /// and so must carry R1 (`NodeLevel::VerifiesLeaves`); every height-≥2 node verifies NODES and so
    /// must carry R2 (`NodeLevel::VerifiesNodes`). This is the selector `prove_node`/`prove_short_node`
    /// and the unpacker share; asserting it over every task pins the per-level R1/R2 assignment the
    /// decoupling depends on — and, crucially, that no height-≥2 node ever has a leaf child.
    ///
    /// Also cross-checks the height itself: a height-1 task's children are ALL leaves, and a
    /// height-≥2 task has at least one node child (so its `max(child height)+1 ≥ 2`).
    #[test]
    fn level1_carries_r1_level_ge2_carries_r2() {
        // Track that both levels actually occur across the swept N (so the test isn't vacuous), plus
        // report whether any N produces only a single node level (all nodes at height 1).
        let mut saw_level1 = false;
        let mut saw_level_ge2 = false;
        for n in 2..=260usize {
            let (tasks, _root) = build_fold_topology(n);
            let is_leaf = |c: &Child| matches!(c, Child::Leaf(_));
            for t in &tasks {
                let level = NodeLevel::from_height(t.height);
                let all_leaf_children = t.children.iter().all(is_leaf);
                if t.height == 1 {
                    assert!(
                        all_leaf_children,
                        "n={n}: height-1 node has a non-leaf child (children={:?})",
                        t.children.len()
                    );
                    assert!(
                        matches!(level, NodeLevel::VerifiesLeaves),
                        "n={n}: height-1 node must select R1 (VerifiesLeaves)"
                    );
                    saw_level1 = true;
                } else {
                    assert!(
                        !all_leaf_children,
                        "n={n}: height-{} node has ONLY leaf children",
                        t.height
                    );
                    assert!(
                        matches!(level, NodeLevel::VerifiesNodes),
                        "n={n}: height-{} node must select R2 (VerifiesNodes)",
                        t.height
                    );
                    saw_level_ge2 = true;
                }
            }
        }
        assert!(saw_level1, "expected some level-1 (R1) nodes in the sweep");
        assert!(
            saw_level_ge2,
            "expected some level-≥2 (R2) nodes in the sweep"
        );
    }
}
