//! In-binary N-leaf `k`-to-1 multiverifier recursion tree.
//!
//! Given an ordered list of `N` leaf circuit proofs, this crate folds the recursion tree above them
//! into a single root proof by repeatedly proving a `FOLD_ARITY`-to-1 [`build_multiverifier_circuit`]
//! node on groups of `k` children. Each node verifies its `k` child proofs and emits a Blake hash
//! binding `[ppRoot_i, outs_i for i in 0..k]` (children left-to-right) as its own `N_RESERVED` output
//! digest words (the full eight-word Blake2s digest); that hash is what the parent node consumes. The
//! node preimage is hashed with `blake2s_u32s`.
//!
//! Arity is the named constant [`FOLD_ARITY`]. Full-`k` nodes at a level share one precompute /
//! `preprocessed_root`; SHORT nodes (the level-0 leaf-remainder groups and the ROOT) are `m`-child
//! with `m ∈ 2..=k` — their arity, and hence circuit shape and `preprocessed_root`, is a
//! deterministic function of the public `N` alone, never prover-chosen.
//!
//! Because the multiverifier *self-verifies* (a multiverifier proof has the same circuit shape as
//! the proof it verifies), a single [`SharedConfig`] works for every internal level, and every
//! internal node reports the same fixed `preprocessed_root`
//! ([`AggregateConfig::node_preprocessed_root`]).
//!
//! This crate folds the multiverifier tree, then proves the **root verification**
//! ([`prove_root_verification_leaves`]) — the only published, and only zk-blinded, proof. Every
//! multiverifier proof, the root included, is internal: consumed (guessed into the witness) by the
//! next circuit up, never published; no multiverifier node is ever blinded.
//!
//! The root verification (1) runs the STARK verifier on the root multiverifier proof in-circuit,
//! and (2) **unpacks** it: it reconstructs the tree's root hash in-circuit from prover-supplied
//! per-leaf output hints — via the same per-node `blake2s_u32s([ppR_i words, outs_i words] for the
//! k children)` binding the nodes used — binds the reconstructed root to the verified root output,
//! and emits the leaf outputs. The unpack is inherently **O(N)** (it touches every leaf). Using one
//! trusted `leaf_preprocessed_root` for all leaves also forces them to share an AIR.
//!
//! The leaf output is the leaf circuit's `output_values`; the unpack rehashes every leaf against the
//! one shared leaf preprocessed root, which is what enforces same-program.
//!
//! Any `N >= 1` is supported via a two-phase deterministic fold:
//!   - **Level 0** consumes ALL `N` leaves into height-1 leaf-verifying nodes (arities from
//!     `level0_group_sizes`, each `2..=k`, never a lone leaf). Leaves and nodes differ in proof shape
//!     (leaf lifting is one below the node's), so a carried-up leaf under a height-≥2 fold would panic
//!     the in-circuit Merkle height check. Consuming every leaf at level 0 guarantees no leaf ever
//!     survives above height 1.
//!   - **Levels ≥ 1** group the height-1 nodes left-to-right into exactly-`k` node-verifying nodes,
//!     carry the `< k` remainder up unchanged (carrying a NODE is safe — all share the node shape),
//!     and fold a final `2..=k` level into the (possibly short) root. Every height-≥2 fold is
//!     homogeneous.
//!
//! One deterministic unbalanced `k`-ary tree of real proofs (no power-of-`k` padding, no dummies). A
//! dynamic permutation-argument unpacker that handles an arbitrary tree shape unknown at
//! circuit-build time is a later optimization.

use std::sync::Arc;

/// Fold arity `k`: each internal node verifies exactly this many children (`k`-to-1 fold).
///
/// The single source of truth for the arity across the recursion pipeline — the tree/streaming fold,
/// the topology, `prove_node`, and the unpacker's per-node hash preimage all read it, so the
/// out-of-circuit unpacker and the in-circuit node hash agree. Re-sweep the arity by changing only
/// this constant; nothing else hard-codes the child count.
///
/// A level's `len() % FOLD_ARITY` (< k) remainder is carried up unchanged, so nodes are always
/// exactly `k` children — never variable-child.
pub const FOLD_ARITY: usize = 8;

/// Default recursion (node-node / root) FRI blowup factor. Feeds the ~96-bit-secure `(pow_bits,
/// n_queries)` table via `get_pcs_config`; the value that makes production node/root proofs.
pub const RECURSION_LOG_BLOWUP: u32 = 3;

/// Default base (shard / "leaf") proof FRI blowup factor. `(pow_bits, n_queries)` and lifting
/// are derived from it via `leaf_pcs_config` to a ~96-bit-secure config. Sweep knob: 1/2/3.
pub const BASE_LOG_BLOWUP: u32 = 1;

/// Default shots (iadd256 executions) per base shard — the manual partition knob. `n_shards =
/// ceil(samples / shots_per_shard)`.
pub const SHOTS_PER_SHARD: usize = 2;

/// All FREE topology parameters, in one place, threaded through the recursion + base-proof pipeline.
///
/// Every field is a *free knob*; everything else (the `(pow_bits, n_queries)` at 96-bit, the trusted
/// roots, the PCS/padding targets, `n_shards`, the base-shard trace log) is DERIVED from these.
/// Security params (`fold_step`, `log_last_layer`, the 96-bit floor, `INTERACTION_POW_BITS`) are
/// pinned, NOT exposed here — they must never be swept below the security floor.
///
/// Construct once (via [`TopologyConfig::from_env`] on the production path, or a literal in a test)
/// and thread it: `fold_arity` rides on the [`AggregateConfig`] (so every config-carrying fold fn
/// reads `config.fold_arity`), while the blowups / `shots_per_shard` are read at the construction /
/// derivation sites.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TopologyConfig {
    /// Base (shard) proof FRI blowup factor. Default [`BASE_LOG_BLOWUP`] (env `BASE_BLOWUP`).
    pub base_log_blowup: u32,
    /// Recursion (node-node / root) FRI blowup factor. Default [`RECURSION_LOG_BLOWUP`].
    pub recursion_log_blowup: u32,
    /// Leaf-wrap FRI blowup factor — the multiverifier leaf that verifies a base proof. Default
    /// [`RECURSION_LOG_BLOWUP`] (env `LEAF_BLOWUP`), i.e. equal to `recursion_log_blowup` unless
    /// overridden. Decoupled from the R1/R2 node blowup so the leaf-wrap trace/lift (which scales
    /// with shots/shard) can be tuned independently; R1 verifies leaves at whatever this is.
    pub leaf_log_blowup: u32,
    /// Node-node fold arity `k` (each internal R2 node verifies exactly `k` children). Default
    /// [`FOLD_ARITY`].
    pub fold_arity: usize,
    /// Shots per base shard (partition knob). Default [`SHOTS_PER_SHARD`] (env `RECURSION_SHARD_SHOTS`).
    pub shots_per_shard: usize,
}

impl Default for TopologyConfig {
    /// Production values. Bottom-layer topology is the standalone-leaf → level-0 leaf-verifying (R1)
    /// → shared R2 up-tree fold.
    fn default() -> Self {
        TopologyConfig {
            base_log_blowup: BASE_LOG_BLOWUP,
            recursion_log_blowup: RECURSION_LOG_BLOWUP,
            leaf_log_blowup: RECURSION_LOG_BLOWUP,
            fold_arity: FOLD_ARITY,
            shots_per_shard: SHOTS_PER_SHARD,
        }
    }
}

impl TopologyConfig {
    /// The topology config in effect, applying the env overrides existing sweep scripts rely on:
    /// `BASE_BLOWUP` → `base_log_blowup`, `RECURSION_SHARD_SHOTS` → `shots_per_shard` (`> 0`),
    /// `RECURSION_FOLD_ARITY` → `fold_arity` (clamped `>= 2`), `LEAF_BLOWUP` → `leaf_log_blowup`.
    /// `recursion_log_blowup` keeps its [`Default`] value (no env knob today). Unset /
    /// unparseable env vars fall back to the default, so with a clean environment this equals
    /// [`TopologyConfig::default`] exactly (in particular `fold_arity` stays 8 unless
    /// `RECURSION_FOLD_ARITY` is explicitly set, e.g. `=4` for the a2 sweep).
    pub fn from_env() -> Self {
        fn parse_env<T: std::str::FromStr>(k: &str) -> Option<T> {
            std::env::var(k).ok().and_then(|s| s.parse().ok())
        }
        let d = TopologyConfig::default();
        TopologyConfig {
            base_log_blowup: parse_env("BASE_BLOWUP").unwrap_or(d.base_log_blowup),
            recursion_log_blowup: d.recursion_log_blowup,
            leaf_log_blowup: parse_env("LEAF_BLOWUP").unwrap_or(d.leaf_log_blowup),
            fold_arity: parse_env::<usize>("RECURSION_FOLD_ARITY")
                .unwrap_or(d.fold_arity)
                .max(2),
            shots_per_shard: parse_env::<usize>("RECURSION_SHARD_SHOTS")
                .filter(|&n| n > 0)
                .unwrap_or(d.shots_per_shard),
        }
    }
}

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
use circuits::ivalue::IValue;
use circuits::ops::{Guess, eq};
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
/// LEAF/R1/R2. The bottom of the tree is a standalone **leaf** (one base proof verified in
/// its own circuit). `recursive_aggregate` consumes ALL leaves at level 0 into height-1 **leaf-
/// verifying (R1)** nodes ([`recursive_aggregate_prove_leaves`]) and then folds those up the tree with
/// `FOLD_ARITY` via the shared **R2** node-node fold. The R2 machinery is:
///   - **R2** ([`node_preprocessed_root`]) — height-≥2 full-`k` nodes, which verify `FOLD_ARITY`
///     NODES (child config [`node_shared_config`], the multiverifier's own shape — the
///     self-verifying fixed point).
/// The leaf/R1 tier's trusted roots + configs live in the LeafR1R2 fields below.
///
/// SHORT nodes (arity `2..=k-1`: the level-0 leaf-node-remainder groups and the short root) have a
/// structurally different circuit ⇒ a DISTINCT preprocessed root per (level, arity). These are not
/// stored here; they are recomputed on the fly (`prove_short_node` when proving, and
/// `short_node_preprocessed_root` in the unpacker) from the public (level, arity) — never
/// prover-chosen. All node variants pad to a COMMON `node_target_padding_sizes` so their *output*
/// proofs share one shape (one [`node_shared_config`], one node PCS).
pub struct AggregateConfig {
    /// Verifier/prover config for a node whose CHILDREN are NODES (level-≥2 nodes) and for
    /// verifying the ROOT proof in the unpacker. Built from the multiverifier node's own
    /// preprocessed shape (the self-verifying fixed point). A base-node's own proof shares this shape
    /// (padded to the common `node_target_padding_sizes`), so R2 verifies base-nodes with it too.
    pub node_shared_config: SharedConfig,
    /// **R2** — the preprocessed root of a level-≥2 (node-verifying) multiverifier node. Reported by
    /// every internal node of height ≥ 2 to its parent.
    pub node_preprocessed_root: HashValue<QM31>,
    /// Padding targets applied to every node's trace, so all node *proofs* share one circuit shape
    /// (hence one `node_shared_config`).
    pub node_target_padding_sizes: ComponentSizes,
    /// PCS config used to prove each NODE and to VERIFY the root (a node proof) in
    /// [`prove_root_verification_leaves`]. A node proof's Merkle auth-path height is
    /// `node_log_size + log_blowup`; this field carries the node-sized lifting.
    pub node_pcs_config: PcsConfig,
    /// Node-node fold arity `k` in effect (from [`TopologyConfig::fold_arity`]). Carried on the config
    /// so every config-threaded fold fn (`recursive_aggregate_prove`, `prove_node`, `prove_short_node`,
    /// the unpacker, the root-consistency check) reads the SAME `k` — the single source of truth the
    /// out-of-circuit unpacker and the in-circuit node hash both depend on.
    pub fold_arity: usize,

    // ---- LEAF/R1 bottom-layer tier -----------------------------------------------------------------
    // The three-tier bottom layer (standalone leaf → level-0 leaf-verifying R1 node → shared R2 up-tree
    // fold), populated by the downstream leaf prover's config derivation. `Option` for historical
    // reasons (they were `None` for an alternate bottom layer that no longer exists); always `Some`
    // today. The shared height-≥2 R2 fold above the bottom layer uses ONLY `node_shared_config` /
    // `node_preprocessed_root`, so it is untouched.
    /// Verifier/prover config for a level-1 node whose CHILDREN are LEAVES. Built from the leaf
    /// circuit's preprocessed shape (`shared_config_for_leaf`); also deserializes the leaf proofs a
    /// level-1 (R1) node verifies.
    pub leaf_shared_config: Option<SharedConfig>,
    /// **R1** — the preprocessed root of a level-1 (leaf-verifying) multiverifier node. Reported by
    /// every height-1 leaf-node to its R2 parent.
    pub level1_preprocessed_root: Option<HashValue<QM31>>,
    /// The trusted preprocessed root of the leaf circuit (same AIR for every leaf). The unpacker uses
    /// this single constant for *all* leaves.
    pub leaf_preprocessed_root: Option<HashValue<QM31>>,
    /// Padding targets applied to every LEAF's trace — the leaf's OWN target (~2^20), decoupled from
    /// the node size so `t_leaf` is pinned independent of `FOLD_ARITY`.
    pub leaf_target_padding_sizes: Option<ComponentSizes>,
    /// PCS config used to prove each LEAF (and to describe the leaf proof shape a level-1 node
    /// verifies). Leaf lifting ~24 (below the node's ~25).
    pub leaf_pcs_config: Option<PcsConfig>,
}

/// Witness-independent proving precompute for the whole recursion, built UP FRONT from public params
/// (decoupled from [`AggregateConfig`] so the recursion config stays pure metadata and the heavy
/// [`CircuitPrecompute`] builds happen off the critical path). A field is `None` when the
/// corresponding tier is inactive (or in the precompute-OFF control arm the
/// `recursion_precompute_identity` byte-identity test builds), falling back to the self-contained
/// [`prove_circuit_assignment`] path that rebuilds tree0 each call.
pub struct RecursionPrecompute {
    /// Precompute for the level-≥2 (node-verifying, R2) multiverifier node circuit. Reused for every
    /// [`prove_node`] call at height ≥ 2.
    pub node_precompute: Option<Arc<CircuitPrecompute>>,
    /// Precompute for the level-1 (leaf-verifying, R1) multiverifier node circuit, reused for every
    /// [`prove_leaf_or_short`] full-`k` call.
    pub level1_precompute: Option<Arc<CircuitPrecompute>>,
    /// Precompute for the leaf circuit, reused for every leaf-prover call.
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

/// Lower THIS thread's scheduling priority (called once per pool worker at startup).
/// Byte-neutral: only a scheduling syscall, touches no proof data. Unprivileged: raising nice
/// and SCHED_IDLE need no CAP_SYS_NICE. `who==0` targets the calling thread's task (per-thread
/// nice on Linux).
fn apply_pool_thread_priority(sched: Option<&str>) {
    match sched {
        None => {}
        Some("idle") | Some("IDLE") => {
            let p = libc::sched_param { sched_priority: 0 };
            unsafe {
                libc::sched_setscheduler(0, libc::SCHED_IDLE, &p);
            }
        }
        Some(s) => {
            let nice: i32 = s.parse().unwrap_or(10);
            unsafe {
                libc::setpriority(libc::PRIO_PROCESS, 0, nice);
            }
        }
    }
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
        // Deprioritize wrap/fold pool workers so the GPU-producer / composition host-dispatch
        // threads win CPU during the bursty composition phase. Byte-neutral (scheduling only).
        // OFF unless RECURSION_POOL_NICE is set: an integer nice delta (e.g. 12), or "idle" (SCHED_IDLE).
        let sched = std::env::var("RECURSION_POOL_NICE").ok();
        let pools = (0..n_pools.max(1))
            .map(|_| {
                let sched = sched.clone();
                Arc::new(
                    rayon::ThreadPoolBuilder::new()
                        .num_threads(threads_per_pool)
                        .start_handler(move |_| apply_pool_thread_priority(sched.as_deref()))
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

    /// Runs `f` on pool `i % n_pools`, blocking until it completes (its internal rayon work uses
    /// that pool's cores). Unlike [`map`], this dispatches ONE job at a time, so a caller can stream
    /// jobs onto specific pools as they arrive (e.g. wrapping bases into leaves as base-proving
    /// produces them) rather than handing over a whole batch up front.
    pub fn install_on<T, F>(&self, i: usize, f: F) -> T
    where
        F: FnOnce() -> T + Send,
        T: Send,
    {
        self.pools[i % self.pools.len()].install(f)
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

/// The SHARED up-tree R2 fold: folds `nodes` (each a height-1 node proof — the level-0 leaf-verifying
/// R1 nodes from [`recursive_aggregate_prove_leaves`]) into a single root proof by repeatedly proving
/// `FOLD_ARITY`-to-1 multiverifier nodes.
///
/// The bottom of the tree (the R1 leaf-verifying layer) is already done before this is called, so this
/// is JUST the group+carry node-node fold over height-1 nodes (the produced R2 nodes are
/// height ≥ 2). Any `M >= 1` nodes:
///   - `M == 1`: the lone node IS the root (no further fold).
///   - `M >= 2`: group the leading full-`k` runs into exactly-`k` node-verifying (R2) nodes and carry
///     the `< k` remainder up unchanged; the first level to reach `2..=k` entries folds whole into
///     the (possibly short) root. Every internal node-node is exactly-`k` (shares `node_precompute` /
///     R2); the root may be short (arity `root_arity(M)`), proved via [`prove_short_node`].
///
/// Sibling groups at each level are independent and are proved concurrently across `pools` (a lone
/// group — e.g. the last fold step — runs on the full machine).
///
/// # Panics
/// If `base_nodes` is empty.
pub fn recursive_aggregate_prove(
    base_nodes: Vec<TreeProof>,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!base_nodes.is_empty(), "need at least one base-node");
    // Fold arity `k`, threaded via the config (the single source of truth shared with the unpacker).
    let k = config.fold_arity;

    // M == 1: the lone base-node is itself the root (no fold). Its height is 1.
    if base_nodes.len() == 1 {
        return AggregateOutput {
            root: base_nodes.into_iter().next().unwrap(),
            n_levels: 1,
        };
    }

    // Seed the fold with the base-nodes at height 1. A node's height is `max(child heights) + 1`,
    // matching `build_fold_topology`'s per-task `height`, which selects R2 (height ≥ 2,
    // verifies nodes). No R_base node is ever built here (base-nodes arrive already proved).
    let mut level: Vec<(usize, TreeProof)> =
        base_nodes.into_iter().map(|bn| (1usize, bn)).collect();

    // --- group+carry over NODES only (all base-nodes / R2 nodes share the node proof shape). ---
    while level.len() > 1 {
        if level.len() <= k {
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
        let remainder = level.len() % k;
        let carry: Vec<(usize, TreeProof)> = level.split_off(level.len() - remainder);
        // Consume `level` into exactly-k groups, computing each group's height (max child + 1)
        // before moving its proofs into a prove closure — no proof is cloned.
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
            .map(|(height, children)| move || (*height, prove_node(children, config, pre, *height)))
            .collect();
        let mut next: Vec<(usize, TreeProof)> = pools.map(jobs);
        next.extend(carry);
        level = next;
    }

    // M >= 2 always folds to a root above (the loop's terminal step returns it); reaching here means
    // the loop exited with a single carried entry, which is that root.
    let (height, root) = level.into_iter().next().unwrap();
    AggregateOutput {
        root,
        n_levels: height,
    }
}

/// The arity of the ROOT node of the fold tree over `m` base-nodes — a deterministic function of the
/// public base-node count `M` (SOUNDNESS: the root shape is public, never prover-chosen).
///
/// The group+carry loop folds the `M` base-NODES (levels with `> k` entries carry the `< k`
/// remainder and emit `len / k` exactly-`k` node-nodes; the first level to reach `2..=k` folds whole
/// into the root). Returns that terminal size (`∈ 2..=k`). For `m == 1` there is no fold (returns
/// `1`, the lone base-node is the root).
pub fn root_arity(m_base_nodes: usize, k: usize) -> usize {
    if m_base_nodes == 1 {
        return 1;
    }
    let mut len = m_base_nodes;
    while len > k {
        len = len / k + len % k;
    }
    len
}

/// A reference to one input of a streaming fold node: either a fold INPUT supplied from below (by
/// input index, in canonical arrival order — a base-node in the base-node streamer, an R1 node in the
/// leaves streamer) or the output of an earlier fold node (by fold-task index). Input-neutral names:
/// the concrete kind of an `Input` depends on which streaming path builds the topology.
#[derive(Clone, Copy)]
enum Child {
    Input(usize),
    Fold(usize),
}

/// One fold in the fixed tree: prove an R2 node over `children` base-nodes/nodes, children
/// left-to-right. An internal task has `children.len() == FOLD_ARITY`; the single ROOT task may be
/// short (`2..=k`). The arity is `children.len()` and the level is `NodeLevel::from_height(height)`
/// (always `VerifiesNodes` here — every fold task is height ≥ 2, verifying base-nodes/nodes).
struct FoldTask {
    children: Vec<Child>,
    /// Height above the bases of this node's output (bases are height 0; base-nodes are height 1;
    /// the first fold produced here is height 2).
    height: usize,
}

/// Computes the FIXED node-node fold topology for `m_base_nodes` base-nodes, decided up front and
/// independent of completion order, realizing the same tree as [`recursive_aggregate_prove`]'s level
/// loop.
///
/// The base-nodes are height 1 (proved upstream); this runs the group+carry loop over them: while a
/// level has `> k` entries it groups the leading full-`k` runs left-to-right into `prove_node(group)`
/// and carries the trailing `< k` remainder up unchanged; a level of `2..=k` entries is folded whole
/// into the root. The returned `Vec<FoldTask>` is in the same order the level loop would prove them;
/// the returned [`Child`] is the root (a `Fold` for `m > 1`, else `Input(0)` = the lone base-node).
/// `Child::Input(i)` denotes base-node `i`. Each task's `children` order matches `prove_node`'s
/// exactly, so each node sees the same inputs as the sequential fold.
fn build_fold_topology(m_base_nodes: usize, k: usize) -> (Vec<FoldTask>, Child) {
    if m_base_nodes == 1 {
        return (Vec::new(), Child::Input(0));
    }
    let mut tasks: Vec<FoldTask> = Vec::new();

    // Seed the level with the `m` base-nodes at height 1 (each a `Child::Input(i)` = base-node i).
    let mut level: Vec<(usize, Child)> = (0..m_base_nodes).map(|i| (1, Child::Input(i))).collect();

    // --- group+carry over NODES only (base-nodes and R2 nodes share the node proof shape). ---
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
        // Carry the `< k` remainder up unchanged (all NODES now — safe under decoupling).
        next.extend(carry);
        level = next;
    }
    (tasks, level[0].1)
}

/// Proves ONE tier-≥1 fold task over its ordered `children`, dispatching EXACTLY as the sequential
/// fold. Every fold task is a node-node fold (height ≥ 2, verifies base-nodes/nodes ⇒ R2); its
/// children arrive already proved:
///   - the ROOT (`is_root`) ⇒ [`prove_short_node`] (the self-contained recompute path) even at
///     arity `FOLD_ARITY` — the sequential terminal step ALWAYS uses it, so the streaming root must
///     too;
///   - every non-root internal node: full-`k` ⇒ [`prove_node`] (precompute, fixed R2), short
///     (impossible for a non-root here) ⇒ [`prove_short_node`].
///
/// Pure function of `(children, is_root, height, config, pre)` — no channel / seed / scheduling
/// state — so completion order cannot affect its result. Shared by BOTH streaming coordinators
/// ([`recursive_aggregate_prove_streaming`] and [`recursive_aggregate_prove_leaves_streaming`]) so
/// the tier-≥1 dispatch logic cannot diverge between them.
fn run_fold_task(
    children: &[TreeProof],
    is_root: bool,
    height: usize,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
) -> TreeProof {
    let k = config.fold_arity;
    if is_root {
        prove_short_node(children, config, height)
    } else if children.len() == k {
        prove_node(children, config, pre, height)
    } else {
        prove_short_node(children, config, height)
    }
}

/// Streaming variant of [`recursive_aggregate_prove`]: folds base-nodes as they arrive over a
/// channel, dispatching each fold to a [`PoolSet`] worker the instant all its children are ready — so
/// the node-node fold runs concurrently with (and overlaps) the upstream base-node producer feeding
/// `rx`.
///
/// This exists so the GPU base-proving + base-node producer can overlap with the CPU fold consumer.
/// The producer is modelled as a stream of completed base-node proofs sent over `rx` in **canonical
/// order** (base-node `i` is the `i`-th `recv()`), NOT as GPU calls — this crate stays
/// leaf-type-agnostic.
///
/// DETERMINISM: the result does not depend on completion order — it matches
/// [`recursive_aggregate_prove`] for the same ordered base-nodes. The topology is FIXED up front by
/// [`build_fold_topology`] (group+carry over the `m` base-nodes; e.g. at k=8 the m=9 root is
/// `node([node([0..7]), node([7..9])])`); every [`FoldTask`] sees the same ordered children the
/// sequential fold gives its matching `prove_node`/`prove_short_node`. Because those are pure
/// functions of their ordered children, identical topology + identical per-node inputs ⇒ the same
/// root proof.
///
/// Streaming schedule: one coordinator owns the dataflow state; `pools.n_pools()` workers (one per
/// pool) pull ready folds and run the fold via [`ThreadPool::install`]. As base-nodes arrive on `rx`,
/// any fold whose `k` children are now available becomes ready; a fold completing makes its parent's
/// child available in turn. Up to `n_pools()` folds run at once while later base-nodes are still
/// being produced.
///
/// Consumes exactly `m_base_nodes` from `rx` in arrival order. Returns the same [`AggregateOutput`]
/// as the level loop. For `m_base_nodes == 1` returns the single base-node as root with
/// `n_levels = 1` (the base-node itself is height 1).
///
/// # Panics
/// If `m_base_nodes == 0`, or if `rx` yields fewer than `m_base_nodes` entries.
pub fn recursive_aggregate_prove_streaming(
    rx: std::sync::mpsc::Receiver<TreeProof>,
    m_base_nodes: usize,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(m_base_nodes >= 1, "need at least one base-node");
    // Fold arity `k`, threaded via the config (must match the sequential path + the unpacker).
    let k = config.fold_arity;

    let (tasks, root_ref) = build_fold_topology(m_base_nodes, k);

    if m_base_nodes == 1 {
        let root = rx.recv().expect("streaming fold: missing base-node 0");
        return AggregateOutput { root, n_levels: 1 };
    }

    // For each task, count its not-yet-available children and record which task consumes each
    // produced value, so completing a fold (or receiving a leaf) can decrement the right parent.
    //   parent_of[Input i] / parent_of_fold[Fold j] = Some((task_idx, slot)), slot = child position
    //   in the task's `children` (left-to-right), so inputs reassemble in the fold's exact order.
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
        // No parent ⇒ this is the root value; the root is always a Fold here (n_leaves > 1).
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
                    // `prove_root_verification_leaves`) + the O(log_k N) in-flight fold path, never all the
                    // node proofs.
                    let children: Vec<TreeProof> = {
                        let mut st = state.lock().unwrap();
                        st.inputs[ti]
                            .iter_mut()
                            .map(|slot| slot.take().unwrap())
                            .collect()
                    };
                    // Dispatch EXACTLY as the sequential fold (via the shared `run_fold_task`), so
                    // the two paths produce the same result.
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
                        // Wake idle workers: either a new fold is ready, or all folds are done.
                        cv.notify_all();
                    }
                }
            });
        }

        // Coordinator: drain base-nodes in canonical order, delivering each to its consumer. A
        // base-node that completes a fold's inputs enqueues it; workers pick it up immediately, so
        // folds overlap with the still-arriving later base-nodes.
        for &parent in &input_parent {
            let base_node = rx
                .recv()
                .expect("streaming fold: fewer base-nodes than m_base_nodes");
            let mut st = state.lock().unwrap();
            deliver(&mut st, parent, base_node);
            cv.notify_all();
        }
    });

    // All folds complete; pull the root the root fold captured.
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

// =================================================================================================
// LEAF/R1/R2 bottom layer. Confined to the BOTTOM layer + config + unpacker; the shared height-≥2 R2
// up-tree fold (`recursive_aggregate_prove`, `prove_node`, `prove_short_node`, `build_node_context`,
// `build_fold_topology`) is reused. The caller proves standalone leaves upstream; the level-0 layer
// below consumes ALL leaves into height-1 leaf-verifying (R1) nodes, then delegates the up-tree fold
// to the shared path.
// =================================================================================================

/// A node's tree level, which selects its shape under leaf↔node padding decoupling.
/// A **level-1** node verifies `FOLD_ARITY` LEAVES (child config
/// `leaf_shared_config`) and reports **R1** (`level1_preprocessed_root`); a **level-≥2** node verifies
/// NODES (child config `node_shared_config`) and reports **R2** (`node_preprocessed_root`). The level
/// is fixed by the public topology (`FoldTask::height`), never prover-chosen. Only the leaf-node
/// bottom layer uses `VerifiesLeaves`; the shared up-tree fold is always `VerifiesNodes`.
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

    /// The child-verifier config: `leaf_shared_config` (R1) for leaf children, `node_shared_config`
    /// (R2) for node children. Panics if the leaf config is absent (i.e. not a `LeafR1R2` config).
    fn shared_config(self, config: &AggregateConfig) -> &SharedConfig {
        match self {
            NodeLevel::VerifiesLeaves => config
                .leaf_shared_config
                .as_ref()
                .expect("leaf_shared_config required for a leaf-verifying (R1) node — LeafR1R2 mode"),
            NodeLevel::VerifiesNodes => &config.node_shared_config,
        }
    }

    /// The trusted preprocessed root a node of this level reports (R1 vs R2).
    fn preprocessed_root(self, config: &AggregateConfig) -> HashValue<QM31> {
        match self {
            NodeLevel::VerifiesLeaves => config
                .level1_preprocessed_root
                .clone()
                .expect("level1_preprocessed_root required for an R1 node — LeafR1R2 mode"),
            NodeLevel::VerifiesNodes => config.node_preprocessed_root.clone(),
        }
    }

    /// The witness-independent precompute for this level's node circuit, if built.
    fn precompute(self, pre: &RecursionPrecompute) -> Option<&Arc<CircuitPrecompute>> {
        match self {
            NodeLevel::VerifiesLeaves => pre.level1_precompute.as_ref(),
            NodeLevel::VerifiesNodes => pre.node_precompute.as_ref(),
        }
    }
}

/// The arities of the LEVEL-0 (leaf-verifying) nodes for `n_leaves`, left-to-right — a deterministic
/// function of the public `N` and fold arity `k` (SOUNDNESS: public topology,
/// never prover-chosen).
///
/// LEAF↔NODE DECOUPLING FIX: leaves (lift24) and nodes (lift25) have different proof shapes, so a
/// carried-up leaf landing under a height-≥2 (node-verifying, lift25) fold panics the in-circuit
/// Merkle height check. To prevent that, ALL leaves are consumed at level 0 into height-1 leaf-nodes.
/// Contiguous groups, each an arity in `2..=k`, NEVER a lone leaf:
///   - `N <= k`: one group of arity `N` (that node IS the root).
///   - `N > k`, `r = N % k`: `r == 0` -> `N/k` full-`k`; `r >= 2` -> `N/k` full-`k` then one arity-`r`
///     group; `r == 1` -> `(N/k - 1)` full-`k` then arity-`(k-1)` and arity-`2` groups (the `k+1`
///     trailing leaves split so every arity stays in `2..=k` with no lone leaf).
///
/// # Panics
/// If `n_leaves < 2` (callers handle the lone-leaf no-fold case before calling this).
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

/// Builds and pads (to the common `node_target_padding_sizes`) the multiverifier circuit that verifies
/// `children`, using the child-verifier config for the node's `level`.
/// Distinct from the shared `build_node_context` (always R2) — this selects the child config by level.
fn build_leaf_node_context(
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

/// Proves one LEVEL-0 (height-1, leaf-verifying) node over `children` leaves:
/// full-`k` groups go through the R1 precompute/`prove_circuit_assignment` path (reporting R1); short
/// groups (`2..=k-1`) recompute their real root R1'(m). `height` is always 1.
fn prove_leaf_or_short(
    children: &[TreeProof],
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    height: usize,
) -> TreeProof {
    debug_assert_eq!(height, 1, "level-0 leaf nodes are always height 1");
    let level = NodeLevel::VerifiesLeaves;
    let _t_node = std::time::Instant::now();
    let full = children.len() == config.fold_arity;
    let mut context = build_leaf_node_context(children, config, level);

    let (preprocessed_root_reported, circuit_proof) = if full {
        // Full-`k` leaf-node: reuse the R1 precompute (or the self-contained path) and report the
        // fixed R1.
        let cp = match level.precompute(pre) {
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
        (level.preprocessed_root(config), cp)
    } else {
        // Short leaf group: distinct shape, rebuild tree0 and report the recomputed real root R1'(m).
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

/// Folds standalone `leaves` into a single root proof. LEVEL 0 consumes ALL
/// leaves into height-1 leaf-verifying (R1) nodes via [`level0_group_sizes`] + [`prove_leaf_or_short`]
/// (so no leaf survives above height 1), then the SHARED [`recursive_aggregate_prove`] folds those
/// height-1 leaf-nodes up the tree with the identical R2 group+carry.
///
/// `n_leaves == 1`: the lone leaf is the root (no fold, `n_levels == 0`). `N <= k`: the single level-0
/// leaf-node is the root (`n_levels == 1`), same as delegating a 1-element vec to the shared fold.
///
/// # Panics
/// If `leaves` is empty, or if the config lacks the `LeafR1R2` extras.
pub fn recursive_aggregate_prove_leaves(
    leaves: Vec<TreeProof>,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!leaves.is_empty(), "need at least one leaf");
    assert!(
        config.leaf_shared_config.is_some(),
        "recursive_aggregate_prove_leaves requires a LeafR1R2 config (leaf_shared_config present)"
    );
    let k = config.fold_arity;

    // n_leaves == 1: the lone leaf is itself the root (no fold, height 0).
    if leaves.len() == 1 {
        return AggregateOutput {
            root: leaves.into_iter().next().unwrap(),
            n_levels: 0,
        };
    }

    // --- Level 0: consume ALL leaves into height-1 leaf-verifying (R1) nodes. After this every entry
    //     is a NODE, so the shared up-tree fold sees only nodes (homogeneous, no carried leaf). ---
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

    // --- Levels ≥ 1: SHARED up-tree R2 fold over the height-1 leaf-nodes (a lone leaf-node is
    //     returned as the root at n_levels 1). ---
    recursive_aggregate_prove(leaf_nodes, config, pre, pools)
}

/// The three job kinds the unified streaming coordinator schedules onto its single worker pool
/// ([`recursive_aggregate_prove_leaves_streaming`], "hide the fold behind base-proving"). One
/// ready-queue holds all three; workers are symmetric pull-workers, so there is no per-kind thread
/// (no oversubscription) and no ordering hazard — ordering does NOT affect the result (see the
/// determinism invariants on `recursive_aggregate_prove_leaves_streaming`).
#[derive(Clone, Copy)]
enum Job {
    /// Wrap the arrived producer input at leaf index `i` into leaf `i` (the injected AIR-specific
    /// wrap closure). Producer-driven: enqueued when `(i, w)` arrives on `rx`.
    Wrap(usize),
    /// Prove level-0 (leaf→R1) group `g` over its contiguous `level0_group_sizes` leaf range. Ready
    /// when all of the group's leaves have been wrapped.
    R1(usize),
    /// Prove tier-≥1 fold task `t` (the shared node-node R2 fold, [`build_fold_topology`]). Ready
    /// when all its children (R1 nodes / earlier fold nodes) are available.
    Fold(usize),
}

/// Overlapped ("hide the fold behind base-proving", Model 1) variant of
/// [`recursive_aggregate_prove_leaves`]: wraps the streamed producer inputs into leaves AND folds
/// the whole tree (level-0 leaf→R1 layer + shared up-tree R2 fold) PROGRESSIVELY, as leaves and
/// nodes become ready — concurrently with the still-arriving producer feeding `rx`. This lets the
/// GPU base-producer overlap with the CPU wrap + fold instead of the fold running as a separate tail
/// after every leaf is collected.
///
/// LEAF-AGNOSTIC: the AIR-specific leaf-wrap is INJECTED as `wrap: impl Fn(W) -> TreeProof` and the
/// producer's per-leaf input `W` is generic, so this crate stays leaf-type-agnostic (the downstream
/// leaf prover passes its own base-maker + leaf-prover callback as `wrap`, and streams
/// `(leaf_idx, base)`). The heavy `wrap` runs INSIDE a pool worker (`pool.install`).
///
/// Streaming schedule (Model 1): one coordinator owns the dataflow state; `pools.n_pools()` SYMMETRIC
/// pull-workers each pull one ready [`Job`] and run it on their pool's cores. The single ready-queue
/// holds three job kinds — `Wrap` (producer-driven), `R1` (ready when its group's leaves are all
/// wrapped), `Fold` (ready when its children are available). Fold-priority (`Fold` > `R1` > `Wrap`)
/// drains sub-trees first to bound host RAM; because every prove is a pure function of its ordered
/// inputs, this priority — and the resulting completion order — does NOT change the result.
///
/// DETERMINISM: the result does not depend on completion order — it matches
/// [`recursive_aggregate_prove_leaves`] for the same ordered leaves. Topology is FIXED up front by
/// the SAME [`level0_group_sizes`] (tier 0) + [`build_fold_topology`] (tier ≥ 1); child ordering is
/// by INDEX (leaf `i` → group `group_of(i)` at slot `i - offset`; tier-≥1 children in their fixed
/// [`FoldTask`] slots), and every node dispatch uses the SAME predicates via [`prove_leaf_or_short`]
/// (tier 0) and [`run_fold_task`] (tier ≥ 1). Out-of-order completion only changes WHEN a slot fills.
///
/// Returns BOTH the ordered `Vec<TreeProof>` leaves (leaf `i` = the wrap of the input streamed with
/// index `i`) — for the `LeafBottom` unpacker + the fingerprint's base-nodes — AND the same
/// [`AggregateOutput`] as [`recursive_aggregate_prove_leaves`].
///
/// Consumes exactly `n_leaves` items from `rx` (in ARBITRARY arrival order; each tagged with its
/// canonical leaf index). Edge cases: `n_leaves == 1` recvs the one input, wraps it, and returns it
/// as the root (`n_levels == 0`), no workers; `2 <= n_leaves <= k` yields `M == 1` so the single
/// level-0 R1 node IS the root (`n_levels == 1`).
///
/// # Panics
/// If `n_leaves == 0`, if the config lacks the `LeafR1R2` extras, if `rx` yields fewer than
/// `n_leaves` items, or if any leaf index arrives twice / out of `0..n_leaves`. A `wrap` panic (or a
/// fold panic) re-panics on the parent via `thread::scope` join — no hang, no silent drop.
pub fn recursive_aggregate_prove_leaves_streaming<W: Send>(
    rx: std::sync::mpsc::Receiver<(usize, W)>,
    n_leaves: usize,
    wrap: impl Fn(W) -> TreeProof + Sync,
    config: &AggregateConfig,
    pre: &RecursionPrecompute,
    pools: &PoolSet,
) -> (Vec<TreeProof>, AggregateOutput) {
    assert!(n_leaves >= 1, "need at least one leaf");
    assert!(
        config.leaf_shared_config.is_some(),
        "recursive_aggregate_prove_leaves_streaming requires a LeafR1R2 config (leaf_shared_config present)"
    );
    let k = config.fold_arity;

    // n_leaves == 1: the lone wrapped leaf is itself the root (no fold, height 0). Mirror
    // `recursive_aggregate_prove_leaves`. No workers.
    if n_leaves == 1 {
        let (idx, w) = rx.recv().expect("streaming leaves fold: missing leaf 0");
        assert_eq!(idx, 0, "single-leaf stream must carry index 0");
        let leaf = wrap(w);
        let out = AggregateOutput { root: leaf.clone(), n_levels: 0 };
        return (vec![leaf], out);
    }

    // --- Tier 0 (leaf→R1) topology: contiguous leaf groups, a pure function of public (n, k). ---
    let sizes = level0_group_sizes(n_leaves, k);
    let m = sizes.len(); // number of R1 nodes (= build_fold_topology's base-node count)
    debug_assert_eq!(
        sizes.iter().sum::<usize>(),
        n_leaves,
        "level0 groups must cover all leaves"
    );
    // leaf i -> (group g, slot within group). Contiguous left-to-right: leaf i is slot `s` of group
    // `g` (determinism invariant: child ordering is by index).
    let leaf_group: Vec<(usize, usize)> = sizes
        .iter()
        .enumerate()
        .flat_map(|(g, &sz)| (0..sz).map(move |s| (g, s)))
        .collect();
    debug_assert_eq!(leaf_group.len(), n_leaves);

    // --- Tier ≥ 1 (R2 up-tree) topology over the m R1 nodes: reuse the SAME fixed DAG the sequential
    //     fold realizes. `build_fold_topology`'s inputs are its height-1 base-nodes, which in THIS
    //     path are the R1 nodes — so here a `Child::Input(g)` denotes R1 node g's output (and a
    //     `Child::Fold(j)` an earlier tier-≥1 fold task), unlike the base-node streamer where an
    //     `Input(i)` is a base-node. ---
    let (tasks, root_ref) = build_fold_topology(m, k);

    // Per-task readiness (mirrors `recursive_aggregate_prove_streaming`): which task+slot consumes
    // each R1 node output / each fold node output, and each task's pending-child count.
    let mut r1_parent: Vec<Option<(usize, usize)>> = vec![None; m];
    let mut node_parent: Vec<Option<(usize, usize)>> = vec![None; tasks.len()];
    let mut fold_pending: Vec<usize> = vec![0; tasks.len()];
    let fold_arity_of: Vec<usize> = tasks.iter().map(|t| t.children.len()).collect();
    for (ti, t) in tasks.iter().enumerate() {
        for (slot, ch) in t.children.iter().enumerate() {
            fold_pending[ti] += 1;
            match ch {
                Child::Input(g) => r1_parent[*g] = Some((ti, slot)),
                Child::Fold(j) => node_parent[*j] = Some((ti, slot)),
            }
        }
    }

    // Dataflow state shared between the coordinator and the workers. Three ready sub-queues, popped
    // Fold > R1 > Wrap (drains sub-trees first to bound host RAM; ordering is byte-irrelevant).
    struct State<W> {
        // Tier 0: pending producer inputs (awaiting a Wrap worker), per-group remaining leaf count,
        // and each group's resolved leaf inputs (slotted by index).
        wrap_inputs: Vec<Option<W>>,
        r1_remaining: Vec<usize>,
        r1_inputs: Vec<Vec<Option<TreeProof>>>,
        // Tier ≥ 1: resolved child inputs + pending child counts (as in the base-node streamer).
        fold_inputs: Vec<Vec<Option<TreeProof>>>,
        fold_pending: Vec<usize>,
        // Ready sub-queues (Fold-priority).
        ready_fold: std::collections::VecDeque<usize>,
        ready_r1: std::collections::VecDeque<usize>,
        ready_wrap: std::collections::VecDeque<usize>,
        // Ordered leaves to return (leaf i = wrap of input streamed with index i).
        leaves_out: Vec<Option<TreeProof>>,
        done: usize,
        // Root proof, captured when the no-parent node (an R1 node if m == 1, else a fold task)
        // completes.
        root: Option<TreeProof>,
    }
    // Total scheduled jobs: n_leaves wraps + m R1 nodes + tasks.len() fold tasks.
    let n_jobs = n_leaves + m + tasks.len();
    let state = std::sync::Mutex::new(State::<W> {
        wrap_inputs: (0..n_leaves).map(|_| None).collect(),
        r1_remaining: sizes.clone(),
        r1_inputs: sizes.iter().map(|&s| (0..s).map(|_| None).collect()).collect(),
        fold_inputs: fold_arity_of
            .iter()
            .map(|&a| (0..a).map(|_| None).collect())
            .collect(),
        fold_pending,
        ready_fold: std::collections::VecDeque::new(),
        ready_r1: std::collections::VecDeque::new(),
        ready_wrap: std::collections::VecDeque::new(),
        leaves_out: (0..n_leaves).map(|_| None).collect(),
        done: 0,
        root: None,
    });
    let cv = std::sync::Condvar::new();

    // Deliver a completed fold/R1 node output into its consuming tier-≥1 task (or capture the root
    // when there is no parent). Mutates `st` under its lock.
    let deliver_node = |st: &mut State<W>, parent: Option<(usize, usize)>, proof: TreeProof| {
        match parent {
            Some((ti, slot)) => {
                st.fold_inputs[ti][slot] = Some(proof);
                st.fold_pending[ti] -= 1;
                if st.fold_pending[ti] == 0 {
                    st.ready_fold.push_back(ti);
                }
            }
            None => st.root = Some(proof), // the root (m == 1 ⇒ R1 node 0; else the root fold task)
        }
    };

    let n_workers = pools.n_pools().max(1);
    std::thread::scope(|s| {
        for pool in pools.pools.iter().take(n_workers) {
            let state = &state;
            let cv = &cv;
            let deliver_node = &deliver_node;
            let r1_parent = &r1_parent;
            let node_parent = &node_parent;
            let leaf_group = &leaf_group;
            let sizes = &sizes;
            let tasks = &tasks;
            let wrap = &wrap;
            s.spawn(move || {
                loop {
                    // Pull one ready job, Fold > R1 > Wrap (drains sub-trees; byte-irrelevant order).
                    let job = {
                        let mut st = state.lock().unwrap();
                        loop {
                            if let Some(t) = st.ready_fold.pop_front() {
                                break Job::Fold(t);
                            }
                            if let Some(g) = st.ready_r1.pop_front() {
                                break Job::R1(g);
                            }
                            if let Some(i) = st.ready_wrap.pop_front() {
                                break Job::Wrap(i);
                            }
                            if st.done == n_jobs {
                                return;
                            }
                            st = cv.wait(st).unwrap();
                        }
                    };
                    match job {
                        // --- Tier 0a: wrap producer input `i` into leaf `i` (injected AIR closure). ---
                        Job::Wrap(i) => {
                            let w = {
                                let mut st = state.lock().unwrap();
                                st.wrap_inputs[i].take().expect("wrap input missing")
                            };
                            let leaf = pool.install(|| wrap(w));
                            let (g, slot) = leaf_group[i];
                            let mut st = state.lock().unwrap();
                            // Record the ordered leaf for the caller's return + slot it into its R1
                            // group by INDEX (determinism invariant).
                            st.leaves_out[i] = Some(leaf.clone());
                            st.r1_inputs[g][slot] = Some(leaf);
                            st.r1_remaining[g] -= 1;
                            if st.r1_remaining[g] == 0 {
                                st.ready_r1.push_back(g);
                            }
                            st.done += 1;
                            cv.notify_all();
                        }
                        // --- Tier 0b: prove level-0 (leaf→R1) group `g` (full-k or short). ---
                        Job::R1(g) => {
                            let children: Vec<TreeProof> = {
                                let mut st = state.lock().unwrap();
                                st.r1_inputs[g]
                                    .iter_mut()
                                    .map(|slot| slot.take().unwrap())
                                    .collect()
                            };
                            debug_assert_eq!(children.len(), sizes[g]);
                            // R1 nodes are always height 1; `prove_leaf_or_short` dispatches full-k
                            // vs short exactly as `recursive_aggregate_prove_leaves`'s level-0 layer.
                            let result =
                                pool.install(|| prove_leaf_or_short(&children, config, pre, 1));
                            let mut st = state.lock().unwrap();
                            deliver_node(&mut st, r1_parent[g], result);
                            st.done += 1;
                            cv.notify_all();
                        }
                        // --- Tier ≥ 1: shared node-node R2 fold task (same dispatch as sequential). ---
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

        // Coordinator: drain the producer inputs (arbitrary order, each tagged with its leaf index)
        // and enqueue a Wrap job per input, so wrap + R1 + fold overlap the still-arriving producer.
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

    // All jobs complete; assemble the ordered leaves + the root.
    let mut st = state.into_inner().unwrap();
    let leaves: Vec<TreeProof> = st
        .leaves_out
        .iter_mut()
        .enumerate()
        .map(|(i, l)| l.take().unwrap_or_else(|| panic!("leaf {i} missing after streaming fold")))
        .collect();
    let root = st.root.take().expect("root not produced");
    // n_levels mirrors `recursive_aggregate_prove_leaves` -> `recursive_aggregate_prove`: m == 1 ⇒
    // the lone R1 node is the root at height 1; else the root fold task's height.
    let n_levels = match root_ref {
        Child::Input(_) => 1, // m == 1: the single level-0 R1 node is the root
        Child::Fold(j) => tasks[j].height,
    };
    (leaves, AggregateOutput { root, n_levels })
}

/// The preprocessed root a SHORT node of the given `level` and `arity` (`2..=k-1`) reports —
/// recomputed witness-independently over that level's child config (`leaf_shared_config` for an R1
/// leaf-node, `node_shared_config` for an R2 node), identical to what [`prove_leaf_or_short`] /
/// [`prove_short_node`] recompute for the same shape. Pure function of the public `(level, arity)`.
///
/// The two level-specialised recomputes ([`short_leaf_node_preprocessed_root`] /
/// [`short_node_preprocessed_root`]) differ ONLY in which child config `level.shared_config` selects;
/// this is their shared body, so the recompute lives in one place.
fn short_node_preprocessed_root_at_level(
    config: &AggregateConfig,
    level: NodeLevel,
    arity: usize,
) -> HashValue<QM31> {
    let shared = level.shared_config(config);
    let pp = node_preprocessed_from_shared(
        shared,
        config.node_target_padding_sizes.clone(),
        arity,
    );
    preprocessed_root(&pp, config.node_pcs_config.fri_config.log_blowup_factor)
}

/// The preprocessed root a SHORT leaf-verifying (R1) node of the given `arity` (`2..=k-1`) reports —
/// recomputed witness-independently over `leaf_shared_config`, identical to what
/// [`prove_leaf_or_short`] recomputes for the same shape. Pure function of
/// the public `arity`.
fn short_leaf_node_preprocessed_root(config: &AggregateConfig, arity: usize) -> HashValue<QM31> {
    short_node_preprocessed_root_at_level(config, NodeLevel::VerifiesLeaves, arity)
}

/// The single reported-root selector: the trusted preprocessed root a fold node of the given public
/// `(height, arity)` reports to its parent — identical to what the PROVER reports for that node
/// and what the unpacker BAKES for it. The level is [`NodeLevel::from_height`] (`height == 1` ⇒ R1
/// leaf-verifying, else R2 node-verifying); the arity selects full-`k` vs short:
///   - full-`k` (`arity == config.fold_arity`) ⇒ the trusted fixed root ([`NodeLevel::preprocessed_root`]):
///     R1 (`level1_preprocessed_root`) or R2 (`node_preprocessed_root`);
///   - short (`2..=k-1`) ⇒ the recomputed real root for that shape
///     ([`short_node_preprocessed_root_at_level`]): short R1'(m) or short-root.
///
/// This is the ONE place the R1/R2/short 3-way choice lives, so the prover's per-node report and the
/// unpacker's baked constant are structurally the same value, not hand-matched copies.
fn reported_root(config: &AggregateConfig, height: usize, arity: usize) -> HashValue<QM31> {
    let level = NodeLevel::from_height(height);
    if arity == config.fold_arity {
        level.preprocessed_root(config)
    } else {
        short_node_preprocessed_root_at_level(config, level, arity)
    }
}

/// The bottom-level input to the unpacker: the ordered standalone leaves
/// (each a proved height-0 leaf `TreeProof` reporting `leaf_preprocessed_root`).
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

/// Bakes a canonical preprocessed root (eight `(lo, hi, 0, 0)`-packed u32 words) into the circuit as
/// eight `context.constant` wires, yielding a [`HashValue<Var>`] usable exactly where a *guessed*
/// root was. SOUNDNESS: a constant is part of the circuit's FIXED data (constants are hashed into the
/// preprocessed output; see stwo-circuits `finalize_context`), so the trusted final verifier's
/// canonical-unpacker-root check PINS these roots — a prover cannot substitute a forged value the way
/// it could for a guessed witness. Because the QM31 value fed to `context.constant` is identical in
/// the QM31 prove pass and the NoValue recompute pass, the two build identical preprocessed
/// traces (the obligation the trusted verifier relies on).
fn constant_pp<Value: IValue>(
    context: &mut Context<Value>,
    pp: &HashValue<QM31>,
) -> HashValue<Var> {
    HashValue(std::array::from_fn(|i| {
        // Each digest word is a QM31 `(low_u16, high_u16, 0, 0)` packing a u32 (see
        // `HashValue<QM31>::from(Blake2sHash)`); bake that exact QM31 as one constant wire.
        U32Wrapper::new_unsafe(context.constant(*pp[i].get()))
    }))
}

/// Builds the LEAF/R1/R2 root-verification unpacker circuit, generic over `Value`, through finalize +
/// (optional) zk-blinding + power-of-two padding — the SINGLE code path shared by the QM31 prove
/// ([`prove_root_verification_leaves`]) and the NoValue canonical-root recompute
/// ([`leaf_r1r2_unpacker_preprocessed_root`] / [`leaf_r1r2_unpacker_verify_config`], used by the
/// trusted final verifier). Sharing one builder is what guarantees the recomputed canonical
/// preprocessed root equals the published proof's: identical gate structure, identical
/// baked constants, identical blinding/padding. The standalone-leaf bottom is the level-0
/// leaf-verifying R1 layer (via [`level0_group_sizes`]).
///
/// `root_proof` / `leaf_output_values` carry the witness (real for QM31, `empty_proof` + `NoValue`
/// for the recompute); `root_output_values` and every preprocessed root are QM31 constants that do
/// NOT depend on `Value` (so the shape is value-independent). Every child preprocessed root (the leaf
/// tree0 root + each fold-node's reported R1/R2/short root) is a CANONICAL config-derived value, BAKED
/// as a constant ([`constant_pp`]) so the canonical-root check pins the whole reconstructed fold to
/// canonical — a guessed root would be an unpinned witness a malicious prover could forge.
fn build_leaf_r1r2_root_verification_context<Value: IValue>(
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
    let leaf_preprocessed_root = config
        .leaf_preprocessed_root
        .clone()
        .expect("leaf_preprocessed_root required for the LeafR1R2 unpacker (LeafR1R2 mode)");
    // Fold arity `k` — must match the fold that built `root` + the unpacker's own group+carry.
    let k = config.fold_arity;

    // Exposes every leaf's N_RESERVED outputs.
    let mut context = Context::<Value>::new(n * N_RESERVED);

    // (1) Verify the root multiverifier proof in-circuit (a NODE proof, node_shared_config / node PCS).
    let circuit_config = CircuitConfig {
        config: config.node_pcs_config,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: config
            .node_shared_config
            .preprocessed_column_log_sizes
            .clone(),
        preprocessed_root: root_preprocessed_root.clone(),
    };
    let statement = CircuitStatement::new(&mut context, &circuit_config, root_output_values);
    let proof_vars = root_proof.guess(&mut context);
    verify(
        &mut context,
        &proof_vars,
        &config.node_shared_config.proof_config,
        &statement,
    );
    let root_out_vars: Vec<Var> = statement.get_output_values().to_vec();

    // (2) Unpack: reconstruct the tree root from the guessed per-leaf outputs and bind it.
    // Every child preprocessed root (the leaf tree0 root + each fold-node's reported root) is a
    // CANONICAL config-derived value, so it is BAKED as a `constant_pp` (a constant is part of the
    // circuit's fixed data, pinned by a trusted canonical-unpacker-root check), NOT guessed. A guessed
    // root would be an unpinned witness a malicious prover could set to a forged value; a baked
    // constant cannot.
    // One trusted leaf tree0 root for EVERY leaf (forces a shared leaf AIR).
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

    // Shared child-preimage hash for one ordered group — matches the in-circuit node hash in
    // `build_multiverifier_circuit`.
    let fold_hash = |context: &mut Context<Value>,
                     group: &[(usize, HashValue<Var>, Vec<Var>)]|
     -> Vec<Var> {
        let mut preimage: Vec<U32Wrapper<Var>> = Vec::new();
        for (_, pp, outs) in group {
            let output_words = unpack_qm31s_to_u32_words(context, outs.iter().copied());
            preimage.extend(pp.iter().copied().chain(output_words));
        }
        let n_bytes = 4 * preimage.len();
        let h = blake2s_u32s(context, preimage, n_bytes);
        h.iter().map(|w| *w.get()).collect()
    };

    // `fold_group` folds one ordered group into a node, BAKING the SAME reported preprocessed root the
    // prover reported as a constant (selected by public (height, arity): R1 vs R2 (full-`k`) or the
    // recomputed short root — short leaf-node R1'(m) / short root). The value is pinned (constant), so
    // a wrong reconstructed root can only miss the verified root ⇒ REJECTED, never accepted-invalid.
    let fold_group = |context: &mut Context<Value>,
                      group: &[(usize, HashValue<Var>, Vec<Var>)]|
     -> (usize, HashValue<Var>, Vec<Var>) {
        let outs = fold_hash(context, group);
        let height = group.iter().map(|(h, _, _)| *h).max().unwrap() + 1;
        // ONE reported-root selector (R1/R2/short by public (height, arity)) shared with the prover.
        let node_pp = constant_pp(context, &reported_root(config, height, group.len()));
        (height, node_pp, outs)
    };

    // --- BOTTOM (LEVEL 0): consume ALL leaves into height-1 leaf-nodes (per level0_group_sizes). ---
    // n == 1: the lone leaf is itself the root (no fold), matching recursive_aggregate_prove_leaves.
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
                fold_group(&mut context, &group)
            })
            .collect();
        drop(leaves_iter);
        level0
    };

    // --- LEVELS ≥ 1: SHARED group+carry over NODES only (identical to prove_root_verification_leaves). ---
    while level.len() > 1 {
        if level.len() <= k {
            let root = fold_group(&mut context, &level);
            level = vec![root];
            break;
        }
        let remainder = level.len() % k;
        let carry: Vec<(usize, HashValue<Var>, Vec<Var>)> =
            level.split_off(level.len() - remainder);
        let mut next = Vec::with_capacity(level.len() / k + remainder);
        for group in level.chunks(k) {
            next.push(fold_group(&mut context, group));
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

    // (4) Finalize, (optionally) blind, pad to power-of-two sizes. No `validate_circuit` here (generic
    //     over `Value`; the QM31 prove path validates the returned padded context itself).
    let mut context = context.finalize(false);
    if let Some(zk) = zk_blind {
        add_zk_blinding(&mut context, zk.seed, zk.n_padding);
    }
    pad_context(&mut context);
    context
}

/// Recomputes the CANONICAL LeafR1R2 unpacker preprocessed root for the trusted public `(n, config)`,
/// witness-independently — the value the trusted final verifier (the downstream root verifier)
/// checks the published `rv.proof` against. Rebuilds the SAME unpacker
/// circuit the prover built (via the shared [`build_leaf_r1r2_root_verification_context`], but with a
/// `NoValue` witness: `empty_proof` + zero leaf outputs), then preprocesses and roots it. Because the
/// two passes share one builder and the same baked constants + blinding `n_padding`, this equals the
/// published proof's preprocessed root by construction.
///
/// All child roots the unpacker bakes (leaf tree0, R1/R2, short leaf-node / short root) are CANONICAL
/// config-derived values already on `config` (`leaf_preprocessed_root`, `level1_preprocessed_root`,
/// `node_preprocessed_root`, recomputed short variants) — the trusted verifier must pass a `config`
/// whose roots are the canonical (trusted) values, all derived from trusted public `(n, config)`,
/// NEVER from the prover. `zk_n_padding` must equal the prover's blinding `n_padding` (the root PCS
/// `n_queries`) so the blinding rows match; `None` means no blinding.
pub fn leaf_r1r2_unpacker_preprocessed_root(
    n: usize,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_n_padding: Option<usize>,
) -> HashValue<QM31> {
    // The ROOT node's own preprocessed root is guessed inside `CircuitStatement::new` (a witness), so
    // its concrete value does NOT affect the preprocessed trace shape; a placeholder is sufficient.
    let root_pp = HashValue::from([0u32; N_RESERVED]);
    let zk_blind = zk_n_padding.map(|n_padding| ZkBlind { seed: [0u8; 32], n_padding });
    let root_output_values = [QM31::zero(); N_RESERVED];
    let leaf_output_values = vec![[NoValue; N_RESERVED]; n];
    let mut context = build_leaf_r1r2_root_verification_context::<NoValue>(
        empty_proof(&config.node_shared_config.proof_config),
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

/// Recomputes the full [`CircuitConfig`] the TRUSTED FINAL VERIFIER uses to `verify_circuit` the
/// published LeafR1R2 root-verification proof, from the trusted public `(n, config)` —
/// witness-independently, via the SAME shared builder ([`build_leaf_r1r2_root_verification_context`])
/// the prover used, for the standalone-leaf bottom:
///   - `preprocessed_root` = the canonical unpacker root (the pin: a forged reconstruction that bakes
///     a non-canonical child root produces a different preprocessed root ⇒ this config rejects it),
///   - `preprocessed_column_log_sizes` / `config` (PCS) = the recomputed trace's own shape,
///   - `n_outputs` = `n * N_RESERVED` (one leaf output per leaf).
///
/// The caller (the downstream root verifier) passes `rv.proof` + the CALLER-COMMITTED
/// `rv.leaf_outputs` as `CircuitPublicData`. See [`leaf_r1r2_unpacker_preprocessed_root`] for the
/// `(n, config, zk_n_padding)` trust contract (all recomputed from trusted public params, never from
/// the prover).
pub fn leaf_r1r2_unpacker_verify_config(
    n: usize,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_n_padding: Option<usize>,
) -> CircuitConfig {
    let root_pp = HashValue::from([0u32; N_RESERVED]);
    let zk_blind = zk_n_padding.map(|n_padding| ZkBlind { seed: [0u8; 32], n_padding });
    let root_output_values = [QM31::zero(); N_RESERVED];
    let leaf_output_values = vec![[NoValue; N_RESERVED]; n];
    let mut context = build_leaf_r1r2_root_verification_context::<NoValue>(
        empty_proof(&config.node_shared_config.proof_config),
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

/// Builds and proves the **root verification** — the only published, only zk-blinded proof — for the
/// standalone-leaf topology. Two phases: verify the root multiverifier proof in-circuit, then
/// reconstruct + bind the tree root and emit the leaf outputs. The BOTTOM reconstruction guesses each
/// LEAF's `(leaf_preprocessed_root, output_values)`, groups the leaves into height-1 leaf-nodes via
/// [`level0_group_sizes`] (each reporting R1 for a full-`k` group, else the recomputed short R1'(m)),
/// then folds those up with the SHARED level-≥1 R2 group+carry. Reconstructs the same shape
/// [`recursive_aggregate_prove_leaves`] folds. The circuit-BUILD is factored into the shared generic
/// [`build_leaf_r1r2_root_verification_context`] so the NoValue canonical-root recompute the trusted
/// verifier runs builds the identical circuit.
///
/// `bottom.leaves` must be the same ordered leaves fed to [`recursive_aggregate_prove_leaves`], and
/// `root` the returned root. Requires a `LeafR1R2` config.
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
    let mut context = build_leaf_r1r2_root_verification_context::<QM31>(
        root.proof.clone(),
        &root.output_values,
        &root.preprocessed_root,
        &leaf_output_values,
        n,
        config,
        zk_blind,
    );
    // Correctness tripwire (QM31 prove pass only — the shared builder skips it because it also runs
    // witness-free for the `NoValue` recompute). Validating the final padded context covers the
    // pre-blind and post-blind checks.
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

// Every node the SHARED up-tree fold (`recursive_aggregate_prove`) builds verifies NODE children
// (height-1 R1 leaf-nodes, or R2 nodes at height ≥ 2) with a single node kind: `node_shared_config`
// (child config, the self-verifying fixed point), reporting R2 (`node_preprocessed_root`) at full
// arity, and a recomputed short-root real root at a short arity (the short ROOT only). The unpacker
// selects the trusted reported root by public (height, arity) — R2 for full-`k` and
// `short_node_preprocessed_root` for the short root. (The level-0 R1 leaf-verifying layer is built by
// `recursive_aggregate_prove_leaves` before the shared fold runs.)

/// Builds and pads (to the common `node_target_padding_sizes`) the multiverifier circuit that
/// verifies `children` (R1/R2 nodes) with `node_shared_config`.
fn build_node_context(children: &[TreeProof], config: &AggregateConfig) -> FinalizedContext<QM31> {
    let inputs: Vec<MultiverifierInput<QM31>> = children.iter().map(child_input).collect();
    let mut context = build_multiverifier_circuit::<QM31>(inputs, &config.node_shared_config);
    pad_to_targets(&mut context, config.node_target_padding_sizes.clone());
    context.validate_circuit();
    context
}

/// Proves one exactly-`FOLD_ARITY` INTERNAL R2 node verifying `children` (base-nodes / R2 nodes;
/// `children.len() == FOLD_ARITY`). Reports **R2** (`node_preprocessed_root`) and reuses
/// `node_precompute`. `height` (≥ 2) is recorded for the measurement log only.
fn prove_node(
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
    let mut context = build_node_context(children, config);

    let circuit_proof = match pre.node_precompute.as_ref() {
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
        preprocessed_root: config.node_preprocessed_root.clone(),
        output_values,
    }
}

/// Proves one SHORT R2 node (arity `m ∈ 2..=FOLD_ARITY`) verifying `children` (base-nodes / R2
/// nodes). Used for the short ROOT (the terminal fold step). A short node's circuit shape differs
/// from the exactly-`k` internal shape (fewer child-verify sub-circuits), so it cannot reuse
/// `node_precompute`; it is proved via the self-contained rebuild path. Its reported
/// `preprocessed_root` is the circuit's *real* preprocessed root (recomputed here) — a value fixed by
/// the node's arity (a deterministic function of the public base-node count), hence verifier-derivable
/// (the unpacker recomputes the identical value via [`short_node_preprocessed_root`]) and never
/// prover-chosen. When `m == FOLD_ARITY` this yields exactly the same shape (and root) as a full-`k`
/// internal node.
fn prove_short_node(children: &[TreeProof], config: &AggregateConfig, height: usize) -> TreeProof {
    assert!(
        (2..=config.fold_arity).contains(&children.len()),
        "short/root fold node must have 2..=fold_arity children (got {})",
        children.len()
    );
    let _t_node = std::time::Instant::now();
    let mut context = build_node_context(children, config);

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
// leaves of a given circuit's config.
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

/// The `NoValue` node `ProofConfig` a multiverifier NODE circuit is built/proved with, sized over
/// `all_circuit_components::<NoValue>()` + `INTERACTION_POW_BITS` for `n_preprocessed_columns`
/// preprocessed columns and `pcs_config`. Shared by [`node_preprocessed_from_shared`] and
/// [`multiverifier_node_preprocessed`] so the two NoValue node builders derive the config the same way
/// (they only differ in where `n_preprocessed_columns` / the log sizes come from).
fn noval_node_proof_config(n_preprocessed_columns: usize, pcs_config: &PcsConfig) -> ProofConfig {
    ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        n_preprocessed_columns,
        pcs_config,
        INTERACTION_POW_BITS,
    )
}

/// A placeholder `NoValue` multiverifier child input (empty proof + zeroed root/outputs) for building
/// the witness-independent node shape — the preprocessed trace does not depend on child values.
fn empty_node_input(proof_config: &ProofConfig) -> MultiverifierInput<NoValue> {
    MultiverifierInput {
        proof: empty_proof(proof_config),
        preprocessed_root: HashValue::from([0u32; N_RESERVED]),
        output_values: [QM31::zero(); N_RESERVED],
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

/// The preprocessed root a SHORT R2 node of the given `arity` (`2..=FOLD_ARITY-1`, the short ROOT)
/// reports — recomputed witness-independently over `node_shared_config`, identical to what
/// [`prove_short_node`] recomputes for the same shape. Pure function of the public `arity`, so the
/// unpacker binds the same value the prover reported.
fn short_node_preprocessed_root(config: &AggregateConfig, arity: usize) -> HashValue<QM31> {
    short_node_preprocessed_root_at_level(config, NodeLevel::VerifiesNodes, arity)
}

impl AggregateConfig {
    /// Defense-in-depth consistency check: the full-`FOLD_ARITY` node-node root recomputed via
    /// [`short_node_preprocessed_root`] must equal the trusted R2 (`node_preprocessed_root`) the
    /// unpacker binds full-`k` nodes to. They agree by construction (same node circuit shape via
    /// `node_preprocessed_from_shared`); a divergence is fail-closed (the root verification rejects
    /// via the missing-root reconstruction), so this just turns the recompute equivalence into a loud
    /// check. (The cached precompute already asserts tree0 == root in [`CircuitPrecompute::new`].)
    pub fn assert_full_arity_roots_consistent(&self) {
        let k = self.fold_arity;
        assert_eq!(
            short_node_preprocessed_root(self, k),
            self.node_preprocessed_root,
            "full-{k} node-node preprocessed root recompute != trusted R2",
        );
        // Also check the R1 (leaf-verifying) full-`k` root against its recompute, which matters in
        // the genuinely decoupled R1 != R2 regime.
        if let Some(level1_root) = &self.level1_preprocessed_root {
            assert_eq!(
                short_leaf_node_preprocessed_root(self, k),
                *level1_root,
                "full-{k} leaf-node preprocessed root recompute != trusted R1",
            );
        }
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
    fold_arity: usize,
) -> (PreprocessedCircuit, ComponentSizes) {
    let proof_config =
        noval_node_proof_config(leaf_preprocessed.preprocessed_trace.n_columns(), &pcs_config);
    let shared = SharedConfig {
        pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: leaf_preprocessed.preprocessed_trace.log_sizes(),
    };
    // The internal node shape is exactly-`fold_arity` children (matches `prove_node`).
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

#[cfg(test)]
mod topology_tests {
    use super::{
        Child, FOLD_ARITY, build_fold_topology, level0_group_sizes,
        root_arity,
    };

    /// The arity these topology tests run at — the [`TopologyConfig`](super::TopologyConfig) default
    /// (`fold_arity = FOLD_ARITY`). Threaded explicitly into `build_fold_topology`/`root_arity` (which
    /// now take `k`) so the tests exercise the production default; the k=8-pinned expectations below
    /// assert `K == 8` so they trip loudly if the default ever changes.
    const K: usize = FOLD_ARITY;

    /// A symbolic tree shape, index-aware — the byte-identity-relevant structure of the node-node fold
    /// tree over the base-nodes (each node's ordered children and the resulting nesting). `Leaf(i)` is
    /// base-node `i` (the fold's height-1 inputs, proved upstream).
    #[derive(PartialEq, Eq, Debug)]
    enum Shape {
        Leaf(usize),
        Node(Vec<Shape>),
    }

    /// The shape `recursive_aggregate_prove`'s node-node fold builds over `m` base-nodes, computed over
    /// indices — the `k`-ary group+carry over the base-nodes (leading full-`k` runs into
    /// nodes, `< k` remainder carried up, a `2..=k` level folded whole into the root). The single
    /// source of truth the topology must match. `m == 1` ⇒ the lone base-node is the root.
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

    /// Reference count of R2 nodes the node-node fold proves over `m` base-nodes (`m == 1` ⇒ 0, the
    /// lone base-node is the root; base-nodes themselves are proved upstream, not counted here).
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

    /// Reference root height of the node-node fold over `m` base-nodes: base-nodes are height 1, each
    /// fold level adds 1 (`m == 1` ⇒ height 1, the lone base-node IS the root).
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

    /// The shape the streaming scheduler realizes, reconstructed from `build_fold_topology`'s task
    /// list + root reference. Each task's ordered `children` resolve to the same `Shape` nodes,
    /// proving the streaming dataflow folds the identical tree with the identical child inputs.
    fn streaming_shape(m: usize) -> Shape {
        let (tasks, root) = build_fold_topology(m, K);
        fn resolve(c: Child, tasks: &[super::FoldTask]) -> Shape {
            match c {
                Child::Input(i) => Shape::Leaf(i),
                Child::Fold(j) => Shape::Node(
                    tasks[j].children.iter().map(|&ch| resolve(ch, tasks)).collect(),
                ),
            }
        }
        resolve(root, &tasks)
    }

    /// The streamed tree is byte-identical to the sequential one because it has the IDENTICAL shape:
    /// same nesting, same base-node-index-to-child-slot assignment for every node. Since `prove_node`
    /// is a pure function of its ordered children, identical shape + identical per-node inputs ⇒
    /// identical proof bytes and `recursion_fingerprint`. Checks every `m` up to 260 base-nodes —
    /// covers ALL `m mod k` residues at k=FOLD_ARITY across several levels, plus power-of-k boundaries.
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

    /// Pins k=8 group+carry examples over base-nodes (the fold's height-1 inputs).
    ///   - m=9 (`r=1`): root over `node([0..8]) + carried Leaf(8)`? No — the loop carries the `< k`
    ///     remainder and folds the whole `2..=k` level into the root, so m=9 → `node([node([0..8]),
    ///     Leaf(8)])` where Leaf(8) is a carried base-node (a NODE, safe to carry).
    ///   - m=17 (`r=1`): 17 base-nodes → first level `node([0..8]), node([8..16])` + carried Leaf(16)
    ///     → root over those three.
    #[test]
    fn streaming_topology_m9_m17_example_k8() {
        assert_eq!(K, 8, "this pinned example is written for k=8 (the TopologyConfig default)");
        use Shape::{Leaf, Node};
        // m=9: 9 > 8 ⇒ first level groups [0..8) into one node, carries base-node 8; 2 entries ≤ k ⇒
        // root over [node([0..8)), Leaf(8)].
        let m9 = Node(vec![Node((0..8).map(Leaf).collect()), Leaf(8)]);
        assert_eq!(streaming_shape(9), m9);
        // m=17: first level [0..8),[8..16) + carried base-node 16 ⇒ 3 entries ≤ k ⇒ root over them.
        let m17 = Node(vec![
            Node((0..8).map(Leaf).collect()),
            Node((8..16).map(Leaf).collect()),
            Leaf(16),
        ]);
        assert_eq!(streaming_shape(17), m17);
    }

    /// `build_fold_topology`'s R2-node count and root height match the reference over `m` base-nodes,
    /// across every `m mod k` residue. `m == 1` ⇒ no fold node, root is the lone base-node at height 1.
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

    /// Arity invariants of the node-node fold over `m` base-nodes: every non-root R2 fold node is
    /// exactly-`k`; the root may be short (`2..=k`) with arity == `root_arity(m)`. Every fold task is
    /// height ≥ 2 (base-nodes are the height-1 inputs). All arities are in `2..=k`.
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
                    // Non-root fold nodes are always exactly-k.
                    assert_eq!(
                        t.children.len(),
                        K,
                        "m={m}: non-root fold node {ti} is not exactly-k"
                    );
                }
            }
        }
    }

    /// Pins k=8 root arities + total R2-node count for the group+carry fold over `m` base-nodes.
    /// m=8 is a clean full-`k` root (one node, no shorts); m∈{9,35,69} exercise the carry.
    ///   - m=8: root over [0..8) (arity 8, 1 node).
    ///   - m=9: [node([0..8)), carried 8] → root arity 2 (2 nodes total).
    ///   - m=35: 35 = 4·8 + 3 → level1 = 4 full-8 nodes + carried 3 = 7 entries ≤ k → root arity 7
    ///     (5 nodes total).
    ///   - m=69: 69 = 8·8 + 5 → level1 = 8 full-8 nodes + carried 5 = 13 entries > k → level2 =
    ///     node([those 8]) + carried 5 = 6 entries → root arity 6 (8 + 1 + 1 = 10 nodes total).
    #[test]
    fn fold_pins_key_m() {
        assert_eq!(K, 8, "these pinned expectations are for k=8 (the TopologyConfig default)");
        // (m, expected root_arity).
        let cases = [(8usize, 8usize), (9, 2), (35, 7), (69, 6)];
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

    // =====================================================================================
    // Two-tier (leaf→R1→R2) streaming DAG topology tests ([`recursive_aggregate_prove_leaves_
    // streaming`], Model 1). SYMBOLIC — no proving. They prove that the coordinator's fixed DAG
    // (tier 0 = `level0_group_sizes`, tier ≥ 1 = `build_fold_topology` over the R1 nodes) folds
    // the SAME tree, with the SAME per-node child ordering, that `recursive_aggregate_prove_leaves`
    // realizes — the byte-identity invariant the streaming path relies on.
    // =====================================================================================

    /// A symbolic two-tier tree shape over standalone leaves: `Leaf(i)` = leaf i, `R1(children)` =
    /// a level-0 leaf-verifying node over its leaves, `R2(children)` = a node-node fold over R1/R2
    /// nodes. Index-aware, so it captures the byte-identity-relevant child ordering at every node.
    #[derive(PartialEq, Eq, Debug, Clone)]
    enum LeafShape {
        Leaf(usize),
        R1(Vec<LeafShape>),
        R2(Vec<LeafShape>),
    }

    /// The tree `recursive_aggregate_prove_leaves` realizes over `n` leaves: level 0 slices the
    /// leaves into `level0_group_sizes(n, k)` contiguous R1 nodes, then the SHARED up-tree fold
    /// (`recursive_aggregate_prove`, mirrored by `sequential_shape` over the m R1 nodes) folds those
    /// into the root. `n == 1` ⇒ the lone leaf is the root (no R1). Reference for the streaming DAG.
    fn sequential_leaf_shape(n: usize) -> LeafShape {
        if n == 1 {
            return LeafShape::Leaf(0);
        }
        // Tier 0: contiguous leaf groups → R1 nodes (indices 0..m in left-to-right leaf order).
        let sizes = level0_group_sizes(n, K);
        let mut next_leaf = 0usize;
        let r1_nodes: Vec<LeafShape> = sizes
            .iter()
            .map(|&sz| {
                let children = (0..sz)
                    .map(|_| {
                        let l = LeafShape::Leaf(next_leaf);
                        next_leaf += 1;
                        l
                    })
                    .collect();
                LeafShape::R1(children)
            })
            .collect();
        assert_eq!(next_leaf, n);
        let m = r1_nodes.len();
        // Tier ≥ 1: the group+carry over the m R1 nodes (same loop as `sequential_shape`),
        // but the height-1 inputs are the R1 nodes themselves. m == 1 ⇒ that R1 node IS the root.
        if m == 1 {
            return r1_nodes.into_iter().next().unwrap();
        }
        let mut level: Vec<LeafShape> = r1_nodes;
        while level.len() > 1 {
            if level.len() <= K {
                return LeafShape::R2(level);
            }
            let remainder = level.len() % K;
            let carry: Vec<LeafShape> = level.split_off(level.len() - remainder);
            let mut nxt: Vec<LeafShape> = Vec::new();
            let mut iter = level.into_iter().peekable();
            while iter.peek().is_some() {
                let group: Vec<LeafShape> = iter.by_ref().take(K).collect();
                nxt.push(LeafShape::R2(group));
            }
            nxt.extend(carry);
            level = nxt;
        }
        level.into_iter().next().unwrap()
    }

    /// The tree the STREAMING coordinator realizes over `n` leaves, reconstructed purely from the
    /// two fixed topology functions: tier 0 = `level0_group_sizes(n, k)` (contiguous leaf→R1
    /// grouping, leaf i at slot `i-offset` of its group), tier ≥ 1 = `build_fold_topology(m, k)`
    /// where `Child::Input(g)` = R1 node g. Mirrors exactly how the coordinator slots inputs.
    fn streaming_leaf_shape(n: usize) -> LeafShape {
        if n == 1 {
            return LeafShape::Leaf(0);
        }
        let sizes = level0_group_sizes(n, K);
        // R1 node g's children are the contiguous leaf range [off, off+sz).
        let mut off = 0usize;
        let r1_shapes: Vec<LeafShape> = sizes
            .iter()
            .map(|&sz| {
                let children = (off..off + sz).map(LeafShape::Leaf).collect();
                off += sz;
                LeafShape::R1(children)
            })
            .collect();
        assert_eq!(off, n);
        let m = r1_shapes.len();
        let (tasks, root) = build_fold_topology(m, K);
        // Resolve a tier-≥1 child: `Child::Input(g)` is R1 node g; `Child::Fold(j)` is fold task j.
        fn resolve(c: Child, tasks: &[super::FoldTask], r1: &[LeafShape]) -> LeafShape {
            match c {
                Child::Input(g) => r1[g].clone(),
                Child::Fold(j) => LeafShape::R2(
                    tasks[j]
                        .children
                        .iter()
                        .map(|&ch| resolve(ch, tasks, r1))
                        .collect(),
                ),
            }
        }
        resolve(root, &tasks, &r1_shapes)
    }

    /// The streaming two-tier DAG folds the IDENTICAL tree `recursive_aggregate_prove_leaves`
    /// realizes — same tier-0 leaf→R1 grouping, same up-tree R2 nesting, same leaf-index→slot
    /// assignment at every node. Since `prove_leaf_or_short`/`run_fold_task` are pure functions of
    /// their ordered children, identical shape ⇒ identical proof bytes. Swept over the required
    /// n ∈ {1, 2, k, k+1, ragged r==1, ~2k+3} PLUS a dense 1..=260 sweep (all residues, several
    /// levels, power-of-k boundaries).
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

    /// Tier-0 group assignment IS `level0_group_sizes` slicing: leaves land contiguously,
    /// left-to-right, each R1 node consuming exactly its group size; every leaf index appears once,
    /// in order. Pins n=k+1 (r==1 splits into k-1 and 2) as a worked example.
    #[test]
    fn tier0_group_assignment_matches_level0_sizes() {
        assert_eq!(K, 8, "the k+1 (r==1) pin is written for k=8 (the TopologyConfig default)");
        // n = k+1 = 9 (r==1): level0_group_sizes → [k-1, 2] = [7, 2]. So R1(0) = leaves 0..7,
        // R1(1) = leaves 7..9.
        use LeafShape::{Leaf, R1};
        // n=9 ⇒ m=2 R1 nodes, m <= k ⇒ the R2 root folds them; but the SHAPE at tier 0 is these two
        // R1 nodes: R1(0) = leaves 0..7, R1(1) = leaves 7..9. Reconstruct the tier-0 layer directly
        // and compare.
        assert_eq!(
            streaming_leaf_shape(9),
            LeafShape::R2(vec![
                R1((0..7).map(Leaf).collect()),
                R1((7..9).map(Leaf).collect()),
            ]),
            "n=9 (r==1) tier-0 grouping wrong"
        );

        // General: every leaf index 0..n appears exactly once, contiguous per group, per
        // level0_group_sizes, across all required + a dense sweep.
        for n in 2..=260usize {
            let sizes = level0_group_sizes(n, K);
            let shape = streaming_leaf_shape(n);
            let mut collected: Vec<usize> = Vec::new();
            collect_r1_leaf_indices(&shape, &mut collected);
            let expected: Vec<usize> = (0..n).collect();
            assert_eq!(collected, expected, "n={n}: leaves not consumed contiguously in order");
            // Group sizes read back off the R1 nodes match level0_group_sizes exactly.
            let mut r1_sizes: Vec<usize> = Vec::new();
            collect_r1_sizes(&shape, &mut r1_sizes);
            assert_eq!(r1_sizes, sizes, "n={n}: R1 group sizes != level0_group_sizes");
        }
    }

    /// Depth-first collect of leaf indices under every R1 node (left-to-right) — the order the
    /// tier-0 layer consumes leaves.
    fn collect_r1_leaf_indices(s: &LeafShape, out: &mut Vec<usize>) {
        match s {
            LeafShape::Leaf(i) => out.push(*i),
            LeafShape::R1(c) | LeafShape::R2(c) => {
                for ch in c {
                    collect_r1_leaf_indices(ch, out);
                }
            }
        }
    }

    /// Depth-first collect of each R1 node's arity (left-to-right) — the tier-0 group sizes.
    fn collect_r1_sizes(s: &LeafShape, out: &mut Vec<usize>) {
        match s {
            LeafShape::Leaf(_) => {}
            LeafShape::R1(c) => out.push(c.len()),
            LeafShape::R2(c) => {
                for ch in c {
                    collect_r1_sizes(ch, out);
                }
            }
        }
    }
}
