//! Witness-independent proving precomputes: the whole-recursion [`RecursionPrecompute`] (a flat set
//! of committed trees sharing one twiddle tree + column pool) and the per-shape
//! [`PreprocessedTree`].

use std::collections::BTreeMap;

use circuit_common::preprocessed::PreprocessedCircuit;
use circuits::blake::HashValue;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::poly::twiddles::TwiddleTree;

/// One fixed circuit shape's committed preprocessed tree: the preprocessed circuit, its committed
/// tree0, and the PCS config (its `lifting_log_size` pinned to the tree's domain). Every prove of
/// this shape reuses the tree instead of rebuilding it.
pub struct PreprocessedTree {
    /// The fixed preprocessed circuit for this shape.
    pub preprocessed: PreprocessedCircuit,
    /// The committed tree0 commitment tree for this shape.
    pub tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>,
    /// PCS config for this shape, `lifting_log_size` pinned to the cached tree's domain.
    pub pcs_config: PcsConfig,
}

/// One (preprocessed, pcs_config, expected_root) shape the caller hands in to build a
/// [`PreprocessedTree`].
pub struct TreeSpec {
    pub preprocessed: PreprocessedCircuit,
    pub pcs_config: PcsConfig,
    pub expected_root: HashValue<QM31>,
}

/// Witness-independent proving precompute for the whole recursion, built up front from public
/// params. Mirrors `privacy_prove::RecursiveProverPrecomputes`: one shared `base_column_pool` + one
/// shared `twiddles`, and a committed [`PreprocessedTree`] for every shape a prove needs — the
/// `leaf`, the per-arity `level1` (leaf-verifying) nodes, and the per-arity `fold` (node-verifying)
/// nodes. Every tree asserts, at build time, that its committed root equals the pinned root the
/// caller supplied.
pub struct RecursionPrecompute {
    /// Shared memory pool for the prover's SIMD columns.
    pub base_column_pool: BaseColumnPool<SimdBackend>,
    /// Twiddles sized for the largest prove domain across all held shapes.
    pub twiddles: TwiddleTree<SimdBackend>,
    /// The leaf circuit's tree, reused for every leaf-prover call.
    pub leaf: PreprocessedTree,
    /// Per-arity level1 (leaf-verifying) node trees, keyed by child count `2..=k`.
    pub level1: BTreeMap<usize, PreprocessedTree>,
    /// Per-arity fold (node-verifying) node trees, keyed by child count `2..=k`.
    pub fold: BTreeMap<usize, PreprocessedTree>,
}

impl PreprocessedTree {
    /// Builds the committed tree for a fixed `preprocessed` shape at `pcs_config`'s blowup,
    /// mirroring what `prove_circuit_assignment` builds internally. Self-contained (builds its
    /// own twiddles + pool) — for the per-run one-shot unpacker tree; the flat
    /// [`RecursionPrecompute`] shares one twiddle tree across all its shapes instead. SOUNDNESS
    /// GUARD: asserts once, at build time, that the committed root equals the trusted
    /// `expected_root` — a shape mismatch aborts before proving.
    pub fn new(
        preprocessed: PreprocessedCircuit,
        pcs_config: PcsConfig,
        expected_root: HashValue<QM31>,
    ) -> Self {
        build_one_shot_tree(preprocessed, pcs_config, expected_root).0
    }
}

/// Builds a per-run ONE-SHOT committed tree (its own `twiddles` + `base_column_pool`, returned so
/// the caller can prove against it via `prove_circuit_with_precompute`), asserting its root against
/// `expected_root`. The same tree-builder the flat precompute uses — for the unpacker tree, which
/// is distinct per run and so is not held in [`RecursionPrecompute`].
pub fn build_one_shot_tree(
    preprocessed: PreprocessedCircuit,
    pcs_config: PcsConfig,
    expected_root: HashValue<QM31>,
) -> (
    PreprocessedTree,
    TwiddleTree<SimdBackend>,
    BaseColumnPool<SimdBackend>,
) {
    let base_column_pool = BaseColumnPool::<SimdBackend>::new();
    let log_blowup_factor = pcs_config.fri_config.log_blowup_factor;
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(preprocessed.trace_log_size + log_blowup_factor.max(1))
            .circle_domain()
            .half_coset,
    );
    let tree = build_tree(
        preprocessed,
        pcs_config,
        expected_root,
        &twiddles,
        &base_column_pool,
    );
    (tree, twiddles, base_column_pool)
}

impl RecursionPrecompute {
    /// Builds the flat precompute: one shared `base_column_pool` + one shared `twiddles` sized to
    /// the largest prove domain across all shapes, then a committed [`PreprocessedTree`] for
    /// the `leaf` and for each arity's `level1` / `fold` shape. Every tree asserts its root
    /// against the supplied pinned root (the caller — `gate-air-leaf` — supplies the pinned
    /// consts).
    pub fn new(
        leaf: TreeSpec,
        level1: BTreeMap<usize, TreeSpec>,
        fold: BTreeMap<usize, TreeSpec>,
    ) -> Self {
        let base_column_pool = BaseColumnPool::<SimdBackend>::new();
        let max_domain = std::iter::once(&leaf)
            .chain(level1.values())
            .chain(fold.values())
            .map(shape_prove_domain)
            .max()
            .expect("at least the leaf shape");
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(max_domain).circle_domain().half_coset,
        );

        let leaf = build_spec(leaf, &twiddles, &base_column_pool);
        let level1 = level1
            .into_iter()
            .map(|(a, s)| (a, build_spec(s, &twiddles, &base_column_pool)))
            .collect();
        let fold = fold
            .into_iter()
            .map(|(a, s)| (a, build_spec(s, &twiddles, &base_column_pool)))
            .collect();

        Self {
            base_column_pool,
            twiddles,
            leaf,
            level1,
            fold,
        }
    }

    /// The held level1 (leaf-verifying) node tree for `arity`. Panics if not built (unsupported
    /// arity).
    pub fn level1_tree(&self, arity: usize) -> &PreprocessedTree {
        self.level1
            .get(&arity)
            .unwrap_or_else(|| panic!("no level1 precompute for arity {arity}"))
    }

    /// The held fold (node-verifying) node tree for `arity`. Panics if not built (unsupported
    /// arity).
    pub fn fold_tree(&self, arity: usize) -> &PreprocessedTree {
        self.fold
            .get(&arity)
            .unwrap_or_else(|| panic!("no fold precompute for arity {arity}"))
    }
}

/// Builds one shape's [`TreeSpec`] into a [`PreprocessedTree`] reusing the shared `twiddles`/pool.
fn build_spec(
    spec: TreeSpec,
    twiddles: &TwiddleTree<SimdBackend>,
    base_column_pool: &BaseColumnPool<SimdBackend>,
) -> PreprocessedTree {
    build_tree(
        spec.preprocessed,
        spec.pcs_config,
        spec.expected_root,
        twiddles,
        base_column_pool,
    )
}

/// The single tree-builder: interpolates + commits `preprocessed`'s tree0 with the shared
/// `twiddles`/`base_column_pool`, pins the PCS `lifting_log_size` to the tree domain, and asserts
/// the committed root equals `expected_root` (the load-bearing soundness check every tree shares).
fn build_tree(
    preprocessed: PreprocessedCircuit,
    pcs_config: PcsConfig,
    expected_root: HashValue<QM31>,
    twiddles: &TwiddleTree<SimdBackend>,
    base_column_pool: &BaseColumnPool<SimdBackend>,
) -> PreprocessedTree {
    let log_blowup_factor = pcs_config.fri_config.log_blowup_factor;
    let lifting_log_size = preprocessed.trace_log_size + log_blowup_factor;
    let pcs_config = PcsConfig {
        lifting_log_size: Some(lifting_log_size),
        ..pcs_config
    };

    let preprocessed_trace = preprocessed.preprocessed_trace.get_trace::<SimdBackend>();
    let preprocessed_trace_polys = SimdBackend::interpolate_columns(preprocessed_trace, twiddles);
    let tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        preprocessed_trace_polys,
        log_blowup_factor,
        twiddles,
        true,
        Some(lifting_log_size),
        base_column_pool,
    );

    let root: HashValue<QM31> = tree.commitment.root().into();
    assert_eq!(
        root, expected_root,
        "precomputed preprocessed (tree0) root must equal the trusted preprocessed_root \
         (column order / log_blowup / shape mismatch)"
    );

    PreprocessedTree {
        preprocessed,
        tree,
        pcs_config,
    }
}

/// The largest prove domain a shape needs: `trace_log_size + max(log_blowup, composition bound =
/// 1)` (matches `prove_circuit_assignment`'s twiddle domain).
fn shape_prove_domain(spec: &TreeSpec) -> u32 {
    spec.preprocessed.trace_log_size + spec.pcs_config.fri_config.log_blowup_factor.max(1)
}
