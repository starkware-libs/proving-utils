//! Witness-independent proving precomputes: the whole-recursion [`RecursionPrecompute`] (a flat set
//! of committed trees sharing one twiddle tree + column pool), the per-shape [`PreprocessedTree`],
//! and the node-shape derivation ([`node_preprocessed_from_shared`], [`fold_used_arities`]) the
//! prover uses to build each held tree. The whole-recursion builder
//! ([`build_recursion_precompute`]) takes the caller's already-built leaf [`FinalizedContext`] and
//! assembles every held tree.

use std::collections::{BTreeMap, BTreeSet};

use crate::AggregateConfig;
use crate::leaf::leaf_preprocessed;

use circuit_common::N_RESERVED;
use circuit_common::finalize::{ComponentSizes, pad_to_targets};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuits::blake::HashValue;
use circuits::context::FinalizedContext;
use circuits::ivalue::NoValue;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use num_traits::Zero;
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

/// Builds + preprocesses the NoValue multiverifier node circuit of `arity` children for a given
/// `shared` config, padded to `target_padding`. Keyed on the already-built `SharedConfig`. The node
/// shape the prover commits per held tree, and the shape the caller's capture/drift path rebuilds.
pub(crate) fn node_preprocessed_from_shared(
    shared: &SharedConfig,
    target_padding: ComponentSizes,
    arity: usize,
) -> PreprocessedCircuit {
    // Same node circuit as `prove_fold_node`/`prove_short_fold_node`, with NoValue witnesses (the
    // preprocessed trace is witness-independent).
    let proof_config = noval_node_proof_config(
        shared.proof_config.n_preprocessed_columns,
        &shared.pcs_config,
    );
    let node_shared = SharedConfig {
        pcs_config: shared.pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: shared.preprocessed_column_log_sizes.clone(),
    };
    let inputs: Vec<MultiverifierInput<NoValue>> = (0..arity)
        .map(|_| empty_node_input(&proof_config))
        .collect();
    let mut ctx = build_multiverifier_circuit::<NoValue>(inputs, &node_shared);
    pad_to_targets(&mut ctx, target_padding);
    PreprocessedCircuit::preprocess_circuit(&mut ctx)
}

/// The distinct node arities a fold over `n_leaves` (fold arity `k`) actually uses: `(level1,
/// fold)`. A curve point touches only a handful of the `2..=k` arities, so the prover commits a
/// preprocessed tree ONLY for these. Reuses the real topology helpers
/// (`crate::level0_group_sizes`, `crate::prove_streaming::fold_node_arities`) so it cannot diverge
/// from the fold. Node sets are empty for `n_leaves <= 1` (the lone leaf is the root).
pub fn fold_used_arities(n_leaves: usize, k: usize) -> (BTreeSet<usize>, BTreeSet<usize>) {
    if n_leaves <= 1 {
        return (BTreeSet::new(), BTreeSet::new());
    }
    let sizes = crate::level0_group_sizes(n_leaves, k);
    let level1: BTreeSet<usize> = sizes.iter().copied().collect();
    let fold = crate::prove_streaming::fold_node_arities(sizes.len(), k);
    (level1, fold)
}

/// Builds the flat leaf/level1/fold [`RecursionPrecompute`] from the caller's already-built leaf
/// `leaf_ctx` (the only AIR-specific ingredient) and `config`. Each layer's preprocessed shape is
/// rebuilt from `config` — no fixed-point loop — and every tree asserts its committed root equals
/// `config`'s root (the load-bearing soundness check: a drifted pinned config fails it loudly).
///
/// `build_all_arities`: production passes `false` → build shapes only for the arities this point's
/// fold uses ([`fold_used_arities`] of `n_leaves`), since committing every unused `2..=k` arity's
/// ~2^22 tree overruns the base-precompute overlap window. Tests pass `true` (they fold a small N
/// differing from the placeholder `n_leaves`, so they need every `2..=k` arity).
pub fn build_recursion_precompute(
    leaf_ctx: FinalizedContext<NoValue>,
    config: &AggregateConfig,
    n_leaves: usize,
    build_all_arities: bool,
) -> RecursionPrecompute {
    let k = config.fold_arity;
    let node_pcs = config.node_pcs_config;
    let node_target = &config.node_target_padding_sizes;

    // Leaf tree: pad + preprocess the caller's leaf circuit to the config's leaf target.
    let leaf_pp = leaf_preprocessed(leaf_ctx, config.leaf_target_padding_sizes.clone());
    let leaf = TreeSpec {
        preprocessed: leaf_pp,
        pcs_config: config.leaf_pcs_config,
        expected_root: config.leaf_preprocessed_root.clone(),
    };

    // Node shapes: level1 verifies leaves (`leaf_shared_config`), fold verifies nodes
    // (`fold_shared_config`); both pad to the common `node_target`, rebuilt (not re-derived).
    let (level1_arities, fold_arities): (Vec<usize>, Vec<usize>) = if build_all_arities {
        ((2..=k).collect(), (2..=k).collect())
    } else {
        let (l, f) = fold_used_arities(n_leaves, k);
        (l.into_iter().collect(), f.into_iter().collect())
    };
    let level1 = level1_arities
        .into_iter()
        .map(|a| {
            (
                a,
                node_spec(
                    &config.leaf_shared_config,
                    node_pcs,
                    node_target,
                    a,
                    config.level1_root(a),
                ),
            )
        })
        .collect();
    let fold = fold_arities
        .into_iter()
        .map(|a| {
            (
                a,
                node_spec(
                    &config.fold_shared_config,
                    node_pcs,
                    node_target,
                    a,
                    config.fold_root(a),
                ),
            )
        })
        .collect();
    RecursionPrecompute::new(leaf, level1, fold)
}

/// One node layer's [`TreeSpec`] for `arity`: the node preprocessed circuit verifying
/// `child_shared`-configured children (padded to `node_target`), committed at `node_pcs`, asserting
/// `expected_root`. Shared by the level1 (leaf child) and fold (node child) tiers. Generic — all
/// inputs come from the [`AggregateConfig`].
fn node_spec(
    child_shared: &SharedConfig,
    node_pcs: PcsConfig,
    node_target: &ComponentSizes,
    arity: usize,
    expected_root: HashValue<QM31>,
) -> TreeSpec {
    TreeSpec {
        preprocessed: node_preprocessed_from_shared(child_shared, node_target.clone(), arity),
        pcs_config: node_pcs,
        expected_root,
    }
}

impl RecursionPrecompute {
    /// Builds the flat precompute: one shared `base_column_pool` + one shared `twiddles` sized to
    /// the largest prove domain across all shapes, then a committed [`PreprocessedTree`] for
    /// the `leaf` and for each arity's `level1` / `fold` shape. Every tree asserts its root
    /// against the supplied pinned root (the caller — `gate-air-leaf` — supplies the pinned
    /// consts).
    pub(crate) fn new(
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

/// The `NoValue` node `ProofConfig` a multiverifier NODE circuit is built/proved with. Shared by
/// the NoValue node builders (here + `test_utils`) so they derive the config identically.
pub(crate) fn noval_node_proof_config(
    n_preprocessed_columns: usize,
    pcs_config: &PcsConfig,
) -> ProofConfig {
    ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        n_preprocessed_columns,
        pcs_config,
        INTERACTION_POW_BITS,
    )
}

/// A placeholder `NoValue` child input for building the witness-independent node shape.
pub(crate) fn empty_node_input(proof_config: &ProofConfig) -> MultiverifierInput<NoValue> {
    MultiverifierInput {
        proof: empty_proof(proof_config),
        preprocessed_root: HashValue::from([0u32; N_RESERVED]),
        output_values: [QM31::zero(); N_RESERVED],
    }
}
