//! Witness-independent proving precomputes: the whole-recursion [`RecursionPrecompute`] and the
//! per-shape [`CircuitPrecompute`].

use std::sync::Arc;

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

/// Witness-independent proving precompute for the whole recursion, built up front from public params
/// (decoupled from [`crate::AggregateConfig`] so heavy builds happen off the critical path). A `None`
/// field means that tier is inactive, falling back to the self-contained `prove_circuit_assignment`.
pub struct RecursionPrecompute {
    /// Precompute for the fold (node-verifying) node circuit; reused for every `crate::prove_fold_node`.
    pub fold_precompute: Option<Arc<CircuitPrecompute>>,
    /// Precompute for the level1 (leaf-verifying) node circuit; reused for every full-`k`
    /// `crate::prove_leaf_or_short`.
    pub level1_precompute: Option<Arc<CircuitPrecompute>>,
    /// Precompute for the leaf circuit, reused for every leaf-prover call.
    pub leaf_precompute: Option<Arc<CircuitPrecompute>>,
}

/// Witness-independent precompute for one fixed circuit shape: its preprocessed circuit, twiddles, and
/// committed tree0, plus a shared column pool. These depend only on the gate structure, not the
/// witness, so for the recursion's repeated shapes they are computed once and reused across all proves
/// (shared read-only across [`crate::pools::PoolSet`] workers via `Arc`).
pub struct CircuitPrecompute {
    /// The fixed preprocessed circuit for this shape.
    pub preprocessed: PreprocessedCircuit,
    /// Twiddles sized for this shape's largest prove domain (`trace_log_size + max(log_blowup, 1)`).
    pub twiddles: TwiddleTree<SimdBackend>,
    /// The committed tree0 commitment tree for this shape.
    pub tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>,
    /// Shared memory pool for the prover's SIMD columns.
    pub base_column_pool: BaseColumnPool<SimdBackend>,
    /// PCS config for this shape, `lifting_log_size` pinned to the cached tree's domain.
    pub pcs_config: PcsConfig,
}

impl CircuitPrecompute {
    /// Builds the precompute for a fixed `preprocessed` shape at `log_blowup_factor`, mirroring what
    /// `prove_circuit_assignment` builds internally. SOUNDNESS GUARD: asserts once, at build time, that
    /// the committed tree's root equals the trusted `expected_root` — since every prove reuses this
    /// tree, that one check transfers the trust to all of them (a shape mismatch aborts before proving).
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
