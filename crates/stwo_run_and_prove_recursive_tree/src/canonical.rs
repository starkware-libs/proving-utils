//! One-time setup of the single circuit shape that verifies every layer of the recursive tree.
//!
//! Because the leaf cairo-verifier circuit and the multiverifier circuit are both padded to the
//! same [`TARGET_PADDING_SIZES`], they share the same preprocessed-trace
//! layout and `trace_log_size`. As a result a *single* multiverifier circuit shape can verify both
//! leaf proofs (layer 1) and multiverifier proofs (every layer above), with one [`SharedConfig`]
//! and one preprocessed root. This is what makes the reduction homogeneous and lets an unpaired
//! entry be carried up to a higher layer unchanged.
//!
//! This module replicates the logic of `circuit_multiverifier::test_utils`'s
//! `get_preprocessed_multiverifier_from_circuit`, which is test-only upstream.

use circuit_cairo_verifier::privacy::{get_pcs_config, privacy_cairo_verifier_config};
use circuit_cairo_verifier::verify::build_cairo_verifier_circuit;
use circuit_common::finalize::{ComponentSizes, pad_to_targets};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_prover::prover::{BaseColumnPool, SimdBackend};
use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuits::blake::HashValue;
use circuits::context::FinalizedContext;
use circuits::ivalue::NoValue;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use stwo::core::pcs::PcsConfig;
use tracing::{Level, info, span};

use crate::RecursiveTreeError;

// ---------------------------------------------------------------------------------------------
// Circuit configuration.
//
// TEMPORARY: the whole tree is configured to match the pre-generated *privacy* cairo-verifier
// proof used as the leaf fixture (see `circuit_multiverifier::verify_test`), so the recursive-tree
// binary can be tested end-to-end without running `leaf_prover`. When `leaf_prover` is integrated
// this will move back to the leaf-prover-derived (canonical) config.
// ---------------------------------------------------------------------------------------------

/// Log blowup factor of the outer circuit proof (matches `circuit_multiverifier::verify_test`).
pub const CIRCUIT_LOG_BLOWUP_FACTOR: u32 = 3;

/// Cairo-verifier (leaf) circuit trace log size in the privacy setup — drives the outer proof's
/// PCS config (matches
/// `circuit_multiverifier::verify_test::PRIVACY_CAIRO_VERIFIER_TRACE_LOG_SIZE`).
pub const CIRCUIT_TRACE_LOG_SIZE: u32 = 21;

/// PCS config for proving each layer (matches `circuit_multiverifier::verify_test::PCS_CONFIG`).
pub const CIRCUIT_PCS_CONFIG: PcsConfig =
    get_pcs_config(CIRCUIT_TRACE_LOG_SIZE, CIRCUIT_LOG_BLOWUP_FACTOR);

/// Common per-component padding target applied to BOTH the leaf cairo-verifier circuit and the
/// multiverifier circuit, so they share one preprocessed-trace layout and a single proof shape
/// verifies every layer. Matches `circuit_multiverifier::verify_test::TARGET_PADDING_SIZES`.
pub const TARGET_PADDING_SIZES: ComponentSizes = ComponentSizes {
    eq: 1 << 17,
    qm31_ops: 1 << 21,
    m31_to_u32: 1 << 18,
    triple_xor: 1 << 17,
    blake_g_gate: 1 << 20,
};

/// Everything that is identical for every node of the tree. Built once at startup and threaded by
/// reference into every `reduce_pair` call.
pub struct CanonicalCircuit {
    /// The preprocessed multiverifier circuit — the shape every layer's proof is generated
    /// against.
    pub preprocessed_multiverifier: PreprocessedCircuit,
    /// Config shared by all proofs being verified by the multiverifier. Its `proof_config` is also
    /// used to deserialize leaf / intermediate proofs from disk.
    pub shared_config: SharedConfig,
    /// Reused across all `prove_circuit_assignment` calls.
    pub base_column_pool: BaseColumnPool<SimdBackend>,
}

impl CanonicalCircuit {
    /// Builds the canonical circuit shape and all the configuration derived from it.
    pub fn build() -> Result<Self, RecursiveTreeError> {
        let _span = span!(Level::INFO, "CanonicalCircuit::build").entered();

        // 1. The leaf cairo-verifier circuit (padded + preprocessed). Its preprocessed trace gives
        //    the column count / log sizes that describe a *child* circuit proof.
        let preprocessed_leaf = build_preprocessed_leaf_circuit();

        // 2. The proof config + shared config for verifying a child circuit proof.
        let proof_config = ProofConfig::new(
            &all_circuit_components::<NoValue>(),
            preprocessed_leaf.preprocessed_trace.n_columns(),
            &CIRCUIT_PCS_CONFIG,
            INTERACTION_POW_BITS,
        );
        let shared_config = SharedConfig {
            pcs_config: CIRCUIT_PCS_CONFIG,
            proof_config: proof_config.clone(),
            preprocessed_column_log_sizes: preprocessed_leaf.preprocessed_trace.log_sizes(),
        };

        // 3. The multiverifier circuit shape, built from two empty (structure-only) inputs and
        //    padded to the same target as the leaf circuit.
        let empty_input = || MultiverifierInput {
            proof: empty_proof(&proof_config),
            preprocessed_root: HashValue::from([0u32; circuits::blake::BLAKE2S_DIGEST_N_WORDS]),
            output_values: [0; circuit_common::N_RESERVED],
        };
        let mut multiverifier_context =
            build_multiverifier_circuit::<NoValue>(empty_input(), empty_input(), &shared_config);
        pad_to_targets(&mut multiverifier_context, TARGET_PADDING_SIZES);
        let preprocessed_multiverifier =
            PreprocessedCircuit::preprocess_circuit(&mut multiverifier_context);

        // 4. Homogeneity check: the leaf and multiverifier circuits must share the SAME
        //    preprocessed trace layout (column ids + per-column log sizes + overall trace_log_size)
        //    so that one `proof_config` / `preprocessed_column_log_sizes` verifies BOTH a leaf
        //    child proof and a multiverifier child proof.
        if preprocessed_leaf.preprocessed_trace.log_sizes()
            != preprocessed_multiverifier.preprocessed_trace.log_sizes()
            || preprocessed_leaf.trace_log_size != preprocessed_multiverifier.trace_log_size
        {
            return Err(RecursiveTreeError::PaddingParity);
        }

        info!(
            trace_log_size = preprocessed_multiverifier.trace_log_size,
            "Canonical multiverifier circuit ready."
        );
        Ok(Self {
            preprocessed_multiverifier,
            shared_config,
            base_column_pool: BaseColumnPool::new(),
        })
    }
}

/// The privacy cairo-verifier (leaf) circuit padded to [`TARGET_PADDING_SIZES`] and preprocessed.
/// This is the child-circuit shape the multiverifier verifies; its preprocessed trace gives the
/// column count / log sizes that describe a child circuit proof.
fn build_preprocessed_leaf_circuit() -> PreprocessedCircuit {
    let mut leaf_context = build_unpadded_leaf_context();
    pad_to_targets(&mut leaf_context, TARGET_PADDING_SIZES);
    PreprocessedCircuit::preprocess_circuit(&mut leaf_context)
}

/// The unpadded privacy cairo-verifier (leaf) circuit context.
pub fn build_unpadded_leaf_context() -> FinalizedContext<NoValue> {
    build_cairo_verifier_circuit(&privacy_cairo_verifier_config(CIRCUIT_LOG_BLOWUP_FACTOR))
}

/// Builds the multiverifier circuit topology (structure-only) from a leaf circuit padded only with
/// the *default* next-power-of-two padding (NOT [`TARGET_PADDING_SIZES`]), and applies no target
/// padding to the multiverifier itself. Exposed for the regression test that derives and locks
/// [`TARGET_PADDING_SIZES`] — mirroring `circuit_multiverifier::verify_test`'s `None`-padding path,
/// which must not depend on the very constant being derived.
#[cfg(test)]
pub fn build_unpadded_multiverifier_context() -> FinalizedContext<NoValue> {
    let mut leaf_context = build_unpadded_leaf_context();
    let preprocessed_leaf = PreprocessedCircuit::preprocess_circuit(&mut leaf_context);
    let proof_config = ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        preprocessed_leaf.preprocessed_trace.n_columns(),
        &CIRCUIT_PCS_CONFIG,
        INTERACTION_POW_BITS,
    );
    let shared_config = SharedConfig {
        pcs_config: CIRCUIT_PCS_CONFIG,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: preprocessed_leaf.preprocessed_trace.log_sizes(),
    };
    let empty_input = || MultiverifierInput {
        proof: empty_proof(&proof_config),
        preprocessed_root: HashValue::from([0u32; circuits::blake::BLAKE2S_DIGEST_N_WORDS]),
        output_values: [0; circuit_common::N_RESERVED],
    };
    build_multiverifier_circuit::<NoValue>(empty_input(), empty_input(), &shared_config)
}
