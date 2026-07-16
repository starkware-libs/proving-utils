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

use std::path::PathBuf;

use circuit_cairo_verifier::all_components::all_components;
use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_cairo_verifier::utils::load_program;
use circuit_cairo_verifier::verify::{
    CairoVerifierConfig, build_cairo_verifier_circuit, get_preprocessed_root,
};
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
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use indexmap::IndexMap;
use leaf_prover::consts::DISABLED_COMPONENTS_SMALL_PREPROCESSED;
use stwo::core::pcs::PcsConfig;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTraceVariant;
use tracing::{Level, info, span};

use crate::RecursiveTreeError;

// ---------------------------------------------------------------------------------------------
// Circuit configuration.
//
// The tree is configured to the shape `leaf_prover` produces when proving the
// `leaf_simple_bootloader` with the canonical-small setup: `CanonicalSmall` preprocessed trace for
// the inner Cairo proof, and a blowup-1 (memory-feasible), 96-bit-secure circuit PCS config.
// ---------------------------------------------------------------------------------------------

/// Log blowup factor of the outer circuit proof.
pub const CANONICAL_CIRCUIT_LOG_BLOWUP_FACTOR: u32 = 1;

/// Cairo-verifier (leaf) circuit trace log size — the log size the leaf-bootloader verifier
/// circuit reaches (its dominant components, `qm31_ops`/`blake_g_gate`, hit 2^23; see
/// [`TARGET_PADDING_SIZES`]).
pub const CANONICAL_CIRCUIT_TRACE_LOG_SIZE: u32 = 23;

/// PCS config for proving each layer. MUST equal the config the leaf circuit proofs were produced
/// with: this constant is the single source of truth for the tree's circuit PCS shape, and the
/// backend must pass it (via the leaf prover's `circuit_prover_params_json`) when producing
/// leaves.
// TODO(yairv): Consider taking this from the backend via configuration (alongside the leaf
// bootloader program), so the backend passes one config to both `leaf_prover` and the recursive
// tree.
pub const CANONICAL_CIRCUIT_PCS_CONFIG: PcsConfig = get_pcs_config(
    CANONICAL_CIRCUIT_TRACE_LOG_SIZE,
    CANONICAL_CIRCUIT_LOG_BLOWUP_FACTOR,
);

/// Common per-component padding target applied to BOTH the leaf cairo-verifier circuit and the
/// multiverifier circuit, so they share one preprocessed-trace layout and a single proof shape
/// verifies every layer. Derived (and locked by `target_padding_sizes_are_consistent`) as the
/// per-component max of the two circuits — currently the leaf-bootloader verifier circuit
/// dominates every component, so `leaf_prover`'s default next-power-of-two padding already
/// produces exactly this shape.
pub const TARGET_PADDING_SIZES: ComponentSizes = ComponentSizes {
    eq: 1 << 20,
    qm31_ops: 1 << 23,
    m31_to_u32: 1 << 20,
    triple_xor: 1 << 19,
    blake_g_gate: 1 << 23,
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
            &CANONICAL_CIRCUIT_PCS_CONFIG,
            INTERACTION_POW_BITS,
        );
        let shared_config = SharedConfig {
            pcs_config: CANONICAL_CIRCUIT_PCS_CONFIG,
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

/// The unpadded cairo-verifier (leaf) circuit context, shaped exactly as `leaf_prover` shapes it
/// when proving the leaf simple bootloader (see `leaf_prover::prove_leaf`): `CanonicalSmall`
/// preprocessed trace, all components except [`DISABLED_COMPONENTS_SMALL_PREPROCESSED`], the
/// bootloader program's felts, and its two public outputs (the hashed-output Uint256 low/high).
pub fn build_unpadded_leaf_context() -> FinalizedContext<NoValue> {
    build_cairo_verifier_circuit(&leaf_cairo_verifier_config())
}

/// Path of the compiled leaf simple bootloader — the program every leaf proof attests to.
/// TEMPORARY: read from this crate's `test_data`; production will receive it via configuration.
fn leaf_bootloader_program_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_data/leaf_simple_bootloader_compiled.json")
}

/// The slice of the leaf's Cairo prover parameters the canonical circuit shape depends on.
#[derive(serde::Deserialize)]
struct LeafCairoProverParams {
    /// PCS config of the *inner* Cairo proof the leaf circuit verifies.
    pcs_config: PcsConfig,
    preprocessed_trace: PreProcessedTraceVariant,
}

/// The Cairo prover parameters the leaf's inner proof is produced with — loaded from the same
/// file the golden e2e proves leaves with, so the canonical circuit shape cannot drift from it.
/// TEMPORARY: read from `leaf_prover`'s test data; production will receive it via configuration
/// (see the TODO on [`CANONICAL_CIRCUIT_PCS_CONFIG`]).
fn leaf_cairo_prover_params() -> LeafCairoProverParams {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../leaf_prover/tests/data/cairo_prover_params_canonical_small.json");
    serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap()
}

/// Mirrors `circuit_cairo_verifier::privacy::privacy_cairo_verifier_config`, for the leaf simple
/// bootloader under the canonical-small test setup instead of the privacy transaction.
// TODO(yairv): Share a parameterized config builder with `privacy_cairo_verifier_config`
// (upstream, in stwo-circuits) instead of mirroring its structure here.
fn leaf_cairo_verifier_config() -> CairoVerifierConfig {
    let leaf_cairo_params = leaf_cairo_prover_params();
    let preprocessed_trace_variant = leaf_cairo_params.preprocessed_trace;
    // Build `enabled_bits` (one flag per component in the full list) and `components` (only the
    // enabled entries, as expected by `ProofConfig::new`) in a single pass.
    let (enabled_bits, components): (Vec<bool>, Vec<_>) = all_components::<NoValue>()
        .into_iter()
        .map(|(name, component)| {
            let enabled = !DISABLED_COMPONENTS_SMALL_PREPROCESSED.contains(&name);
            (enabled, enabled.then_some((name, component)))
        })
        .unzip();
    let components: IndexMap<&'static str, Box<dyn CircuitEval<NoValue>>> =
        components.into_iter().flatten().collect();

    let proof_config = ProofConfig::new(
        &components,
        preprocessed_trace_variant.n_columns(),
        &leaf_cairo_params.pcs_config,
        cairo_air::verifier::INTERACTION_POW_BITS,
    );

    CairoVerifierConfig {
        // The inner Cairo proof's lifting log size: the trace's FRI evaluation domain (`max(min
        // lifting, max column log size)` — already folded into `proof_config.fri`).
        preprocessed_root: get_preprocessed_root(
            proof_config.fri.log_evaluation_domain_size() as u32
        ),
        proof_config,
        enabled_bits,
        program: load_program(&leaf_bootloader_program_path()),
        // The leaf simple bootloader outputs only the blake2s hash of `[task program hash,
        // task output...]`, as a Uint256 (low, high).
        n_outputs: 2,
        preprocessed_trace_variant,
    }
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
        &CANONICAL_CIRCUIT_PCS_CONFIG,
        INTERACTION_POW_BITS,
    );
    let shared_config = SharedConfig {
        pcs_config: CANONICAL_CIRCUIT_PCS_CONFIG,
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
