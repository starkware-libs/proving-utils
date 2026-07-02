//! The per-node tree state and the core pair reduction (the circuit-world replacement for the old
//! Cairo simple-bootloader pair run).

use circuit_common::N_RESERVED;
use circuit_common::finalize::pad_to_targets;
use circuit_multiverifier::verify::{MultiverifierInput, build_multiverifier_circuit};
use circuit_prover::prover::{
    prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
};
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuit_serialize::serialize::CircuitSerialize;
use circuits::blake::HashValue;
use circuits::ivalue::qm31_from_u32s;
use circuits_stark_verifier::proof::ProofConfig;
use serde::{Deserialize, Serialize};
use stwo::core::fields::qm31::QM31;
use stwo::core::verifier::PREPROCESSED_TRACE_IDX;
use tracing::{Level, span};

use crate::RecursiveTreeError;
use crate::canonical::{CanonicalCircuit, TARGET_PADDING_SIZES};
use crate::leaf_io::LeafInput;

/// In-memory representation of a single tree node during reduction. At layer 0 these wrap the leaf
/// proofs; at higher layers each entry is the result of folding two children.
pub struct LayerEntry {
    /// This node's serialized `Proof<QM31>`, held in memory (a leaf proof read from disk at layer
    /// 0, or a freshly reserialized multiverifier proof at internal/carried nodes). Kept in memory
    /// rather than round-tripped through a scratch file — one proof per live entry, freed as the
    /// layer is consumed.
    pub proof_bytes: Vec<u8>,
    /// Preprocessed root of this node's proof: for a layer-0 leaf it's whatever root the manifest
    /// declared; for an internal/carried node it's the multiverifier root read from the freshly
    /// proved proof.
    pub preprocessed_root: HashValue<QM31>,
    /// Nested packed-output subtree rooted at this node. Also holds this node's output values (as
    /// QM31 limbs); recover them via [`PackedNode::output_values_qm31`] when building the next
    /// layer.
    pub packed_output: PackedNode,
}

impl LayerEntry {
    /// Builds the layer-0 entry for a leaf: reads its serialized proof from disk into memory and
    /// takes its outputs and preprocessed root from the leaf manifest.
    pub fn from_leaf(leaf: &LeafInput) -> Result<Self, RecursiveTreeError> {
        let proof_bytes = std::fs::read(&leaf.proof_path)
            .map_err(|e| RecursiveTreeError::PathIO(e, leaf.proof_path.clone()))?;
        Ok(Self {
            proof_bytes,
            preprocessed_root: HashValue::from(leaf.preprocessed_root),
            packed_output: PackedNode::leaf(leaf.parse_output_values()?),
        })
    }

    /// Materializes this node as a [`MultiverifierInput`] by deserializing its in-memory proof.
    pub fn to_multiverifier_input(
        &self,
        proof_config: &ProofConfig,
    ) -> Result<MultiverifierInput<QM31>, RecursiveTreeError> {
        let proof = deserialize_proof_with_config(&mut self.proof_bytes.as_slice(), proof_config)
            .map_err(|e| RecursiveTreeError::Deserialize(format!("{e:?}")))?;
        Ok(MultiverifierInput {
            proof,
            preprocessed_root: self.preprocessed_root.clone(),
            output_values: self.packed_output.output_values_qm31(),
        })
    }
}

/// Folds two children into a new parent entry: builds a multiverifier circuit that verifies both
/// children, proves it against the canonical preprocessed circuit, and reserializes the resulting
/// proof into the parent entry for the next layer.
pub fn reduce_pair(
    left: LayerEntry,
    right: LayerEntry,
    layer_idx: usize,
    pair_idx: usize,
    canonical: &CanonicalCircuit,
) -> Result<LayerEntry, RecursiveTreeError> {
    let _span = span!(Level::INFO, "reduce_pair", layer_idx, pair_idx).entered();

    let input0 = left.to_multiverifier_input(&canonical.shared_config.proof_config)?;
    let input1 = right.to_multiverifier_input(&canonical.shared_config.proof_config)?;

    let mut context = build_multiverifier_circuit::<QM31>(input0, input1, &canonical.shared_config);
    pad_to_targets(&mut context, TARGET_PADDING_SIZES);
    debug_assert!(
        context.is_circuit_valid(),
        "multiverifier circuit rejected its inputs at layer {layer_idx} pair {pair_idx}"
    );

    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &canonical.preprocessed_multiverifier,
        &canonical.base_column_pool,
        canonical.shared_config.pcs_config,
    )
    .map_err(|e| RecursiveTreeError::Proving(format!("{e:?}")))?;

    // Extract everything the next layer needs BEFORE consuming the proof:
    // `prepare_circuit_proof_for_circuit_verifier` takes the `CircuitProof` by value.
    let root_hash = circuit_proof.stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX];
    let preprocessed_root: HashValue<QM31> = root_hash.into();
    let outputs = circuit_proof.claim.output_values.clone();
    let output_values: [QM31; N_RESERVED] = outputs
        .try_into()
        .map_err(|v: Vec<QM31>| RecursiveTreeError::BadOutputArity(v.len()))?;

    let (proof, _public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
    let mut proof_bytes = Vec::new();
    proof.serialize(&mut proof_bytes);

    Ok(LayerEntry {
        proof_bytes,
        preprocessed_root,
        packed_output: PackedNode::internal(output_values, left.packed_output, right.packed_output),
    })
}

/// Nested packed-output tree mirroring the fold. Each node records its two output values and, for
/// an internal node, its two child subtasks. This is the circuit-world analogue of the old Cairo
/// `PackedOutput`/`CompositePackedOutput`, kept for a future per-leaf unpacker.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PackedNode {
    /// This node's two output values, each as 4 little-endian `QM31` limbs.
    pub output_values: [[u32; 4]; N_RESERVED],
    /// Empty for leaves; the two child subtrees for internal nodes. `default` so a leaf node
    /// (which omits the field on serialization) round-trips back on deserialization.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub subtasks: Vec<PackedNode>,
}

impl PackedNode {
    pub fn leaf(output_values: [QM31; N_RESERVED]) -> Self {
        Self {
            output_values: output_values.map(|v| qm31_to_u32_limbs(&v)),
            subtasks: Vec::new(),
        }
    }

    pub fn internal(
        output_values: [QM31; N_RESERVED],
        left: PackedNode,
        right: PackedNode,
    ) -> Self {
        Self {
            output_values: output_values.map(|v| qm31_to_u32_limbs(&v)),
            subtasks: vec![left, right],
        }
    }

    /// This node's output values as `QM31`s (inverse of the limb encoding stored in
    /// [`Self::output_values`]).
    pub fn output_values_qm31(&self) -> [QM31; N_RESERVED] {
        self.output_values
            .map(|[a, b, c, d]| qm31_from_u32s(a, b, c, d))
    }
}

/// Decomposes a `QM31` into its four little-endian `M31` limbs as raw `u32`s — the encoding used
/// for output values both in `PackedNode` and in a leaf's inline [`crate::leaf_io::LeafInput`]
/// outputs.
pub fn qm31_to_u32_limbs(value: &QM31) -> [u32; 4] {
    value.to_m31_array().map(|m| m.0)
}
