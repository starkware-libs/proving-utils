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
    /// Builds the layer-0 entry for a leaf from its `leaf_prover` output: its proof, outputs, and
    /// preprocessed root all travel inline in the [`LeafInput`].
    pub fn from_leaf(leaf: &LeafInput) -> Result<Self, RecursiveTreeError> {
        Ok(Self {
            proof_bytes: leaf.proof.clone(),
            preprocessed_root: leaf.preprocessed_root(),
            packed_output: PackedNode::leaf(
                leaf.parse_output_values()?,
                leaf.program_output.clone(),
            ),
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
    let output_values: [QM31; N_RESERVED] =
        outputs
            .try_into()
            .map_err(|v: Vec<QM31>| RecursiveTreeError::BadOutputArity {
                expected: N_RESERVED,
                got: v.len(),
            })?;

    let (proof, _public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
    let mut proof_bytes = Vec::new();
    proof.serialize(&mut proof_bytes);

    Ok(LayerEntry {
        proof_bytes,
        preprocessed_root,
        packed_output: PackedNode::internal(output_values, left.packed_output, right.packed_output),
    })
}

/// Nested packed-output tree mirroring the fold — the circuit-world analogue of the old Cairo
/// `PackedOutput`, kept for a future per-leaf unpacker.
///
/// A leaf is a [`PackedNode::Composite`] holding its circuit output over a single
/// [`PackedNode::Plain`] carrying that leaf's Cairo program output; each fold builds a `Composite`
/// over its two children. So walking `subtasks` to the bottom reaches every leaf's `Plain`, from
/// which the leaf's program output is read directly. Unlike Cairo's fieldless `Plain` (whose data
/// is sliced out of the parent's flat `outputs` via `fact_topologies`), ours carries the output
/// inline — the offset/topology unpacking doesn't apply to circuit outputs, so a dedicated
/// circuit-world unpacker just walks this tree.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PackedNode {
    /// A leaf's Cairo program output (each felt a decimal string). Terminal — the analogue of Cairo
    /// `PackedOutput::Plain`, but carrying the output rather than being a bare marker.
    Plain { program_output: Vec<String> },
    /// A verifier / fold node: its `N_RESERVED` circuit output values (each as 4 little-endian
    /// `QM31` limbs) and its child subtasks. The analogue of `CompositePackedOutput`.
    Composite {
        output_values: [[u32; 4]; N_RESERVED],
        subtasks: Vec<PackedNode>,
    },
}

impl PackedNode {
    /// A leaf entry: the leaf circuit's `output_values` over a single `Plain` carrying its program
    /// output.
    pub fn leaf(output_values: [QM31; N_RESERVED], program_output: Vec<String>) -> Self {
        PackedNode::Composite {
            output_values: output_values.map(|v| qm31_to_u32_limbs(&v)),
            subtasks: vec![PackedNode::Plain { program_output }],
        }
    }

    /// An internal fold node: the multiverifier's `output_values` over its two children.
    pub fn internal(
        output_values: [QM31; N_RESERVED],
        left: PackedNode,
        right: PackedNode,
    ) -> Self {
        PackedNode::Composite {
            output_values: output_values.map(|v| qm31_to_u32_limbs(&v)),
            subtasks: vec![left, right],
        }
    }

    /// This `Composite` node's circuit output values as raw `QM31` limbs. Panics on a `Plain` node
    /// — every fold node (`LayerEntry::packed_output`) is a `Composite`; `Plain` only ever
    /// appears as a leaf's subtask.
    pub fn output_values(&self) -> &[[u32; 4]; N_RESERVED] {
        match self {
            PackedNode::Composite { output_values, .. } => output_values,
            PackedNode::Plain { .. } => {
                unreachable!(
                    "output_values called on a Plain node; fold nodes are always Composite"
                )
            }
        }
    }

    /// This `Composite` node's output values as `QM31`s (inverse of the limb encoding). Panics on a
    /// `Plain` node, as [`Self::output_values`].
    pub fn output_values_qm31(&self) -> [QM31; N_RESERVED] {
        self.output_values()
            .map(|[a, b, c, d]| qm31_from_u32s(a, b, c, d))
    }
}

/// Decomposes a `QM31` into its four little-endian `M31` limbs as raw `u32`s — the encoding used
/// for output values both in `PackedNode` and in a leaf's inline [`crate::leaf_io::LeafInput`]
/// outputs.
pub fn qm31_to_u32_limbs(value: &QM31) -> [u32; 4] {
    value.to_m31_array().map(|m| m.0)
}
