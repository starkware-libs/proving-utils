//! The per-node tree state and the core pair reduction (the circuit-world replacement for the old
//! Cairo simple-bootloader pair run).

use circuit_cairo_serialize::prepare_circuit_proof_for_cairo_verifier;
use circuit_common::N_RESERVED;
use circuit_common::finalize::pad_to_targets;
use circuit_multiverifier::verify::{MultiverifierInput, build_multiverifier_circuit};
use circuit_prover::prover::{
    prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
    prove_circuit_assignment_with_channel,
};
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuit_serialize::serialize::CircuitSerialize;
use circuit_verifier::circuit_proof::CircuitProof;
use circuit_verifier::statement::{all_circuit_components, circuit_component_log_sizes};
use circuits::blake::HashValue;
use circuits::ivalue::{NoValue, qm31_from_u32s};
use circuits_stark_verifier::proof::ProofConfig;
use serde::{Deserialize, Serialize};
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs::blake2_hash::Blake2sHash;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::core::verifier::PREPROCESSED_TRACE_IDX;
use tracing::{Level, span};

use crate::RecursiveTreeError;
use crate::canonical::{CanonicalCircuit, TARGET_PADDING_SIZES};
use crate::leaf_io::{LeafInput, LeafProofExt};

/// In-memory representation of a single tree node during reduction. At layer 0 these wrap the leaf
/// proofs; at higher layers each entry is the result of folding two children.
pub struct LayerEntry {
    /// This node's serialized proof, held in memory (a leaf `Proof<QM31>` read from disk at layer
    /// 0, a freshly reserialized multiverifier `Proof<QM31>` at internal/carried nodes, or the
    /// Cairo verifier's felt252 arguments stream at the root — see [`reduce_pair`]). Kept in
    /// memory rather than round-tripped through a scratch file — one proof per live entry, freed
    /// as the layer is consumed.
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
    /// Builds the layer-0 entry for a leaf from its [`LeafInput`]: its proof, outputs, and
    /// preprocessed root all travel inline in the flattened
    /// [`leaf_proof_format::SerializedLeafProof`], the hashed-output preimage next to it.
    pub fn from_leaf(leaf: &LeafInput) -> Result<Self, RecursiveTreeError> {
        Ok(Self {
            proof_bytes: leaf.proof.proof.clone(),
            preprocessed_root: leaf.proof.preprocessed_root(),
            packed_output: PackedNode::leaf(
                leaf.proof.parse_output_values()?,
                digest_bytes_to_words(&leaf.proof.circuit_preprocessed_root),
                leaf.proof.program_output.clone(),
                leaf.output_preimage.clone(),
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
///
/// `is_root` marks the tree's final reduction. Its proof is consumed by the Cairo circuit verifier
/// rather than by another multiverifier fold, so it is proven with the standard lossless Blake2s
/// Merkle channel (internal folds use the M31 channel the multiverifier circuit verifies) and
/// serialized as the felt252 hex-string JSON stream `scarb execute --arguments-file` expects.
pub fn reduce_pair(
    left: LayerEntry,
    right: LayerEntry,
    layer_idx: usize,
    pair_idx: usize,
    canonical: &CanonicalCircuit,
    is_root: bool,
) -> Result<LayerEntry, RecursiveTreeError> {
    let _span = span!(Level::INFO, "reduce_pair", layer_idx, pair_idx, is_root).entered();

    let input0 = left.to_multiverifier_input(&canonical.shared_config.proof_config)?;
    let input1 = right.to_multiverifier_input(&canonical.shared_config.proof_config)?;

    let mut context = build_multiverifier_circuit::<QM31>(input0, input1, &canonical.shared_config);
    pad_to_targets(&mut context, TARGET_PADDING_SIZES);
    debug_assert!(
        context.is_circuit_valid(),
        "multiverifier circuit rejected its inputs at layer {layer_idx} pair {pair_idx}"
    );

    let (proof_bytes, extracted) = if is_root {
        let circuit_proof = prove_circuit_assignment_with_channel::<Blake2sMerkleChannel>(
            context.values(),
            &canonical.preprocessed_multiverifier,
            &canonical.base_column_pool,
            canonical.shared_config.pcs_config,
        )
        .map_err(|e| RecursiveTreeError::Proving(format!("{e:?}")))?;
        let extracted = extract_root_and_outputs(&circuit_proof)?;

        // Serialize for the Cairo circuit verifier: only the proof goes on the wire; the
        // verifier-config constants are baked into the Cairo binary.
        let component_log_sizes = circuit_component_log_sizes(
            &all_circuit_components::<NoValue>(),
            &canonical
                .preprocessed_multiverifier
                .preprocessed_trace
                .log_sizes(),
        );
        let felts = prepare_circuit_proof_for_cairo_verifier(circuit_proof, &component_log_sizes);
        let proof_hex: Vec<String> = felts.iter().map(|felt| format!("0x{felt:x}")).collect();
        let proof_bytes = serde_json::to_vec_pretty(&proof_hex)?;
        (proof_bytes, extracted)
    } else {
        let circuit_proof = prove_circuit_assignment(
            context.values(),
            &canonical.preprocessed_multiverifier,
            &canonical.base_column_pool,
            canonical.shared_config.pcs_config,
        )
        .map_err(|e| RecursiveTreeError::Proving(format!("{e:?}")))?;
        let extracted = extract_root_and_outputs(&circuit_proof)?;

        let (proof, _public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
        let mut proof_bytes = Vec::new();
        proof.serialize(&mut proof_bytes);
        (proof_bytes, extracted)
    };

    Ok(LayerEntry {
        proof_bytes,
        preprocessed_root: extracted.preprocessed_root,
        packed_output: PackedNode::internal(
            extracted.output_values,
            extracted.root_words,
            left.packed_output,
            right.packed_output,
        ),
    })
}

/// The parent-entry data extracted from a freshly proven circuit proof: its preprocessed root (as
/// the circuits' `HashValue` and as raw little-endian u32 words) and its circuit output values.
struct ExtractedProofData {
    preprocessed_root: HashValue<QM31>,
    root_words: [u32; N_RESERVED],
    output_values: [QM31; N_RESERVED],
}

/// Extracts the parent entry's preprocessed root and output values from a freshly proven circuit
/// proof — BEFORE the proof is consumed (both serialization paths take the `CircuitProof` by
/// value).
fn extract_root_and_outputs<H: MerkleHasherLifted<Hash = Blake2sHash>>(
    circuit_proof: &CircuitProof<H>,
) -> Result<ExtractedProofData, RecursiveTreeError> {
    let root_hash = circuit_proof.stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX];
    let root_words = digest_bytes_to_words(&root_hash.0);
    let preprocessed_root: HashValue<QM31> = root_hash.into();
    let outputs = circuit_proof.claim.output_values.clone();
    let output_values: [QM31; N_RESERVED] =
        outputs
            .try_into()
            .map_err(|v: Vec<QM31>| RecursiveTreeError::BadOutputArity {
                expected: N_RESERVED,
                got: v.len(),
            })?;
    Ok(ExtractedProofData {
        preprocessed_root,
        root_words,
        output_values,
    })
}

/// Reads a 32-byte digest as eight little-endian u32 words — the wire encoding of a preprocessed
/// root everywhere outside the circuits (matching `HashValue`'s `From<Blake2sHash>`).
pub fn digest_bytes_to_words(bytes: &[u8; 32]) -> [u32; N_RESERVED] {
    std::array::from_fn(|i| u32::from_le_bytes(bytes[i * 4..i * 4 + 4].try_into().unwrap()))
}

/// Nested packed-output tree — the circuit-world analogue of the old Cairo `PackedOutput` —
/// mirroring the leaf hash chain and the fold, one node per hash layer, so a future unpacker opens
/// exactly one hash per edge it walks:
///
/// ```text
/// Composite { output_values: O_L }                 // leaf circuit output; folds stack above this
///   └─ BootloaderOutput { program_output: H1 }     // O_L = circuit-blake2s(program_output)
///        └─ Plain { output_preimage }              // H1 = cairo0-blake2s(output_preimage)
/// ```
///
/// Each fold builds a `Composite` over its two children, so walking `subtasks` to the bottom
/// reaches every leaf's `Plain`, from which the unpacker reads the raw task output. Unlike Cairo's
/// fieldless `Plain` (whose data is sliced out of the parent's flat `outputs` via
/// `fact_topologies`), ours carries the data inline — the offset/topology unpacking doesn't apply
/// to circuit outputs, so a dedicated circuit-world unpacker just walks this tree.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PackedNode {
    /// A leaf's hashed-output preimage — the task's program hash followed by the task's raw output
    /// (each felt a decimal string; see `LeafInput::output_preimage`). Terminal — the
    /// analogue of Cairo `PackedOutput::Plain`, but carrying the reveal rather than being a bare
    /// marker.
    Plain { output_preimage: Vec<String> },
    /// The leaf simple bootloader's output: the Blake2s digest of its `Plain` child's preimage, as
    /// a Uint256 low/high pair of decimal felts (`SerializedLeafProof::program_output`). Has
    /// exactly one subtask, the `Plain` carrying the preimage.
    BootloaderOutput {
        program_output: Vec<String>,
        subtask: Box<PackedNode>,
    },
    /// A verifier / fold node: its `N_RESERVED` circuit output values (each as 4 little-endian
    /// `QM31` limbs), the preprocessed root of this node's proof (eight little-endian u32 words —
    /// the root the unpacker must use in this node's fold contribution; it looks the value up in
    /// its supported-roots trust list), and its child subtasks. The analogue of
    /// `CompositePackedOutput`.
    Composite {
        output_values: [[u32; 4]; N_RESERVED],
        preprocessed_root: [u32; N_RESERVED],
        subtasks: Vec<PackedNode>,
    },
}

impl PackedNode {
    /// A leaf entry, one node per hash layer: the leaf circuit's `output_values` over the
    /// bootloader's `program_output` over the `Plain` preimage reveal.
    pub fn leaf(
        output_values: [QM31; N_RESERVED],
        preprocessed_root: [u32; N_RESERVED],
        program_output: Vec<String>,
        output_preimage: Vec<String>,
    ) -> Self {
        PackedNode::Composite {
            output_values: output_values.map(|v| qm31_to_u32_limbs(&v)),
            preprocessed_root,
            subtasks: vec![PackedNode::BootloaderOutput {
                program_output,
                subtask: Box::new(PackedNode::Plain { output_preimage }),
            }],
        }
    }

    /// An internal fold node: the multiverifier's `output_values` over its two children.
    pub fn internal(
        output_values: [QM31; N_RESERVED],
        preprocessed_root: [u32; N_RESERVED],
        left: PackedNode,
        right: PackedNode,
    ) -> Self {
        PackedNode::Composite {
            output_values: output_values.map(|v| qm31_to_u32_limbs(&v)),
            preprocessed_root,
            subtasks: vec![left, right],
        }
    }

    /// This `Composite` node's circuit output values as raw `QM31` limbs. Panics on any other
    /// variant — every fold node (`LayerEntry::packed_output`) is a `Composite`;
    /// `BootloaderOutput`/`Plain` only ever appear inside a leaf's subtask chain.
    pub fn output_values(&self) -> &[[u32; 4]; N_RESERVED] {
        match self {
            PackedNode::Composite { output_values, .. } => output_values,
            PackedNode::BootloaderOutput { .. } | PackedNode::Plain { .. } => {
                unreachable!(
                    "output_values called on a non-Composite node; fold nodes are always Composite"
                )
            }
        }
    }

    /// This `Composite` node's output values as `QM31`s (inverse of the limb encoding). Panics on
    /// non-`Composite` nodes, as [`Self::output_values`].
    pub fn output_values_qm31(&self) -> [QM31; N_RESERVED] {
        self.output_values()
            .map(|[a, b, c, d]| qm31_from_u32s(a, b, c, d))
    }
}

/// Decomposes a `QM31` into its four little-endian `M31` limbs as raw `u32`s — the encoding used
/// for output values both in `PackedNode` and in a leaf's inline
/// [`leaf_proof_format::SerializedLeafProof`] outputs.
pub fn qm31_to_u32_limbs(value: &QM31) -> [u32; 4] {
    value.to_m31_array().map(|m| m.0)
}
