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
use circuits::ivalue::{IValue, NoValue};
use circuits_stark_verifier::proof::ProofConfig;
use serde::{Deserialize, Serialize};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
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
    /// This node's circuit output words (the unreduced Blake2s digest the circuit outputs):
    /// derived from the leaf's `output_preimage` at layer 0, read from the fresh proof's claim at
    /// internal nodes. The multiverifier needs them to verify this node at the next layer.
    pub output_values: [u32; N_RESERVED],
    /// Nested packed-output subtree rooted at this node.
    pub packed_output: PackedNode,
}

impl LayerEntry {
    /// Builds the layer-0 entry for a leaf from its [`LeafInput`]: the proof and preprocessed root
    /// travel inline in the flattened [`leaf_proof_format::SerializedLeafProof`], and the output
    /// values are recomputed from the hashed-output preimage next to it.
    pub fn from_leaf(leaf: &LeafInput) -> Result<Self, RecursiveTreeError> {
        Ok(Self {
            proof_bytes: leaf.proof.proof.clone(),
            preprocessed_root: leaf.proof.preprocessed_root(),
            output_values: leaf.output_values()?,
            packed_output: PackedNode::leaf(leaf.output_preimage.clone()),
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
            output_values: self.output_values,
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

    let (proof_bytes, preprocessed_root, output_values) = if is_root {
        // The Cairo verifier does not carry `min_lifting_log_size` on the wire and mixes 0 into
        // its channel, so the root proof must be created with 0 (`CairoSerialize for PcsConfig`
        // asserts it).
        let root_pcs_config = PcsConfig {
            min_lifting_log_size: 0,
            ..canonical.shared_config.pcs_config
        };
        let circuit_proof = prove_circuit_assignment_with_channel::<Blake2sMerkleChannel>(
            context.values(),
            &canonical.preprocessed_multiverifier,
            &canonical.base_column_pool,
            root_pcs_config,
        )
        .map_err(|e| RecursiveTreeError::Proving(format!("{e:?}")))?;
        let (preprocessed_root, output_values) = extract_root_and_outputs(&circuit_proof)?;

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
        (proof_bytes, preprocessed_root, output_values)
    } else {
        let circuit_proof = prove_circuit_assignment(
            context.values(),
            &canonical.preprocessed_multiverifier,
            &canonical.base_column_pool,
            canonical.shared_config.pcs_config,
        )
        .map_err(|e| RecursiveTreeError::Proving(format!("{e:?}")))?;
        let (preprocessed_root, output_values) = extract_root_and_outputs(&circuit_proof)?;

        let (proof, _public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
        let mut proof_bytes = Vec::new();
        proof.serialize(&mut proof_bytes);
        (proof_bytes, preprocessed_root, output_values)
    };

    Ok(LayerEntry {
        proof_bytes,
        preprocessed_root,
        output_values,
        packed_output: PackedNode::internal(left.packed_output, right.packed_output),
    })
}

/// Extracts the parent entry's preprocessed root and output values from a freshly proven circuit
/// proof. The claim's outputs are packed-`u32` `QM31`s; they are unpacked back to the raw digest
/// words.
fn extract_root_and_outputs<H: MerkleHasherLifted<Hash = Blake2sHash>>(
    circuit_proof: &CircuitProof<H>,
) -> Result<(HashValue<QM31>, [u32; N_RESERVED]), RecursiveTreeError> {
    let root_hash = circuit_proof.stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX];
    let preprocessed_root: HashValue<QM31> = root_hash.into();
    let outputs: Vec<u32> = circuit_proof
        .claim
        .output_values
        .iter()
        .map(|qm31| qm31.unpack_u32())
        .collect();
    let output_values: [u32; N_RESERVED] =
        outputs
            .try_into()
            .map_err(|v: Vec<u32>| RecursiveTreeError::BadOutputArity {
                expected: N_RESERVED,
                got: v.len(),
            })?;
    Ok((preprocessed_root, output_values))
}

/// Nested packed-output tree:
///
/// ```text
/// Composite { subtasks: [left, right] }   // a fold: the multiverifier over two children
///   ...
///     Composite { subtasks: [plain] }     // a leaf: the cairo-verifier circuit over one task run
///       └─ Plain { output_preimage }      // terminal: the leaf task's revealed output
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PackedNode {
    /// A leaf's hashed-output preimage — the task's program hash followed by the task's raw output
    /// (each felt a decimal string; see `LeafInput::output_preimage`).
    Plain { output_preimage: Vec<String> },
    /// A verifier node — a fold over two children, or the leaf circuit over its single `Plain`
    /// child.
    Composite { subtasks: Vec<PackedNode> },
}

impl PackedNode {
    /// A leaf entry: the leaf circuit node over the `Plain` preimage reveal.
    pub fn leaf(output_preimage: Vec<String>) -> Self {
        PackedNode::Composite {
            subtasks: vec![PackedNode::Plain { output_preimage }],
        }
    }

    /// An internal fold node over its two children.
    pub fn internal(left: PackedNode, right: PackedNode) -> Self {
        PackedNode::Composite {
            subtasks: vec![left, right],
        }
    }
}
