//! Loading the leaves for a fold.
//!
//! The binary is given a manifest (`{"leaves": ["<path>", ...]}`) listing one leaf input file per
//! leaf. Each is a [`LeafInput`]: the [`SerializedLeafProof`] `leaf_prover` produced — the shared
//! `leaf_proof_format` type, so producer and consumer share one definition of the wire format —
//! flattened together with the backend-injected bootloader context into one JSON object.
//! [`LeafProofExt`] adds the fold-side conversions.

use std::path::PathBuf;

use circuit_common::N_RESERVED;
use circuits::blake::{BLAKE2S_DIGEST_N_WORDS, HashValue};
use circuits::ivalue::qm31_from_u32s;
use leaf_proof_format::SerializedLeafProof;
use serde::{Deserialize, Serialize};
use stwo::core::fields::qm31::QM31;

use crate::RecursiveTreeError;

/// One leaf input to the recursive tree: the raw `leaf_prover` output plus the bootloader-level
/// context that `leaf_prover` doesn't know about (it proves an arbitrary Cairo run, not
/// specifically a bootloader run), so it cannot live on [`SerializedLeafProof`] itself. The
/// backend injects the extra fields next to the proof's own; `#[serde(flatten)]` keeps the file a
/// single flat JSON object.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LeafInput {
    /// The `leaf_prover` output file's contents, verbatim.
    #[serde(flatten)]
    pub proof: SerializedLeafProof,
    /// The preimage of `proof.program_output` (which is its Blake2s digest as a Uint256 low/high
    /// pair): the task's program hash followed by the task's raw output, each element a felt
    /// encoded as a decimal number. Dumped by the leaf simple bootloader to its
    /// `output_preimage_dump_path` and injected here by the backend.
    pub output_preimage: Vec<String>,
}

/// Fold-side conversions on a [`SerializedLeafProof`] — the typed values the fold needs from a
/// leaf's wire data. Kept in this crate (not in `leaf_proof_format`) so the shared format crate
/// stays dependency-light.
pub trait LeafProofExt {
    /// This leaf's circuit output values as `QM31`s, validating the count is `N_RESERVED`.
    fn parse_output_values(&self) -> Result<[QM31; N_RESERVED], RecursiveTreeError>;

    /// This leaf circuit's preprocessed root as a [`HashValue<QM31>`]: the 32 digest bytes read as
    /// eight little-endian words (matching `From<Blake2sHash>`, the same conversion `reduce_pair`
    /// applies to internal-node roots). The multiverifier uses it to verify this leaf.
    fn preprocessed_root(&self) -> HashValue<QM31>;
}

impl LeafProofExt for SerializedLeafProof {
    fn parse_output_values(&self) -> Result<[QM31; N_RESERVED], RecursiveTreeError> {
        if self.circuit_output.len() != N_RESERVED {
            return Err(RecursiveTreeError::BadLeafOutputs {
                reason: format!(
                    "expected {N_RESERVED} circuit output values, got {}",
                    self.circuit_output.len()
                ),
            });
        }
        Ok(std::array::from_fn(|i| {
            let [a, b, c, d] = self.circuit_output[i];
            qm31_from_u32s(a, b, c, d)
        }))
    }

    fn preprocessed_root(&self) -> HashValue<QM31> {
        let words: [u32; BLAKE2S_DIGEST_N_WORDS] = std::array::from_fn(|i| {
            u32::from_le_bytes(
                self.circuit_preprocessed_root[i * 4..i * 4 + 4]
                    .try_into()
                    .unwrap(),
            )
        });
        HashValue::from(words)
    }
}

/// Reads the leaves manifest (`{"leaves": ["<path>", ...]}`) and loads each referenced leaf input
/// file into a [`LeafInput`], preserving order.
pub fn load_leaves(path: &PathBuf) -> Result<Vec<LeafInput>, RecursiveTreeError> {
    #[derive(Deserialize)]
    struct LeavesManifest {
        leaves: Vec<PathBuf>,
    }
    let content =
        std::fs::read_to_string(path).map_err(|e| RecursiveTreeError::PathIO(e, path.clone()))?;
    let manifest: LeavesManifest = serde_json::from_str(&content)?;
    manifest
        .leaves
        .iter()
        .map(|leaf_path| {
            let leaf_json = std::fs::read_to_string(leaf_path)
                .map_err(|e| RecursiveTreeError::PathIO(e, leaf_path.clone()))?;
            Ok(serde_json::from_str(&leaf_json)?)
        })
        .collect()
}
