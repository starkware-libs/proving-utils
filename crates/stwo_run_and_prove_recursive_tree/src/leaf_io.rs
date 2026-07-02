//! Loading the leaves for a fold.
//!
//! The binary is given a manifest (`{"leaves": ["<path>", ...]}`) listing one `leaf_prover` output
//! file per leaf. Each is a [`SerializedLeafProof`] — the shared `leaf_proof_format` type, so
//! producer and consumer share one definition of the wire format — carrying the leaf verifier
//! circuit's output values and preprocessed root plus the serialized `Proof<QM31>` inline (base64).
//! [`LeafProofExt`] adds the fold-side conversions.

use std::path::PathBuf;

use circuit_common::N_RESERVED;
use circuits::blake::{BLAKE2S_DIGEST_N_WORDS, HashValue};
use circuits::ivalue::qm31_from_u32s;
use leaf_proof_format::SerializedLeafProof;
use serde::Deserialize;
use stwo::core::fields::qm31::QM31;

use crate::RecursiveTreeError;

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

/// Reads the leaves manifest (`{"leaves": ["<path>", ...]}`) and loads each referenced
/// `leaf_prover` output file into a [`SerializedLeafProof`], preserving order.
pub fn load_leaves(path: &PathBuf) -> Result<Vec<SerializedLeafProof>, RecursiveTreeError> {
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
