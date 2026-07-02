//! Loading the leaves for a fold.
//!
//! The binary is given a manifest (`{"leaves": ["<path>", ...]}`) listing one `leaf_prover` output
//! file per leaf. Each of those files is a [`LeafInput`] — a mirror of `leaf_prover`'s
//! `LeafProverSerializedOutput` (matching field names, so it deserializes directly): the leaf
//! verifier circuit's output values and preprocessed root, plus the serialized `Proof<QM31>`
//! (base64) inline.

use std::path::PathBuf;

use circuit_common::N_RESERVED;
use circuits::blake::{BLAKE2S_DIGEST_N_WORDS, HashValue};
use circuits::ivalue::qm31_from_u32s;
use serde::{Deserialize, Serialize};
use serde_with::base64::Base64;
use serde_with::serde_as;
use stwo::core::fields::qm31::QM31;

use crate::RecursiveTreeError;

/// One leaf, mirroring `leaf_prover`'s `LeafProverSerializedOutput`. Field names match so a
/// leaf-output JSON deserializes straight into this.
#[serde_as]
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct LeafInput {
    /// The Cairo program's output, each felt as a decimal string. Carried through for a future
    /// unpacking.
    pub program_output: Vec<String>,
    /// The leaf verifier circuit's output values, one `[u32; 4]` per `QM31` (little-endian limbs)
    /// — the statement the multiverifier hashes. Must have exactly `N_RESERVED` entries.
    pub circuit_output: Vec<[u32; 4]>,
    /// Preprocessed (Merkle) root of the leaf verifier circuit, as a 32-byte Blake2s digest.
    pub circuit_preprocessed_root: [u8; 32],
    /// The leaf circuit's serialized `Proof<QM31>`, base64-encoded in JSON.
    #[serde_as(as = "Base64")]
    pub proof: Vec<u8>,
}

impl LeafInput {
    /// This leaf's [`Self::circuit_output`] as `QM31`s, validating the count.
    pub fn parse_output_values(&self) -> Result<[QM31; N_RESERVED], RecursiveTreeError> {
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

    /// The leaf circuit's preprocessed root as a [`HashValue<QM31>`]. The multiverifier uses it to
    /// verify this leaf.
    pub fn preprocessed_root(&self) -> HashValue<QM31> {
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
/// `leaf_prover` output file into a [`LeafInput`], preserving order.
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
