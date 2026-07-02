//! Loading the leaves list from disk.
//!
//! Each leaf is described by a [`LeafInput`]: its public output values and preprocessed root
//! inline, plus a path to its serialized `Proof<QM31>`. Both are inline (rather than read from the
//! proof) because neither is recoverable from the serialized proof: the outputs are the circuit's
//! public data (`prepare_circuit_proof_for_circuit_verifier` splits them into a separate
//! `CircuitPublicData`, and only `Proof<QM31>` is serialized), and the serialized proof carries the
//! trace / interaction / composition roots but NOT the preprocessed root. Declaring the root per
//! leaf is also what keeps the fold agnostic to the leaf's circuit type — see [`LeafInput`].

use std::path::PathBuf;

use circuit_common::N_RESERVED;
use circuits::blake::BLAKE2S_DIGEST_N_WORDS;
use circuits::ivalue::qm31_from_u32s;
use serde::{Deserialize, Serialize};
use stwo::core::fields::qm31::QM31;

use crate::RecursiveTreeError;

/// A leaf as listed in the leaves JSON: the leaf circuit's public output values and preprocessed
/// root, plus the path to its serialized `Proof<QM31>`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct LeafInput {
    /// Leaf train id; carried for logs so the binary's output can be cross-referenced against the
    /// pipeline when something fails mid-reduction.
    pub train_id: u64,
    /// The leaf circuit's public output values, one `[u32; 4]` per `QM31` (little-endian limbs).
    /// Must have exactly `N_RESERVED` entries.
    pub output_values: Vec<[u32; 4]>,
    /// Preprocessed (Merkle) root of the circuit that produced this leaf's proof, as
    /// `BLAKE2S_DIGEST_N_WORDS` little-endian words. The multiverifier needs it to verify the
    /// leaf, and it is not recoverable from the serialized proof, so it is declared here. This
    /// is what makes the fold agnostic to the leaf's circuit type: a cairo-verifier leaf
    /// carries the cairo-verifier root, a folded-subtree leaf carries the multiverifier root,
    /// and either verifies against the same canonical shape.
    pub preprocessed_root: [u32; BLAKE2S_DIGEST_N_WORDS],
    /// Path to the leaf's serialized `Proof<QM31>`.
    pub proof_path: PathBuf,
}

impl LeafInput {
    /// This leaf's [`Self::output_values`] as `QM31`s, validating the count.
    pub fn parse_output_values(&self) -> Result<[QM31; N_RESERVED], RecursiveTreeError> {
        if self.output_values.len() != N_RESERVED {
            return Err(RecursiveTreeError::BadLeafOutputs {
                train_id: self.train_id,
                reason: format!(
                    "expected {N_RESERVED} output values, got {}",
                    self.output_values.len()
                ),
            });
        }
        Ok(std::array::from_fn(|i| {
            let [a, b, c, d] = self.output_values[i];
            qm31_from_u32s(a, b, c, d)
        }))
    }
}

/// Reads the leaves JSON file (`{"leaves": [LeafInput, ...]}`) and returns the inner list.
pub fn load_leaves(path: &PathBuf) -> Result<Vec<LeafInput>, RecursiveTreeError> {
    #[derive(Deserialize)]
    struct LeavesFile {
        leaves: Vec<LeafInput>,
    }
    let content =
        std::fs::read_to_string(path).map_err(|e| RecursiveTreeError::PathIO(e, path.clone()))?;
    let file: LeavesFile = serde_json::from_str(&content)?;
    Ok(file.leaves)
}
