//! Loading the leaves for a fold.
//!
//! The binary is given a manifest (`{"leaves": ["<path>", ...]}`) listing one leaf input file per
//! leaf. Each is a [`LeafInput`]: the [`SerializedLeafProof`] `leaf_prover` produced — the shared
//! `leaf_proof_format` type, so producer and consumer share one definition of the wire format —
//! flattened together with the backend-injected bootloader context into one JSON object.
//! [`LeafProofExt`] adds the fold-side conversions.

use std::path::PathBuf;

use blake2::{Blake2s256, Digest};
use circuit_common::N_RESERVED;
use circuits::blake::{BLAKE2S_DIGEST_N_WORDS, HashValue};
use circuits::ivalue::IValue;
use circuits_stark_verifier::proof_from_stark_proof::pack_into_qm31s;
use leaf_proof_format::SerializedLeafProof;
use serde::{Deserialize, Serialize};
use starknet_types_core::felt::Felt;
use starknet_types_core::hash::Blake2Felt252;
use stwo::core::fields::qm31::QM31;
use stwo_cairo_common::prover_types::felt::split_f252;

use crate::RecursiveTreeError;

/// One leaf input to the recursive tree: the raw `leaf_prover` output plus the bootloader-level
/// context that `leaf_prover` doesn't know about (it proves an arbitrary Cairo run, not
/// specifically a bootloader run), so it cannot live on [`SerializedLeafProof`] itself. The
/// backend injects the extra fields next to the proof's own; `#[serde(flatten)]` keeps the file a
/// single flat JSON object.
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct LeafInput {
    /// The `leaf_prover` output file's contents, verbatim.
    #[serde(flatten)]
    pub proof: SerializedLeafProof,
    /// The preimage of the leaf's hashed output: the task's program hash followed by the task's
    /// raw output, each element a felt encoded as a decimal number. Dumped by the leaf simple
    /// bootloader to its `output_preimage_dump_path` and injected here by the backend.
    pub output_preimage: Vec<String>,
}

impl LeafInput {
    /// Recomputes this leaf circuit's `N_RESERVED` output words from `output_preimage`, replaying
    /// the leaf's hash chain out-of-circuit (the wire format carries only the preimage; every
    /// intermediate digest is derivable from it, so shipping them too would be redundant):
    /// 1. `H1 = blake2s(cairo0-encode(output_preimage))`: the digest the leaf simple bootloader
    ///    computes over its task's output and writes — as a Uint256 (low, high) felt pair — to its
    ///    own output segment.
    /// 2. `O_L = blake2s(limbs(H1.low) ++ limbs(H1.high))`: the digest the leaf cairo-verifier
    ///    circuit outputs over the bootloader outputs' 9-bit-limb encoding, recomputed with the
    ///    same `QM31::blake2s` packing the circuit uses.
    pub fn output_values(&self) -> Result<[u32; N_RESERVED], RecursiveTreeError> {
        let preimage: Vec<Felt> = self
            .output_preimage
            .iter()
            .map(|felt| {
                Felt::from_dec_str(felt).map_err(|e| RecursiveTreeError::BadLeafOutputs {
                    reason: format!("invalid decimal felt {felt:?} in output_preimage: {e}"),
                })
            })
            .collect::<Result<_, _>>()?;

        // 1. H1, over the same u32-word encoding Cairo's `encode_felt252_data_and_calc_blake2s`
        // hashes; its 32 digest bytes split into the Uint256 halves as eight little-endian words.
        let encoded_bytes: Vec<u8> = Blake2Felt252::encode_felts_to_u32s(&preimage)
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect();
        let h1: [u8; 32] = Blake2s256::digest(&encoded_bytes).into();
        let h1_words: [u32; BLAKE2S_DIGEST_N_WORDS] =
            std::array::from_fn(|i| u32::from_le_bytes(h1[i * 4..i * 4 + 4].try_into().unwrap()));

        // 2. O_L. Each Uint256 half (four digest words, zero-extended to felt width) is one
        // bootloader-output felt; `split_f252` decomposes it into the 9-bit limbs the circuit
        // hashes.
        let limbs = h1_words
            .chunks_exact(4)
            .flat_map(|half| split_f252(std::array::from_fn(|i| if i < 4 { half[i] } else { 0 })));
        let output_qm31s = pack_into_qm31s(limbs);
        let output_hash = QM31::blake2s(&output_qm31s, output_qm31s.len() * 16);
        Ok(std::array::from_fn(|i| output_hash[i].get().unpack_u32()))
    }
}

/// Fold-side conversions on a [`SerializedLeafProof`] — the typed values the fold needs from a
/// leaf's wire data. Kept in this crate (not in `leaf_proof_format`) so the shared format crate
/// stays dependency-light.
pub trait LeafProofExt {
    /// This leaf circuit's preprocessed root as a [`HashValue<QM31>`]: the 32 digest bytes read as
    /// eight little-endian words (matching `From<Blake2sHash>`, the same conversion `reduce_pair`
    /// applies to internal-node roots). The multiverifier uses it to verify this leaf.
    fn preprocessed_root(&self) -> HashValue<QM31>;
}

impl LeafProofExt for SerializedLeafProof {
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
