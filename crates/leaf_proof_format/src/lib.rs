use serde::{Deserialize, Serialize};
use serde_with::base64::Base64;
use serde_with::serde_as;

/// Describes the structure of the output JSON file of the leaf prover.
#[serde_as]
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct SerializedLeafProof {
    /// The preprocessed root of the proof of the verifier circuit.
    pub circuit_preprocessed_root: [u8; 32],
    /// The serialized proof of the verifier circuit execution.
    #[serde_as(as = "Base64")]
    pub proof: Vec<u8>,
}
