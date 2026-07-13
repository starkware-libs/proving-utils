use serde::{Deserialize, Serialize};
use serde_with::base64::Base64;
use serde_with::serde_as;

/// Describes the structure of the output JSON file
#[serde_as]
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct SerializedLeafProof {
    /// The output of the Cairo program received. Each element is a felt, encoded as a decimal
    /// number.
    pub program_output: Vec<String>,
    /// The output of the verifier circuit
    pub circuit_output: Vec<[u32; 4]>,
    /// The preprocessed root of the proof of the verifier circuit.
    pub circuit_preprocessed_root: [u8; 32],
    /// The serialized proof of the verifier circuit execution
    #[serde_as(as = "Base64")]
    pub proof: Vec<u8>,
}
