//! The JSON schema for the circuit registry: a map of circuit configs, the leaf verifiers (one per
//! trace size), and the multiverifiers, each with its preprocessed root.

use std::collections::BTreeMap;

use circuit_common::finalize::ComponentSizes;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The padded log sizes of the verifier circuit's AIR components.
#[derive(Serialize, Deserialize)]
pub struct LogSizes {
    pub eq: u32,
    pub qm31_ops: u32,
    pub m31_to_u32: u32,
    pub triple_xor: u32,
    pub blake_g_gate: u32,
}

impl From<&ComponentSizes> for LogSizes {
    fn from(padded: &ComponentSizes) -> Self {
        LogSizes {
            eq: log_size(padded.eq),
            qm31_ops: log_size(padded.qm31_ops),
            m31_to_u32: log_size(padded.m31_to_u32),
            triple_xor: log_size(padded.triple_xor),
            blake_g_gate: log_size(padded.blake_g_gate),
        }
    }
}

impl From<&LogSizes> for ComponentSizes {
    fn from(log: &LogSizes) -> Self {
        ComponentSizes {
            eq: 1 << log.eq,
            qm31_ops: 1 << log.qm31_ops,
            m31_to_u32: 1 << log.m31_to_u32,
            triple_xor: 1 << log.triple_xor,
            blake_g_gate: 1 << log.blake_g_gate,
        }
    }
}

fn log_size(size: usize) -> u32 {
    size.next_power_of_two().ilog2()
}

/// A preprocessed-trace Merkle root: eight little-endian u32 words, serialized as an array of
/// `0x`-prefixed hex strings.
pub struct RootHex(pub [u32; 8]);

impl Serialize for RootHex {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.map(|word| format!("{word:#010x}")).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for RootHex {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let words: [String; 8] = Deserialize::deserialize(deserializer)?;
        let mut root = [0u32; 8];
        for (out, word) in root.iter_mut().zip(words) {
            let hex = word.strip_prefix("0x").unwrap_or(&word);
            *out = u32::from_str_radix(hex, 16).map_err(serde::de::Error::custom)?;
        }
        Ok(RootHex(root))
    }
}

impl RootHex {
    /// The root as 32 little-endian bytes, matching a proof's `circuit_preprocessed_root`.
    pub fn to_le_bytes(&self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for (word, chunk) in self.0.iter().zip(bytes.chunks_exact_mut(4)) {
            chunk.copy_from_slice(&word.to_le_bytes());
        }
        bytes
    }
}

/// A circuit configuration: the (circuit-prover) log blowup factor and padded component log sizes a
/// circuit is proven with. Circuits sharing a config produce proofs a common AIR can verify.
#[derive(Serialize, Deserialize)]
pub struct CircuitConfig {
    pub log_blowup_factor: u32,
    pub component_log_sizes: LogSizes,
}

/// A leaf verifier circuit (verifying one Cairo proof of the given trace size and log blowup
/// factor), padded to its config's component sizes.
#[derive(Serialize, Deserialize)]
pub struct LeafVerifier {
    /// Key into `CircuitRegistry::circuit_configs`.
    pub config: String,
    pub trace_log_size: u32,
    /// Log blowup factor of the Cairo proof this leaf verifies.
    pub log_blowup_factor: u32,
    pub preprocessed_root: RootHex,
}

/// The multiverifier circuit, padded to its config's component sizes.
#[derive(Serialize, Deserialize)]
pub struct Multiverifier {
    /// Key into `CircuitRegistry::circuit_configs`: the multiverifier's own config.
    pub config: String,
    /// Configs of the two circuits whose proofs the multiverifier verifies.
    pub input_configs: [String; 2],
    pub preprocessed_root: RootHex,
}

/// The json output: a map of circuit configs, the leaf verifiers (one per trace size), and the
/// multiverifiers. All circuits are padded to the shared target sizes and proven with the same
/// blowup, so they share a single config; the multiverifier verifies proofs of the leaf circuit and
/// is essentially the same across trace sizes, so a single multiverifier is reported.
#[derive(Serialize, Deserialize)]
pub struct CircuitRegistry {
    pub circuit_configs: BTreeMap<String, CircuitConfig>,
    pub leaf_verifiers: Vec<LeafVerifier>,
    pub multiverifiers: Vec<Multiverifier>,
}

impl CircuitRegistry {
    /// The supported leaf verifier for a Cairo proof with the given trace log size and log blowup
    /// factor, or `None` if the registry doesn't list it.
    pub fn leaf_verifier(
        &self,
        trace_log_size: u32,
        log_blowup_factor: u32,
    ) -> Option<&LeafVerifier> {
        self.leaf_verifiers.iter().find(|leaf| {
            leaf.trace_log_size == trace_log_size && leaf.log_blowup_factor == log_blowup_factor
        })
    }

    /// The component-size pad target of the given config, or `None` if the config is unknown.
    pub fn config_pad_target(&self, config: &str) -> Option<ComponentSizes> {
        self.circuit_configs.get(config).map(|config| (&config.component_log_sizes).into())
    }
}
