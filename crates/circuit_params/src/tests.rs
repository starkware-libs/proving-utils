use std::collections::BTreeMap;

use circuit_registry::{
    CircuitConfig, CircuitRegistry, LeafVerifier, LogSizes, Multiverifier, RootHex,
};

#[test]
fn json_output_round_trips() {
    let registry = CircuitRegistry {
        circuit_configs: BTreeMap::from([(
            "default".to_string(),
            CircuitConfig {
                log_blowup_factor: 1,
                component_log_sizes: LogSizes {
                    eq: 10,
                    qm31_ops: 11,
                    m31_to_u32: 12,
                    triple_xor: 13,
                    blake_g_gate: 14,
                },
            },
        )]),
        leaf_verifiers: vec![LeafVerifier {
            config: "default".to_string(),
            trace_log_size: 20,
            log_blowup_factor: 1,
            preprocessed_root: RootHex([0x0123_4567, 1, 2, 3, 4, 5, 6, 0xffff_ffff]),
        }],
        multiverifiers: vec![Multiverifier {
            config: "default".to_string(),
            input_configs: ["default".to_string(), "default".to_string()],
            preprocessed_root: RootHex([7, 8, 9, 10, 11, 12, 13, 14]),
        }],
    };

    let serialized = serde_json::to_string_pretty(&registry).unwrap();
    let deserialized: CircuitRegistry = serde_json::from_str(&serialized).unwrap();
    let reserialized = serde_json::to_string_pretty(&deserialized).unwrap();

    assert!(serialized == reserialized);
}
