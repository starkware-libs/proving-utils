use circuit_common::finalize::ComponentSizes;

// We expect a Cairo program that uses the "canonical" preprocessed trace to
// use all components except the following
pub const DISABLED_COMPONENTS_CANONICAL_PREPROCESSED: [&str; 4] = [
    "pedersen_builtin_narrow_windows",
    "pedersen_aggregator_window_bits_9",
    "partial_ec_mul_window_bits_9",
    "pedersen_points_table_window_bits_9",
];

// We expect a Cairo program that uses the "small" preprocessed trace to
// use all components except the following
pub const DISABLED_COMPONENTS_SMALL_PREPROCESSED: [&str; 4] = [
    "pedersen_builtin",
    "pedersen_aggregator_window_bits_18",
    "partial_ec_mul_window_bits_18",
    "pedersen_points_table_window_bits_18",
];

// TODO(ilya): Load from file.
pub const DEFAULT_CONFIG_COMPONENT_SIZES: ComponentSizes = ComponentSizes {
    eq: 1 << 20,
    qm31_ops: 1 << 23,
    m31_to_u32: 1 << 20,
    triple_xor: 1 << 19,
    blake_g_gate: 1 << 23,
};
