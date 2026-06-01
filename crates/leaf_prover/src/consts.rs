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
