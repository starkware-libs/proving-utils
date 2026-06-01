use stwo_cairo_prover::stwo::core::fri::FriConfig;
use stwo_cairo_prover::stwo::core::pcs::PcsConfig;

// We expect the Cairo program to use all components except the following
pub const DISABLED_COMPONENTS: [&str; 4] = [
    "pedersen_builtin_narrow_windows",
    "pedersen_aggregator_window_bits_9",
    "partial_ec_mul_window_bits_9",
    "pedersen_points_table_window_bits_9",
];

// Configuration for the circuit that verifies the proof of the Cairo program:
pub const CIRCUIT_LOG_BLOWUP_FACTOR: u32 = 2;
pub const CIRCUIT_TRACE_LOG_SIZE: u32 = 21;

pub const CIRCUIT_FRI_CONFIG: FriConfig = FriConfig {
    log_blowup_factor: CIRCUIT_LOG_BLOWUP_FACTOR,
    log_last_layer_degree_bound: 0,
    n_queries: 35,
    fold_step: 4,
};

pub const CIRCUIT_PCS_CONFIG: PcsConfig = PcsConfig {
    pow_bits: 26,
    fri_config: CIRCUIT_FRI_CONFIG,
    lifting_log_size: Some(CIRCUIT_TRACE_LOG_SIZE + CIRCUIT_LOG_BLOWUP_FACTOR),
};
