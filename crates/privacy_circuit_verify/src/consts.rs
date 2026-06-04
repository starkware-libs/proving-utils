use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;

pub const NUM_OUTPUTS: usize = 1;

/// Uncompressed size in bytes of the serialized cairo proof (including public claim prefix).
pub const CAIRO_PROOF_UNCOMPRESSED_BYTES: usize = 627_244;

/// Uncompressed size in bytes of the serialized recursive circuit proof.
pub const RECURSIVE_PROOF_UNCOMPRESSED_BYTES: usize = 263_796;

/// Multiplicative safety factor applied to the proof size constants to derive decompression limits
/// used in `verify_cairo` and `verify_recursive_circuit` as zip-bomb protection.
pub const PROOF_MAX_DECOMPRESSED_RATIO: usize = 2;

/// Maximum allowed uncompressed size in bytes when decompressing the cairo proof.
/// Used in `verify_cairo` to prevent zip-bomb attacks.
pub const MAX_CAIRO_PROOF_UNCOMPRESSED_BYTES: usize =
    CAIRO_PROOF_UNCOMPRESSED_BYTES * PROOF_MAX_DECOMPRESSED_RATIO;

/// Maximum allowed uncompressed size in bytes when decompressing the recursive circuit proof.
/// Used in `verify_recursive_circuit` to prevent zip-bomb attacks.
pub const MAX_RECURSIVE_PROOF_UNCOMPRESSED_BYTES: usize =
    RECURSIVE_PROOF_UNCOMPRESSED_BYTES * PROOF_MAX_DECOMPRESSED_RATIO;

// Source code for this compiled privacy bootloader can be found at:
// repo: https://github.com/starkware-industries/starkware
// branch: "dev"
// commit: "4d1ae5848dd49802ddd620601d2d1bb303d15c66"
// md5sum: "0494f41365e482142d04b58bd64aa5fe"
// Compiled by command:
// `bazel build --config=rbe
// //src/starkware/cairo/bootloaders/simple_bootloader:privacy_simple_bootloader_program`
pub const PRIVACY_BOOTLOADER_JSON: &[u8] = include_bytes!(
    "../../cairo-program-runner-lib/resources/compiled_programs/bootloaders/privacy_simple_bootloader_compiled.json"
);
pub const CIRCUIT_OUTPUT_ADDRESSES: [usize; 3] = [3, 4, 2];
pub const PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT: [u32; 8] = [
    1226144497, 1215753816, 1261723493, 447821635, 511752374, 214804093, 1020993193, 1889786400,
];
pub const CAIRO_LOG_BLOWUP_FACTOR: u32 = 3;
pub const CAIRO_TRACE_LOG_SIZE: u32 = 20;
pub const CIRCUIT_LOG_BLOWUP_FACTOR: u32 = 2;
pub const CIRCUIT_TRACE_LOG_SIZE: u32 = 21;

pub const CAIRO_FRI_CONFIG: FriConfig = FriConfig {
    log_blowup_factor: CAIRO_LOG_BLOWUP_FACTOR,
    log_last_layer_degree_bound: 0,
    n_queries: 23,
    fold_step: 4,
};

pub const CAIRO_PCS_CONFIG: PcsConfig = PcsConfig {
    pow_bits: 27,
    fri_config: CAIRO_FRI_CONFIG,
    lifting_log_size: Some(CAIRO_TRACE_LOG_SIZE + CAIRO_LOG_BLOWUP_FACTOR),
};

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

// The set of components that are used to verify the privacy transaction.
// The order of the components is determend by the order in circuit_cairo_air::all_components()
pub const PRIVACY_TRANSACTION_COMPONENTS: [&str; 57] = [
    "add_opcode",
    "add_opcode_small",
    "add_ap_opcode",
    "assert_eq_opcode",
    "assert_eq_opcode_imm",
    "assert_eq_opcode_double_deref",
    "blake_compress_opcode",
    "call_opcode_abs",
    "call_opcode_rel_imm",
    "jnz_opcode_non_taken",
    "jnz_opcode_taken",
    "jump_opcode_abs",
    "jump_opcode_double_deref",
    "jump_opcode_rel",
    "jump_opcode_rel_imm",
    "mul_opcode",
    "mul_opcode_small",
    "ret_opcode",
    "verify_instruction",
    "blake_round",
    "blake_g",
    "blake_round_sigma",
    "triple_xor_32",
    "verify_bitwise_xor_12",
    "bitwise_builtin",
    "pedersen_builtin_narrow_windows",
    "poseidon_builtin",
    "range_check_builtin",
    "pedersen_aggregator_window_bits_9",
    "partial_ec_mul_window_bits_9",
    "pedersen_points_table_window_bits_9",
    "poseidon_aggregator",
    "poseidon_3_partial_rounds_chain",
    "poseidon_full_round_chain",
    "cube_252",
    "poseidon_round_keys",
    "range_check_252_width_27",
    "memory_address_to_id",
    "memory_id_to_big",
    "memory_id_to_small",
    "range_check_6",
    "range_check_8",
    "range_check_11",
    "range_check_12",
    "range_check_18",
    "range_check_20",
    "range_check_4_3",
    "range_check_4_4",
    "range_check_9_9",
    "range_check_7_2_5",
    "range_check_3_6_6_3",
    "range_check_4_4_4_4",
    "range_check_3_3_3_3_3",
    "verify_bitwise_xor_4",
    "verify_bitwise_xor_7",
    "verify_bitwise_xor_8",
    "verify_bitwise_xor_9",
];

/// Log sizes (in size-sorted order, matching `PRIVACY_CIRCUIT_PREPROCESSED_IDS`) of the
/// preprocessed columns in the recursive circuit. Each entry is the `ilog2` of the number of
/// rows in the corresponding column.
pub const PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES: [u32; 45] = [
    8, 8, 8, // bitwise_xor_4_{0,1,2}: 2^(2*4) = 2^8
    14, 14, 14, //  bitwise_xor_7_{0,1,2}: 2^(2*7) = 2^14
    16, 16, 16, 16, // bitwise_xor_8_{0,1,2}: 2^(2*8) = 2^16
    17, 17, // eq
    17, 17, 17, 17, 17, // triple_xor
    18, 18, 18, // m31_to_u32
    18, 18, 18, // bitwise_xor_9_{0,1,2}: 2^(2*9) = 2^18
    20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, // blake_g_gate
    20, 20, 20, // bitwise_xor_10_{0,1,2}: 2^(2*10) = 2^20
    21, 21, 21, 21, 21, 21, 21, 21, // qm31 ops
];

pub const PRIVACY_CIRCUIT_PREPROCESSED_IDS: [&str; 45] = [
    "bitwise_xor_4_0",
    "bitwise_xor_4_1",
    "bitwise_xor_4_2",
    "bitwise_xor_7_0",
    "bitwise_xor_7_1",
    "bitwise_xor_7_2",
    "seq_16",
    "bitwise_xor_8_0",
    "bitwise_xor_8_1",
    "bitwise_xor_8_2",
    "eq_in0_address",
    "eq_in1_address",
    "triple_xor_input_addr_0",
    "triple_xor_input_addr_1",
    "triple_xor_input_addr_2",
    "triple_xor_output_addr",
    "triple_xor_multiplicity",
    "m31_to_u32_input_addr",
    "m31_to_u32_output_addr",
    "m31_to_u32_multiplicity",
    "bitwise_xor_9_0",
    "bitwise_xor_9_1",
    "bitwise_xor_9_2",
    "blake_g_gate_input_addr_a",
    "blake_g_gate_input_addr_b",
    "blake_g_gate_input_addr_c",
    "blake_g_gate_input_addr_d",
    "blake_g_gate_input_addr_f0",
    "blake_g_gate_input_addr_f1",
    "blake_g_gate_output_addr_a",
    "blake_g_gate_output_addr_b",
    "blake_g_gate_output_addr_c",
    "blake_g_gate_output_addr_d",
    "blake_g_gate_multiplicity",
    "bitwise_xor_10_0",
    "bitwise_xor_10_1",
    "bitwise_xor_10_2",
    "qm31_ops_add_flag",
    "qm31_ops_sub_flag",
    "qm31_ops_mul_flag",
    "qm31_ops_pointwise_mul_flag",
    "qm31_ops_in0_address",
    "qm31_ops_in1_address",
    "qm31_ops_out_address",
    "qm31_ops_mults",
];
