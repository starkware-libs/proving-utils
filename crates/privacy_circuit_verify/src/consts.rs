use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;

pub const NUM_OUTPUTS: usize = 1;

/// Uncompressed size in bytes of the serialized cairo proof (including public claim prefix).
pub const CAIRO_PROOF_UNCOMPRESSED_BYTES: usize = 627_076;

/// Uncompressed size in bytes of the serialized recursive circuit proof.
pub const RECURSIVE_PROOF_UNCOMPRESSED_BYTES: usize = 373_108;

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
pub const CIRCUIT_OUTPUT_ADDRESSES: [usize; 3] = [222372, 222373, 2];
pub const CIRCUIT_N_BLAKE_GATES: usize = 4327;
pub const PRIVACY_CAIRO_VERIFIER_CONSTS_HASH: [u32; 8] = [
    837290355, 304184779, 934540983, 1030030586, 1068923910, 438446145, 1309815623, 423450064,
];
pub const PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT: [u32; 8] = [
    1787343855, 1667756218, 1239742483, 1200082828, 1596742667, 1869219239, 827237313, 1161827047,
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
pub const PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES: [u32; 79] = [
    // blake_sigma_0..15: 16 rows each
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    // triple_xor_{input_addr_0,1,2,output_addr,multiplicity}
    4, 4, 4, 4, 4, // m31_to_u32_{input_addr,output_addr,multiplicity}
    4, 4, 4, // blake_g_gate_{input_addr_a,b,c,d,f0,f1,output_addr_a,b,c,d,multiplicity}
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, // seq_4
    4, // bitwise_xor_4_{0,1,2}: 2^(2*4) = 256 rows
    8, 8, 8,
    // final_state_addr, blake_output{0,1}_addr, blake_output{0,1}_mults: next_pow2(4321)=8192=2^13
    13, 13, 13, 13, 13, // t0..message3_addr, compress_enabler (10 compress columns): 2^14
    14, 14, 14, 14, 14, 14, 14, 14, 14, 14, // seq_14
    14, // bitwise_xor_7_{0,1,2}: 2^(2*7) = 2^14
    14, 14, 14, // seq_15
    15, // seq_16, bitwise_xor_8_{0,1,2}: 2^(2*8)=2^16
    16, 16, 16, 16, // eq_in{0,1}_address
    17, 17, // bitwise_xor_9_{0,1,2}: 2^(2*9)=2^18
    18, 18, 18, // bitwise_xor_10_{0,1,2}: 2^(2*10)=2^20
    20, 20, 20, // qm31_ops_{add,sub,mul,pointwise_mul}_flag, in0/in1/out_address, mults
    21, 21, 21, 21, 21, 21, 21, 21,
];

pub const PRIVACY_CIRCUIT_PREPROCESSED_IDS: [&str; 79] = [
    "blake_sigma_0",
    "blake_sigma_1",
    "blake_sigma_2",
    "blake_sigma_3",
    "blake_sigma_4",
    "blake_sigma_5",
    "blake_sigma_6",
    "blake_sigma_7",
    "blake_sigma_8",
    "blake_sigma_9",
    "blake_sigma_10",
    "blake_sigma_11",
    "blake_sigma_12",
    "blake_sigma_13",
    "blake_sigma_14",
    "blake_sigma_15",
    "triple_xor_input_addr_0",
    "triple_xor_input_addr_1",
    "triple_xor_input_addr_2",
    "triple_xor_output_addr",
    "triple_xor_multiplicity",
    "m31_to_u32_input_addr",
    "m31_to_u32_output_addr",
    "m31_to_u32_multiplicity",
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
    "seq_4",
    "bitwise_xor_4_0",
    "bitwise_xor_4_1",
    "bitwise_xor_4_2",
    "final_state_addr",
    "blake_output0_addr",
    "blake_output1_addr",
    "blake_output0_mults",
    "blake_output1_mults",
    "t0",
    "t1",
    "finalize_flag",
    "state_before_addr",
    "state_after_addr",
    "message0_addr",
    "message1_addr",
    "message2_addr",
    "message3_addr",
    "compress_enabler",
    "seq_14",
    "bitwise_xor_7_0",
    "bitwise_xor_7_1",
    "bitwise_xor_7_2",
    "seq_15",
    "seq_16",
    "bitwise_xor_8_0",
    "bitwise_xor_8_1",
    "bitwise_xor_8_2",
    "eq_in0_address",
    "eq_in1_address",
    "bitwise_xor_9_0",
    "bitwise_xor_9_1",
    "bitwise_xor_9_2",
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
