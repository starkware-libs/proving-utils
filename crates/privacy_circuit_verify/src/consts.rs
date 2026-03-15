use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;

pub const NUM_OUTPUTS: usize = 1;
pub const PRIVACY_BOOTLOADER_BYTES: &[u8] = include_bytes!(
    "../../cairo-program-runner-lib/resources/compiled_programs/bootloaders/privacy_simple_bootloader_compiled.json"
);
pub const CIRCUIT_OUTPUT_ADDRESSES: [usize; 4] = [340767, 340768, 2922740, 2922741];
pub const CIRCUIT_N_BLAKE_GATES: usize = 13450;
pub const PRIVACY_CAIRO_VERIFIER_CONSTS_HASH: [u32; 8] = [
    1283865202, 2009681603, 1266623912, 534797207, 1489758000, 741307218, 1414461714, 1643656987,
];
pub const PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT: [u32; 8] = [
    736666193, 671587538, 1100540541, 1401951855, 202000446, 1284259076, 1586213897, 825089717,
];
pub const CAIRO_LOG_BLOWUP_FACTOR: u32 = 2;
pub const CAIRO_TRACE_LOG_SIZE: u32 = 20;
pub const CIRCUIT_LOG_BLOWUP_FACTOR: u32 = 1;
pub const CIRCUIT_TRACE_LOG_SIZE: u32 = 22;

pub const CAIRO_FRI_CONFIG: FriConfig = FriConfig {
    log_blowup_factor: CAIRO_LOG_BLOWUP_FACTOR,
    log_last_layer_degree_bound: 0,
    n_queries: 35,
    line_fold_step: 1,
};

pub const CAIRO_PCS_CONFIG: PcsConfig = PcsConfig {
    pow_bits: 26,
    fri_config: CAIRO_FRI_CONFIG,
    lifting_log_size: Some(CAIRO_TRACE_LOG_SIZE + CAIRO_LOG_BLOWUP_FACTOR),
};

pub const CIRCUIT_FRI_CONFIG: FriConfig = FriConfig {
    log_blowup_factor: CIRCUIT_LOG_BLOWUP_FACTOR,
    log_last_layer_degree_bound: 0,
    n_queries: 70,
    line_fold_step: 1,
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

pub const PRIVACY_CIRCUIT_PREPROCESSED_IDS: [&str; 73] = [
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
    "seq_4",
    "seq_5",
    "seq_6",
    "seq_7",
    "seq_8",
    "bitwise_xor_4_0",
    "bitwise_xor_4_1",
    "bitwise_xor_4_2",
    "seq_9",
    "seq_10",
    "seq_11",
    "seq_12",
    "seq_13",
    "final_state_addr",
    "blake_output0_addr",
    "blake_output1_addr",
    "blake_output0_mults",
    "blake_output1_mults",
    "seq_14",
    "bitwise_xor_7_0",
    "bitwise_xor_7_1",
    "bitwise_xor_7_2",
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
    "seq_15",
    "seq_16",
    "bitwise_xor_8_0",
    "bitwise_xor_8_1",
    "bitwise_xor_8_2",
    "seq_17",
    "eq_in0_address",
    "eq_in1_address",
    "seq_18",
    "bitwise_xor_9_0",
    "bitwise_xor_9_1",
    "bitwise_xor_9_2",
    "seq_19",
    "seq_20",
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
