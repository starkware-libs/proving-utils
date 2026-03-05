use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;

pub const NUM_OUTPUTS: usize = 1;

pub const PRIVACY_BOOTLOADER_PATH: &str = "../cairo-program-runner-lib/resources/compiled_programs/bootloaders/privacy_simple_bootloader_compiled.json";

pub const LIFTING_LOG_SIZE: u32 = 22;

pub const PCS_CONFIG: PcsConfig = PcsConfig {
    pow_bits: 22,
    fri_config: FriConfig {
        log_blowup_factor: LIFTING_LOG_SIZE - 20,
        log_last_layer_degree_bound: 0,
        n_queries: 35,
        line_fold_step: 1,
    },
    lifting_log_size: Some(LIFTING_LOG_SIZE),
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
