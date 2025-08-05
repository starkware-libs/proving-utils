use std::any::Any;
use std::collections::HashMap;
use std::rc::Rc;

use cairo_lang_runner::CairoHintProcessor;
use cairo_vm::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::{
    BuiltinHintProcessor, HintFunc, HintProcessorData,
};
use cairo_vm::hint_processor::hint_processor_definition::{HintExtension, HintProcessorLogic};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::runners::cairo_runner::ResourceTracker;
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::Felt252;
use starknet_types_core::felt::Felt;

use crate::hints::bootloader_hints::{
    assert_is_composite_packed_output, assert_program_address,
    compute_and_configure_fact_topologies, compute_and_configure_fact_topologies_simple,
    enter_packed_output_scope, guess_pre_image_of_subtasks_output_hash,
    import_packed_output_schemas, is_plain_packed_output, load_bootloader_config,
    load_simple_bootloader_input, prepare_simple_bootloader_input,
    prepare_simple_bootloader_output_segment, restore_bootloader_output, save_output_pointer,
    save_packed_outputs, set_packed_output_to_subtasks,
};
use crate::hints::codes::*;
use crate::hints::execute_task_hints::{
    append_fact_topologies, bootloader_validate_hash, determine_use_prev_hash,
    execute_task_exit_scope, load_program_hint, setup_subtask_for_execution, validate_hash,
    write_return_builtins_hint,
};
use crate::hints::inner_select_builtins::select_builtin;
use crate::hints::select_builtins::select_builtins_enter_scope;
use crate::hints::simple_bootloader_hints::{
    divide_num_by_2, program_hash_function_to_ap, set_ap_to_zero, set_current_task,
    set_tasks_variable, setup_run_simple_bootloader_before_task_execution,
};
use crate::hints::utils::output_builtin_set_pages_by_size_and_fact_topology;
use crate::hints::verifier_hints::load_and_parse_proof;

use super::applicative_bootloader_hints::{
    finalize_fact_topologies_and_pages, prepare_aggregator_simple_bootloader_output_segment,
    prepare_root_task_unpacker_bootloader_output_segment, restore_applicative_output_state,
};
use super::bootloader_hints::load_unpacker_bootloader_input;
use super::builtin_usage_hints::{
    builtin_usage_5_to_ap, builtin_usage_add_other_segment, builtin_usage_add_signature,
    builtin_usage_set_pages_and_fact_topology, flexible_builtin_usage_from_input,
};
use super::concat_aggregator_hints::{
    concat_aggregator_get_handle_task_output, concat_aggregator_parse_task,
};
use super::fibonacci_hints::{fibonacci_load_claim_idx, fibonacci_load_second_element};
use super::fri_layer::divide_queries_ind_by_coset_size_to_fp_offset;
use super::mock_cairo_verifier_hints::{
    load_mock_cairo_verifier_input, mock_cairo_verifier_hash_to_fp,
    mock_cairo_verifier_len_output_to_fp, mock_cairo_verifier_n_steps_to_ap,
};
use super::pedersen_merkle_hints::{
    pedersen_merkle_idx_parity_to_ap, pedersen_merkle_load_input, pedersen_merkle_update,
    pedersen_merkle_verify_auth_path_len,
};
use super::simple_bootloader_hints::{
    simple_bootloader_simulate_ec_op, simple_bootloader_simulate_ecdsa,
    simple_bootloader_simulate_keccak, simulate_ec_op_assert_false,
    simulate_ec_op_fill_mem_with_bits_of_m, simulate_ecdsa_compute_w_wr_wz,
    simulate_ecdsa_fill_mem_with_felt_96_bit_limbs, simulate_ecdsa_get_r_and_s,
    simulate_keccak_calc_high_low, simulate_keccak_fill_mem_with_state,
};
use super::simple_output_hints::{len_output_to_ap, load_simple_output_input, write_simple_output};
use super::vector_commitment::set_bit_from_index;

/// A hint processor that can only execute the hints defined in this library.
/// For large projects, you may want to compose a hint processor from multiple parts
/// (ex: Starknet OS, bootloader and Cairo VM). This hint processor is as minimal as possible
/// to enable this modularity.
///
/// However, this processor is not sufficient to execute the bootloader. For this,
/// use `StandaloneBootloaderHintProcessor`.
#[derive(Default)]
pub struct MinimalBootloaderHintProcessor;

impl MinimalBootloaderHintProcessor {
    pub fn new() -> Self {
        Self {}
    }
}

impl HintProcessorLogic for MinimalBootloaderHintProcessor {
    fn execute_hint(
        &mut self,
        vm: &mut VirtualMachine,
        exec_scopes: &mut ExecutionScopes,
        hint_data: &Box<dyn Any>,
        constants: &HashMap<String, Felt252>,
    ) -> Result<(), HintError> {
        let hint_data = hint_data
            .downcast_ref::<HintProcessorData>()
            .ok_or(HintError::WrongHintData)?;

        let ids_data = &hint_data.ids_data;
        let ap_tracking = &hint_data.ap_tracking;

        match hint_data.code.as_str() {
            BOOTLOADER_RESTORE_BOOTLOADER_OUTPUT => restore_bootloader_output(vm, exec_scopes),
            BOOTLOADER_PREPARE_SIMPLE_BOOTLOADER_INPUT => {
                prepare_simple_bootloader_input(exec_scopes)
            }
            BOOTLOADER_READ_SIMPLE_BOOTLOADER_INPUT => load_simple_bootloader_input(exec_scopes),
            BOOTLOADER_READ_UNPACKER_BOOTLOADER_INPUT => {
                load_unpacker_bootloader_input(exec_scopes)
            }
            BOOTLOADER_LOAD_BOOTLOADER_CONFIG => {
                load_bootloader_config(vm, exec_scopes, ids_data, ap_tracking)
            }
            BOOTLOADER_ENTER_PACKED_OUTPUT_SCOPE => {
                enter_packed_output_scope(vm, exec_scopes, ids_data, ap_tracking)
            }
            BOOTLOADER_SAVE_OUTPUT_POINTER => {
                save_output_pointer(vm, exec_scopes, ids_data, ap_tracking)
            }
            BOOTLOADER_SAVE_PACKED_OUTPUTS => save_packed_outputs(exec_scopes),
            BOOTLOADER_GUESS_PRE_IMAGE_OF_SUBTASKS_OUTPUT_HASH => {
                guess_pre_image_of_subtasks_output_hash(vm, exec_scopes, ids_data, ap_tracking)
            }
            BOOTLOADER_PREPARE_SIMPLE_BOOTLOADER_OUTPUT_SEGMENT => {
                prepare_simple_bootloader_output_segment(vm, exec_scopes, ids_data, ap_tracking)
            }
            BOOTLOADER_COMPUTE_FACT_TOPOLOGIES => {
                compute_and_configure_fact_topologies(vm, exec_scopes)
            }
            BOOTLOADER_SIMPLE_BOOTLOADER_COMPUTE_FACT_TOPOLOGIES => {
                compute_and_configure_fact_topologies_simple(vm, exec_scopes)
            }
            BOOTLOADER_SET_PACKED_OUTPUT_TO_SUBTASKS => set_packed_output_to_subtasks(exec_scopes),
            BOOTLOADER_IMPORT_PACKED_OUTPUT_SCHEMAS => import_packed_output_schemas(),
            BOOTLOADER_IS_PLAIN_PACKED_OUTPUT => is_plain_packed_output(vm, exec_scopes),
            BOOTLOADER_PROGRAM_HASH => program_hash_function_to_ap(vm, exec_scopes),
            BOOTLOADER_VALIDATE_HASH => bootloader_validate_hash(
                vm,
                exec_scopes,
                &hint_data.ids_data,
                &hint_data.ap_tracking,
            ),
            BOOTLOADER_ASSERT_IS_COMPOSITE_PACKED_OUTPUT => {
                assert_is_composite_packed_output(exec_scopes)
            }
            SETUP_RUN_SIMPLE_BOOTLOADER_BEFORE_TASK_EXECUTION => {
                setup_run_simple_bootloader_before_task_execution(
                    vm,
                    exec_scopes,
                    ids_data,
                    ap_tracking,
                )
            }
            SIMPLE_BOOTLOADER_SET_TASKS_VARIABLE => set_tasks_variable(exec_scopes),
            SIMPLE_BOOTLOADER_DIVIDE_NUM_BY_2 => divide_num_by_2(vm, ids_data, ap_tracking),
            SIMPLE_BOOTLOADER_SET_CURRENT_TASK => {
                set_current_task(vm, exec_scopes, ids_data, ap_tracking)
            }
            DETERMINE_USE_PREV_HASH => {
                determine_use_prev_hash(vm, exec_scopes, ids_data, ap_tracking)
            }
            SIMPLE_BOOTLOADER_ZERO => set_ap_to_zero(vm),
            LOAD_PROGRAM_SEGMENT => load_program_hint(vm, exec_scopes, ids_data, ap_tracking),
            EXECUTE_TASK_VALIDATE_HASH => validate_hash(vm, exec_scopes, ids_data, ap_tracking),
            EXECUTE_TASK_ASSERT_PROGRAM_ADDRESS => {
                assert_program_address(vm, exec_scopes, ids_data, ap_tracking)
            }
            EXECUTE_TASK_WRITE_RETURN_BUILTINS => {
                write_return_builtins_hint(vm, exec_scopes, ids_data, ap_tracking)
            }
            EXECUTE_TASK_APPEND_FACT_TOPOLOGIES => {
                append_fact_topologies(vm, exec_scopes, ids_data, ap_tracking)
            }
            SELECT_BUILTINS_ENTER_SCOPE => {
                select_builtins_enter_scope(vm, exec_scopes, ids_data, ap_tracking)
            }
            INNER_SELECT_BUILTINS_SELECT_BUILTIN => {
                select_builtin(vm, exec_scopes, ids_data, ap_tracking)
            }
            VERIFIER_LOAD_AND_PARSE_PROOF => {
                load_and_parse_proof(vm, exec_scopes, ids_data, ap_tracking)
            }
            VERIFIER_GET_INDEX_LAST_BIT => set_bit_from_index(vm, ids_data, ap_tracking),
            VERIFIER_DIVIDE_QUERIES_IND_BY_COSET_SIZE_TO_FP_OFFSET => {
                divide_queries_ind_by_coset_size_to_fp_offset(vm, ids_data, ap_tracking)
            }
            APPLICATIVE_LOAD_INPUTS => prepare_aggregator_simple_bootloader_output_segment(
                vm,
                exec_scopes,
                ids_data,
                ap_tracking,
            ),
            APPLICATIVE_SET_UP_UNPACKER_INPUTS => {
                prepare_root_task_unpacker_bootloader_output_segment(
                    vm,
                    exec_scopes,
                    ids_data,
                    ap_tracking,
                )
            }
            APPLICATIVE_RESTORE_OUTPUT_BUILTIN_STATE => {
                restore_applicative_output_state(vm, exec_scopes)
            }
            APPLICATIVE_FINALIZE_FACT_TOPOLOGIES_AND_PAGES => {
                finalize_fact_topologies_and_pages(vm, exec_scopes, ids_data, ap_tracking)
            }
            SIMPLE_BOOTLOADER_SIMULATE_EC_OP => {
                simple_bootloader_simulate_ec_op(vm, ids_data, ap_tracking)
            }
            SIMULATE_EC_OP_FILL_MEM_WITH_BITS_OF_M => {
                simulate_ec_op_fill_mem_with_bits_of_m(vm, ids_data, ap_tracking, constants)
            }
            SIMULATE_EC_OP_ASSERT_FALSE => simulate_ec_op_assert_false(),
            SIMPLE_BOOTLOADER_SIMULATE_KECCAK => {
                simple_bootloader_simulate_keccak(vm, ids_data, ap_tracking)
            }
            SIMULATE_KECCAK_FILL_MEM_WITH_STATE => {
                simulate_keccak_fill_mem_with_state(vm, ids_data, ap_tracking)
            }
            SIMULATE_KECCAK_CALC_HIGH3_LOW3 => {
                simulate_keccak_calc_high_low(vm, ids_data, ap_tracking, 3)
            }
            SIMULATE_KECCAK_CALC_HIGH6_LOW6 => {
                simulate_keccak_calc_high_low(vm, ids_data, ap_tracking, 6)
            }
            SIMULATE_KECCAK_CALC_HIGH9_LOW9 => {
                simulate_keccak_calc_high_low(vm, ids_data, ap_tracking, 9)
            }
            SIMULATE_KECCAK_CALC_HIGH12_LOW12 => {
                simulate_keccak_calc_high_low(vm, ids_data, ap_tracking, 12)
            }
            SIMULATE_KECCAK_CALC_HIGH15_LOW15 => {
                simulate_keccak_calc_high_low(vm, ids_data, ap_tracking, 15)
            }
            SIMULATE_KECCAK_CALC_HIGH18_LOW18 => {
                simulate_keccak_calc_high_low(vm, ids_data, ap_tracking, 18)
            }
            SIMULATE_KECCAK_CALC_HIGH21_LOW21 => {
                simulate_keccak_calc_high_low(vm, ids_data, ap_tracking, 21)
            }
            SIMPLE_BOOTLOADER_SIMULATE_ECDSA => {
                simple_bootloader_simulate_ecdsa(vm, ids_data, ap_tracking)
            }
            SIMULATE_ECDSA_GET_R_AND_S => simulate_ecdsa_get_r_and_s(vm, ids_data, ap_tracking),
            SIMULATE_ECDSA_COMPUTE_W_WR_WZ => {
                simulate_ecdsa_compute_w_wr_wz(vm, ids_data, ap_tracking, constants)
            }
            SIMULATE_ECDSA_FILL_MEM_WITH_FELT_96_BIT_LIMBS => {
                simulate_ecdsa_fill_mem_with_felt_96_bit_limbs(vm, ids_data, ap_tracking)
            }
            unknown_hint_code => Err(HintError::UnknownHint(
                unknown_hint_code.to_string().into_boxed_str(),
            )),
        }
    }
}

impl ResourceTracker for MinimalBootloaderHintProcessor {}

#[derive(Default)]
pub struct MinimalTestProgramsHintProcessor;

impl MinimalTestProgramsHintProcessor {
    pub fn new() -> Self {
        Self {}
    }
}

impl HintProcessorLogic for MinimalTestProgramsHintProcessor {
    fn execute_hint(
        &mut self,
        vm: &mut VirtualMachine,
        exec_scopes: &mut ExecutionScopes,
        hint_data: &Box<dyn Any>,
        _constants: &HashMap<String, Felt252>,
    ) -> Result<(), HintError> {
        let hint_data = hint_data
            .downcast_ref::<HintProcessorData>()
            .ok_or(HintError::WrongHintData)?;

        let ids_data = &hint_data.ids_data;
        let ap_tracking = &hint_data.ap_tracking;

        match hint_data.code.as_str() {
            SIMPLE_OUTPUT_LOAD_PROGRAM_INPUT => load_simple_output_input(exec_scopes),
            SIMPLE_OUTPUT_WRITE_OUTPUT => {
                write_simple_output(vm, exec_scopes, ids_data, ap_tracking)
            }
            SIMPLE_OUTPUT_LEN_OUTPUT_TO_AP => len_output_to_ap(vm, exec_scopes),
            MOCK_CAIRO_VERIFIER_LOAD_INPUT => {
                load_mock_cairo_verifier_input(vm, exec_scopes, ids_data, ap_tracking)
            }
            MOCK_CAIRO_VERIFIER_OUTPUT_LEN_TO_FP => {
                mock_cairo_verifier_len_output_to_fp(vm, exec_scopes)
            }
            MOCK_CAIRO_VERIFIER_HASH_TO_FP => mock_cairo_verifier_hash_to_fp(vm, exec_scopes),
            MOCK_CAIRO_VERIFIER_GET_N_STEPS => Ok(()),
            MOCK_CAIRO_VERIFIER_N_STEPS_TO_AP => mock_cairo_verifier_n_steps_to_ap(vm, exec_scopes),
            CONCAT_AGGREGATOR_PARSE_TASKS_OUTPUTS => {
                concat_aggregator_parse_task(vm, exec_scopes, ids_data, ap_tracking)
            }
            CONCAT_AGGREGATOR_GET_TASK_OUTPUT_WITH_SIZE => {
                concat_aggregator_get_handle_task_output(vm, exec_scopes, ids_data, ap_tracking, 1)
            }
            CONCAT_AGGREGATOR_GET_TASK_OUTPUT_WITHOUT_SIZE => {
                concat_aggregator_get_handle_task_output(vm, exec_scopes, ids_data, ap_tracking, 0)
            }
            CONCAT_AGGREGATOR_SET_PAGES_AND_FACT_TOPOLOGY => {
                output_builtin_set_pages_by_size_and_fact_topology(vm, ids_data, ap_tracking, 10)
            }
            BUILTIN_USAGE_SET_MAX_SIZE_PAGES_AND_FACT_TOPOLOGY => {
                output_builtin_set_pages_by_size_and_fact_topology(vm, ids_data, ap_tracking, 3800)
            }
            BUILTIN_USAGE_ADD_OTHER_SEGMENT => {
                builtin_usage_add_other_segment(vm, ids_data, ap_tracking, true)
            }
            BUILTIN_USAGE_ADD_OTHER_SEGMENT_FINALIZE => {
                builtin_usage_add_other_segment(vm, ids_data, ap_tracking, true)
            }
            BUILTIN_USAGE_ADD_SIGNATURE
            | BUILTIN_USAGE_ADD_SIGNATURE_FROM_SIGNATURE_BUILTIN_STRUCT => {
                builtin_usage_add_signature(vm, ids_data, ap_tracking)
            }
            BUILTIN_USAGE_5_TO_AP => builtin_usage_5_to_ap(vm),
            BUILTIN_USAGE_SET_PAGES_AND_FACT_TOPOLOGY => {
                builtin_usage_set_pages_and_fact_topology(vm, ids_data, ap_tracking)
            }
            FLEXIBLE_BUILTIN_USAGE_FROM_INPUT => {
                flexible_builtin_usage_from_input(vm, exec_scopes, ids_data, ap_tracking)
            }
            FIBONACCI_LOAD_SECOND_ELEMENT => fibonacci_load_second_element(vm, exec_scopes),
            FIBONACCI_LOAD_CLAIM_IDX => fibonacci_load_claim_idx(vm, exec_scopes),
            PEDERSEN_MERKLE_VERIFY_AUTH_PATH_LEN => {
                pedersen_merkle_verify_auth_path_len(exec_scopes)
            }
            PEDERSEN_MERKLE_LOAD_INPUT => {
                pedersen_merkle_load_input(vm, exec_scopes, ids_data, ap_tracking)
            }
            PEDERSEN_MERKLE_IDX_PARITY_TO_AP => {
                pedersen_merkle_idx_parity_to_ap(vm, ids_data, ap_tracking)
            }
            PEDERSEN_MERKLE_UPDATE_LEFT => {
                pedersen_merkle_update(vm, exec_scopes, ids_data, ap_tracking, true)
            }
            PEDERSEN_MERKLE_UPDATE_RIGHT => {
                pedersen_merkle_update(vm, exec_scopes, ids_data, ap_tracking, false)
            }
            unknown_hint_code => Err(HintError::UnknownHint(
                unknown_hint_code.to_string().into_boxed_str(),
            )),
        }
    }
}

/// A hint processor for use cases where we only care about the bootloader hints.
///
/// When executing a hint, this hint processor will first check the hints defined in this library,
/// then the ones defined in Cairo VM.
pub struct BootloaderHintProcessor<'a> {
    bootloader_hint_processor: MinimalBootloaderHintProcessor,
    builtin_hint_processor: BuiltinHintProcessor,
    test_programs_hint_processor: MinimalTestProgramsHintProcessor,
    pub subtask_cairo1_hint_processor_stack: Vec<Option<CairoHintProcessor<'a>>>,
    pub subtask_cairo0_constants_stack: Vec<Option<HashMap<String, Felt252>>>,
}

impl Default for BootloaderHintProcessor<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> BootloaderHintProcessor<'a> {
    pub fn new() -> Self {
        Self {
            bootloader_hint_processor: MinimalBootloaderHintProcessor::new(),
            builtin_hint_processor: BuiltinHintProcessor::new_empty(),
            subtask_cairo1_hint_processor_stack: Vec::new(),
            test_programs_hint_processor: MinimalTestProgramsHintProcessor::new(),
            subtask_cairo0_constants_stack: Vec::new(),
        }
    }

    pub fn add_hint(&mut self, hint_code: String, hint_func: Rc<HintFunc>) {
        self.builtin_hint_processor
            .extra_hints
            .insert(hint_code, hint_func);
    }

    /// Push new subtask state onto the stacks.
    /// Pass an optional constants map and an optional Cairo hint processor.
    pub fn spawn_subtask(
        &mut self,
        constants: Option<HashMap<String, Felt252>>,
        cairo_hint_processor: Option<CairoHintProcessor<'a>>,
    ) {
        self.subtask_cairo0_constants_stack.push(constants);
        self.subtask_cairo1_hint_processor_stack
            .push(cairo_hint_processor);
    }

    /// Pop the current subtask state off the stacks.
    pub fn despawn_subtask(&mut self) {
        self.subtask_cairo0_constants_stack.pop();
        self.subtask_cairo1_hint_processor_stack.pop();
    }
}

impl HintProcessorLogic for BootloaderHintProcessor<'_> {
    fn execute_hint(
        &mut self,
        _vm: &mut VirtualMachine,
        _exec_scopes: &mut ExecutionScopes,
        hint_data: &Box<dyn Any>,
        _constants: &HashMap<String, Felt>,
    ) -> Result<(), HintError> {
        // This method will never be called, but must be defined for `HintProcessorLogic`.

        let hint_data = hint_data.downcast_ref::<HintProcessorData>().unwrap();
        let hint_code = &hint_data.code;
        Err(HintError::UnknownHint(hint_code.clone().into_boxed_str()))
    }

    fn execute_hint_extensive(
        &mut self,
        vm: &mut VirtualMachine,
        exec_scopes: &mut ExecutionScopes,
        hint_data: &Box<dyn Any>,
        constants: &HashMap<String, Felt>,
    ) -> Result<HintExtension, HintError> {
        // Cascade through the internal hint processors until we find the hint implementation.
        let curr_consts = if self.subtask_cairo0_constants_stack.is_empty() {
            constants
        } else {
            self.subtask_cairo0_constants_stack
                .last()
                .and_then(|opt| opt.as_ref())
                .unwrap_or(constants)
        };

        // In case the subtask_cairo_hint_processor is a Some variant, we try matching the hint
        // using it first, for efficiency, since it is assumed to only be Some if we're inside
        // an execution of a cairo1 program subtask.
        if let Some(Some(subtask_cairo_hint_processor)) =
            self.subtask_cairo1_hint_processor_stack.last_mut()
        {
            match subtask_cairo_hint_processor.execute_hint_extensive(
                vm,
                exec_scopes,
                hint_data,
                curr_consts,
            ) {
                Err(HintError::UnknownHint(_)) | Err(HintError::WrongHintData) => {}
                result => {
                    return result;
                }
            }
        }

        match self.bootloader_hint_processor.execute_hint_extensive(
            vm,
            exec_scopes,
            hint_data,
            curr_consts,
        ) {
            Err(HintError::UnknownHint(_)) => {}
            result => {
                return result;
            }
        }

        let hint_data_dc = hint_data
            .downcast_ref::<HintProcessorData>()
            .ok_or(HintError::WrongHintData)?;
        match hint_data_dc.code.as_str() {
            EXECUTE_TASK_CALL_TASK => {
                return setup_subtask_for_execution(
                    self,
                    vm,
                    exec_scopes,
                    &hint_data_dc.ids_data,
                    &hint_data_dc.ap_tracking,
                )
            }
            EXECUTE_TASK_EXIT_SCOPE => return execute_task_exit_scope(self, exec_scopes),
            _ => {}
        }

        match self.builtin_hint_processor.execute_hint_extensive(
            vm,
            exec_scopes,
            hint_data,
            curr_consts,
        ) {
            Err(HintError::UnknownHint(_)) => {}
            result => {
                return result;
            }
        }

        self.test_programs_hint_processor.execute_hint_extensive(
            vm,
            exec_scopes,
            hint_data,
            curr_consts,
        )
    }
}

impl ResourceTracker for BootloaderHintProcessor<'_> {}
