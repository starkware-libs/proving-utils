use std::any::Any;
use std::collections::HashMap;
use std::rc::Rc;

use cairo_vm::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::{
    BuiltinHintProcessor, HintFunc, HintProcessorData,
};
use cairo_vm::hint_processor::builtin_hint_processor::memcpy_hint_utils::exit_scope;
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
    allocate_program_data_segment, append_fact_topologies, bootloader_validate_hash, call_task,
    is_poseidon_to_ap, load_program_hint, validate_hash, write_return_builtins_hint,
};
use crate::hints::inner_select_builtins::select_builtin;
use crate::hints::select_builtins::select_builtins_enter_scope;
use crate::hints::simple_bootloader_hints::{
    divide_num_by_2, prepare_task_range_checks, set_ap_to_zero, set_current_task,
    set_tasks_variable,
};
use crate::hints::verifier_hints::load_and_parse_proof;

use super::applicative_bootloader_hints::{
    finalize_fact_topologies_and_pages, prepare_aggregator_simple_bootloader_output_segment,
    prepare_root_task_unpacker_bootloader_output_segment, restore_applicative_output_state,
};
use super::bootloader_hints::load_unpacker_bootloader_input;
use super::fri_layer::divide_queries_ind_by_coset_size_to_fp_offset;
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
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
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
            BOOTLOADER_IS_POSEIDON => is_poseidon_to_ap(vm, exec_scopes),
            BOOTLOADER_VALIDATE_HASH => bootloader_validate_hash(
                vm,
                exec_scopes,
                &hint_data.ids_data,
                &hint_data.ap_tracking,
            ),
            BOOTLOADER_ASSERT_IS_COMPOSITE_PACKED_OUTPUT => {
                assert_is_composite_packed_output(exec_scopes)
            }
            SIMPLE_BOOTLOADER_PREPARE_TASK_RANGE_CHECKS => {
                prepare_task_range_checks(vm, exec_scopes, ids_data, ap_tracking)
            }
            SIMPLE_BOOTLOADER_SET_TASKS_VARIABLE => set_tasks_variable(exec_scopes),
            SIMPLE_BOOTLOADER_DIVIDE_NUM_BY_2 => divide_num_by_2(vm, ids_data, ap_tracking),
            SIMPLE_BOOTLOADER_SET_CURRENT_TASK => {
                set_current_task(vm, exec_scopes, ids_data, ap_tracking)
            }
            SIMPLE_BOOTLOADER_ZERO => set_ap_to_zero(vm),
            EXECUTE_TASK_ALLOCATE_PROGRAM_DATA_SEGMENT => {
                allocate_program_data_segment(vm, exec_scopes, ids_data, ap_tracking)
            }
            EXECUTE_TASK_LOAD_PROGRAM => load_program_hint(vm, exec_scopes, ids_data, ap_tracking),
            EXECUTE_TASK_VALIDATE_HASH => validate_hash(vm, exec_scopes, ids_data, ap_tracking),
            EXECUTE_TASK_ASSERT_PROGRAM_ADDRESS => {
                assert_program_address(vm, exec_scopes, ids_data, ap_tracking)
            }
            EXECUTE_TASK_WRITE_RETURN_BUILTINS => {
                write_return_builtins_hint(vm, exec_scopes, ids_data, ap_tracking)
            }
            EXECUTE_TASK_EXIT_SCOPE => exit_scope(exec_scopes),
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
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
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
pub struct BootloaderHintProcessor {
    bootloader_hint_processor: MinimalBootloaderHintProcessor,
    builtin_hint_processor: BuiltinHintProcessor,
    test_programs_hint_processor: MinimalTestProgramsHintProcessor,
    pub additional_constants: HashMap<String, Felt252>,
    pub change_needed: bool,
}

impl Default for BootloaderHintProcessor {
    fn default() -> Self {
        Self::new()
    }
}

impl BootloaderHintProcessor {
    pub fn new() -> Self {
        Self {
            bootloader_hint_processor: MinimalBootloaderHintProcessor::new(),
            builtin_hint_processor: BuiltinHintProcessor::new_empty(),
            test_programs_hint_processor: MinimalTestProgramsHintProcessor::new(),
            additional_constants: HashMap::new(),
            change_needed: false,
        }
    }

    pub fn add_hint(&mut self, hint_code: String, hint_func: Rc<HintFunc>) {
        self.builtin_hint_processor
            .extra_hints
            .insert(hint_code, hint_func);
    }
}

impl HintProcessorLogic for BootloaderHintProcessor {
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
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
        let mut curr_consts = constants;
        if !self.additional_constants.is_empty() {
            if self.change_needed {
                for (key, value) in constants {
                    self.additional_constants.insert(key.clone(), *value);
                }
                self.change_needed = false;
            }
            curr_consts = &self.additional_constants;
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
        if hint_data_dc.code.as_str() == EXECUTE_TASK_CALL_TASK {
            return call_task(
                self,
                vm,
                exec_scopes,
                &hint_data_dc.ids_data,
                &hint_data_dc.ap_tracking,
            );
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

impl ResourceTracker for BootloaderHintProcessor {}
