use std::any::Any;
use std::collections::HashMap;
use std::vec;

use cairo_lang_runner::{Arg, CairoHintProcessor};
use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::{
    get_ptr_from_var_name, get_relocatable_from_var_name, insert_value_from_var_name,
};
use cairo_vm::hint_processor::builtin_hint_processor::memcpy_hint_utils::exit_scope;
use cairo_vm::hint_processor::hint_processor_definition::{
    HintExtension, HintProcessorLogic, HintReference,
};
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::builtin_name::BuiltinName;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::program::Program;
use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::errors::memory_errors::MemoryError;
use cairo_vm::vm::runners::builtin_runner::{OutputBuiltinRunner, OutputBuiltinState};
use cairo_vm::vm::runners::cairo_pie::CairoPie;
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::{any_box, Felt252};
use starknet_crypto::FieldElement;

use super::types::HashFunc;
use super::utils::{get_identifier, get_program_from_task, get_program_identifies};
use super::{BootloaderHintProcessor, PROGRAM_INPUT, PROGRAM_OBJECT};
use crate::hints::fact_topologies::{get_task_fact_topology, FactTopology};
use crate::hints::load_cairo_pie::load_cairo_pie;
use crate::hints::program_hash::compute_program_hash_chain;
use crate::hints::program_loader::ProgramLoader;
use crate::hints::types::{BootloaderVersion, Task};
use crate::hints::vars;

pub fn field_element_to_felt(field_element: FieldElement) -> Felt252 {
    let bytes = field_element.to_bytes_be();
    Felt252::from_bytes_be(&bytes)
}

/// Determines if the program of the new task is the same as the previous one.
/// Stores use_prev_hash to fp.
pub fn determine_use_prev_hash(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let use_prev_hash: i32 = exec_scopes.get(vars::USE_PREV_HASH)?;
    insert_value_from_var_name(
        "use_prev_hash",
        use_prev_hash as usize,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

/// Implements
///
/// from starkware.cairo.bootloaders.simple_bootloader.utils import load_program
///
/// # Call load_program to load the program header and code to memory.
/// program_address, program_data_size = load_program(
///     task=task, memory=memory, program_header=ids.program_header,
///     builtins_offset=ids.ProgramHeader.builtin_list)
/// segments.finalize(program_data_base.segment_index, program_data_size)
pub fn load_program_hint(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_data_base = vm.add_memory_segment();
    insert_value_from_var_name(
        "program_segment_ptr",
        program_data_base,
        vm,
        ids_data,
        ap_tracking,
    )?;

    let task: Task = exec_scopes.get(vars::TASK)?;
    let program = get_program_from_task(&task)?;

    let program_header_ptr = get_ptr_from_var_name("program_header", vm, ids_data, ap_tracking)?;

    // Offset of the builtin_list field in `ProgramHeader`, cf. execute_task.cairo
    let builtins_offset = 4;
    let mut program_loader = ProgramLoader::new(vm, builtins_offset);
    let bootloader_version: BootloaderVersion = 0;
    let loaded_program = program_loader
        .load_program(program_header_ptr, &program, Some(bootloader_version))
        .map_err(Into::<HintError>::into)?;

    vm.segments.finalize(
        Some(loaded_program.size),
        program_data_base.segment_index as usize,
        None,
    );

    exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_data_base);
    exec_scopes.insert_value(vars::PROGRAM_ADDRESS, loaded_program.code_address);

    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.simple_bootloader.utils import get_task_fact_topology
///
/// # Add the fact topology of the current task to 'fact_topologies'.
/// output_start = ids.pre_execution_builtin_ptrs.output
/// output_end = ids.return_builtin_ptrs.output
/// fact_topologies.append(get_task_fact_topology(
///     output_size=output_end - output_start,
///     task=task,
///     output_builtin=output_builtin,
///     output_runner_data=output_runner_data,
/// ))
pub fn append_fact_topologies(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;
    let output_runner_data: Option<OutputBuiltinState> =
        exec_scopes.get(vars::OUTPUT_RUNNER_DATA)?;
    let fact_topologies: &mut Vec<FactTopology> = exec_scopes.get_mut_ref(vars::FACT_TOPOLOGIES)?;

    let pre_execution_builtin_ptrs_addr =
        get_relocatable_from_var_name("pre_execution_builtin_ptrs", vm, ids_data, ap_tracking)?;
    let return_builtin_ptrs_addr =
        get_relocatable_from_var_name("return_builtin_ptrs", vm, ids_data, ap_tracking)?;

    // The output field is the first one in the BuiltinData struct
    let output_start = vm.get_relocatable(pre_execution_builtin_ptrs_addr)?;
    let output_end = vm.get_relocatable(return_builtin_ptrs_addr)?;
    let output_size = (output_end - output_start)?;

    let output_builtin = vm.get_output_builtin_mut()?;
    let fact_topology =
        get_task_fact_topology(output_size, &task, output_builtin, output_runner_data)
            .map_err(Into::<HintError>::into)?;
    fact_topologies.push(fact_topology);

    Ok(())
}

// TODO(idanh): can't find this hint anywhere in the starkware main repo, consider removing it.
/// Implements
/// # Validate hash.
/// from starkware.cairo.bootloaders.hash_program import compute_program_hash_chain
///
/// assert memory[ids.output_ptr + 1] == compute_program_hash_chain(task.get_program()), \
///   'Computed hash does not match input.'";
pub fn validate_hash(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;
    let program = get_program_from_task(&task)?;

    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    let program_hash_ptr = (output_ptr + 1)?;

    let program_hash = vm.get_integer(program_hash_ptr)?.into_owned();

    // Compute the hash of the program
    let computed_program_hash = compute_program_hash_chain(&program, 0, HashFunc::Pedersen)
        .map_err(|e| {
            HintError::CustomHint(format!("Could not compute program hash: {e}").into_boxed_str())
        })?;
    let computed_program_hash = field_element_to_felt(computed_program_hash);

    if program_hash != computed_program_hash {
        return Err(HintError::AssertionFailed(
            "Computed hash does not match input"
                .to_string()
                .into_boxed_str(),
        ));
    }

    Ok(())
}

/// List of all builtins in the order used by the bootloader.
pub const ALL_BUILTINS: [BuiltinName; 11] = [
    BuiltinName::output,
    BuiltinName::pedersen,
    BuiltinName::range_check,
    BuiltinName::ecdsa,
    BuiltinName::bitwise,
    BuiltinName::ec_op,
    BuiltinName::keccak,
    BuiltinName::poseidon,
    BuiltinName::range_check96,
    BuiltinName::add_mod,
    BuiltinName::mul_mod,
];

// TODO(idanh): This function seems to be unused, consider removing it.
fn check_cairo_pie_builtin_usage(
    vm: &mut VirtualMachine,
    builtin_name: &BuiltinName,
    builtin_index: usize,
    cairo_pie: &CairoPie,
    return_builtins_addr: Relocatable,
    pre_execution_builtins_addr: Relocatable,
) -> Result<(), HintError> {
    let return_builtin_value = vm.get_relocatable((return_builtins_addr + builtin_index)?)?;
    let pre_execution_builtin_value =
        vm.get_relocatable((pre_execution_builtins_addr + builtin_index)?)?;
    let expected_builtin_size = (return_builtin_value - pre_execution_builtin_value)?;

    let builtin_size = cairo_pie.metadata.builtin_segments[builtin_name].size;

    if builtin_size != expected_builtin_size {
        return Err(HintError::AssertionFailed(
            "Builtin usage is inconsistent with the CairoPie."
                .to_string()
                .into_boxed_str(),
        ));
    }

    Ok(())
}

/// Writes the updated builtin pointers after the program execution to the given return builtins
/// address.
///
/// `used_builtins` is the list of builtins used by the program and thus updated by it.
fn write_return_builtins(
    vm: &mut VirtualMachine,
    return_builtins_addr: Relocatable,
    used_builtins: &[BuiltinName],
    used_builtins_addr: Relocatable,
    pre_execution_builtins_addr: Relocatable,
    task: &Task,
) -> Result<(), HintError> {
    let mut used_builtin_offset: usize = 0;
    for (index, builtin) in ALL_BUILTINS.iter().enumerate() {
        if used_builtins.contains(builtin) {
            let builtin_addr = (used_builtins_addr + used_builtin_offset)?;
            let builtin_value = vm
                .get_maybe(&builtin_addr)
                .ok_or_else(|| MemoryError::UnknownMemoryCell(Box::new(builtin_addr)))?;
            vm.insert_value((return_builtins_addr + index)?, builtin_value.clone())?;
            used_builtin_offset += 1;

            if let MaybeRelocatable::Int(_) = builtin_value {
                continue;
            }

            if let Task::Pie(cairo_pie) = task {
                check_cairo_pie_builtin_usage(
                    vm,
                    builtin,
                    index,
                    cairo_pie,
                    return_builtins_addr,
                    pre_execution_builtins_addr,
                )?;
            }
        }
        // The builtin is unused, hence its value is the same as before calling the program.
        else {
            let pre_execution_builtin_addr = (pre_execution_builtins_addr + index)?;
            let pre_execution_value =
                vm.get_maybe(&pre_execution_builtin_addr).ok_or_else(|| {
                    MemoryError::UnknownMemoryCell(Box::new(pre_execution_builtin_addr))
                })?;
            vm.insert_value((return_builtins_addr + index)?, pre_execution_value)?;
        }
    }
    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.simple_bootloader.utils import write_return_builtins
///
/// # Fill the values of all builtin pointers after executing the task.
/// builtins = task.get_program().builtins
/// write_return_builtins(
///     memory=memory, return_builtins_addr=ids.return_builtin_ptrs.address_,
///     used_builtins=builtins, used_builtins_addr=ids.used_builtins_addr,
///     pre_execution_builtins_addr=ids.pre_execution_builtin_ptrs.address_, task=task)
///
/// vm_enter_scope({'n_selected_builtins': n_builtins})
///
/// This hint looks at the builtins written by the program and merges them with the stored
/// pre-execution values (stored in a struct named ids.pre_execution_builtin_ptrs) to
/// create a final BuiltinData struct for the program.
pub fn write_return_builtins_hint(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;
    let n_builtins: usize = exec_scopes.get(vars::N_BUILTINS)?;

    // builtins = task.get_program().builtins
    let program = get_program_from_task(&task)?;
    let builtins = &program.builtins;

    // write_return_builtins(
    //     memory=memory, return_builtins_addr=ids.return_builtin_ptrs.address_,
    //     used_builtins=builtins, used_builtins_addr=ids.used_builtins_addr,
    //     pre_execution_builtins_addr=ids.pre_execution_builtin_ptrs.address_, task=task)
    let return_builtins_addr =
        get_relocatable_from_var_name("return_builtin_ptrs", vm, ids_data, ap_tracking)?;
    let used_builtins_addr =
        get_ptr_from_var_name("used_builtins_addr", vm, ids_data, ap_tracking)?;
    let pre_execution_builtins_addr =
        get_relocatable_from_var_name("pre_execution_builtin_ptrs", vm, ids_data, ap_tracking)?;

    write_return_builtins(
        vm,
        return_builtins_addr,
        builtins,
        used_builtins_addr,
        pre_execution_builtins_addr,
        &task,
    )?;

    // vm_enter_scope({'n_selected_builtins': n_builtins})
    let n_builtins: Box<dyn Any> = Box::new(n_builtins);
    exec_scopes.enter_scope(HashMap::from([(
        vars::N_SELECTED_BUILTINS.to_string(),
        n_builtins,
    )]));

    Ok(())
}

/// Common function for processing a program: it inserts the program into task locals,
/// iterates over its hints ranges and compiles each hint using the provided processor,
/// while adjusting the hint's PC to the subtask's program address.
fn process_program_common_logic(
    program: &Program,
    new_task_locals: &mut HashMap<String, Box<dyn std::any::Any>>,
    exec_scopes: &ExecutionScopes,
    hint_compiler: &dyn HintProcessorLogic,
    hint_extension: &mut HintExtension,
) -> Result<(), HintError> {
    new_task_locals.insert(PROGRAM_OBJECT.to_string(), any_box![program.clone()]);

    let program_hints_collection = &program.shared_program_data.hints_collection;
    let program_address: Relocatable = exec_scopes.get(vars::PROGRAM_ADDRESS)?;
    let references = &program.shared_program_data.reference_manager;

    program_hints_collection
        .hints_ranges
        .iter()
        .try_for_each(|(pc, hint_range)| {
            let adjusted_pc = (program_address + pc.offset)?;
            let start = hint_range.0;
            let end = start + hint_range.1.get();
            let compiled_hints = program_hints_collection.hints[start..end]
                .iter()
                .map(|hint| {
                    hint_compiler
                        .compile_hint(
                            &hint.code,
                            &hint.flow_tracking_data.ap_tracking,
                            &hint.flow_tracking_data.reference_ids,
                            references,
                        )
                        .map_err(|err| {
                            HintError::CustomHint(format!("{err} for hint: {}", hint.code).into())
                        })
                })
                .collect::<Result<Vec<_>, HintError>>()?;
            hint_extension.insert(adjusted_pc, compiled_hints);
            Ok::<(), HintError>(())
        })?;

    Ok(())
}

/// Implements a hint that sets up the subtask for execution. It assumes that the program is already
/// loaded into memory and the task is set in the execution scopes.
/// Supports Cairo0 and Cairo1 programs, as well as CairoPIEs.
/// If the program is Cairo0 or Cairo1, it processes the program's hints and constants.
/// If the program is a CairoPIE, it loads the PIE into memory and sets up the necessary pointers.
/// It also prepares the output runner data and enters a new scope with the task locals.
pub fn setup_subtask_for_execution(
    hint_processor: &mut BootloaderHintProcessor,
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<HintExtension, HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;

    let n_builtins = get_program_from_task(&task)?.builtins.len();
    exec_scopes.insert_value(vars::N_BUILTINS, n_builtins);

    let mut new_task_locals = HashMap::new();

    let mut hint_extension = HintExtension::default();

    let subtask_cairo0_constants: Option<HashMap<String, Felt252>>;
    let subtask_cairo1_hint_processor: Option<CairoHintProcessor>;
    match &task {
        Task::Cairo0Program(cairo0_executable) => {
            if let Some(program_input) = cairo0_executable.program_input.as_ref() {
                new_task_locals.insert(PROGRAM_INPUT.to_string(), any_box![program_input.clone()]);
            }

            process_program_common_logic(
                &cairo0_executable.program,
                &mut new_task_locals,
                exec_scopes,
                hint_processor,
                &mut hint_extension,
            )?;

            subtask_cairo0_constants = Some(cairo0_executable.program.constants.clone());
            // This task doesn’t require a cairo1 hint processor.
            subtask_cairo1_hint_processor = None;
        }
        Task::Pie(cairo_pie) => {
            let program_address: Relocatable = exec_scopes.get("program_address")?;

            // ret_pc = ids.ret_pc_label.instruction_offset_ - ids.call_task.instruction_offset_ +
            // pc
            let bootloader_identifiers = get_program_identifies(exec_scopes, PROGRAM_OBJECT)?;
            let ret_pc_label = get_identifier(&bootloader_identifiers, "starkware.cairo.bootloaders.simple_bootloader.execute_task.execute_task.ret_pc_label")?;
            let call_task = get_identifier(
                &bootloader_identifiers,
                "starkware.cairo.bootloaders.simple_bootloader.execute_task.execute_task.call_task",
            )?;

            let ret_pc_offset = ret_pc_label - call_task;
            let ret_pc = (vm.get_pc() + ret_pc_offset)?;

            load_cairo_pie(
                cairo_pie,
                vm,
                program_address,
                (vm.get_ap() - n_builtins)?,
                vm.get_fp(),
                ret_pc,
            )
            .map_err(Into::<HintError>::into)?;
            // No subtask constants and cairo1 hint processor are used.
            subtask_cairo0_constants = None;
            subtask_cairo1_hint_processor = None;
        }
        Task::Cairo1Program(cairo1_executable) => {
            subtask_cairo1_hint_processor = Some(CairoHintProcessor {
                runner: None,
                user_args: vec![vec![Arg::Array(cairo1_executable.user_args.clone())]],
                string_to_hint: cairo1_executable.string_to_hint.clone(),
                starknet_state: Default::default(),
                run_resources: Default::default(),
                syscalls_used_resources: Default::default(),
                no_temporary_segments: false,
                markers: Default::default(),
                panic_traceback: Default::default(),
            });
            process_program_common_logic(
                &cairo1_executable.program,
                &mut new_task_locals,
                exec_scopes,
                subtask_cairo1_hint_processor.as_ref().unwrap(),
                &mut hint_extension,
            )?;
            // Push None since no subtask constants are used.
            subtask_cairo0_constants = None;
        }
    }
    hint_processor.spawn_subtask(subtask_cairo0_constants, subtask_cairo1_hint_processor);

    // output_runner_data = prepare_output_runner(
    //     task=task,
    //     output_builtin=output_builtin,
    //     output_ptr=ids.pre_execution_builtin_ptrs.output)
    let pre_execution_builtin_ptrs_addr =
        get_relocatable_from_var_name(vars::PRE_EXECUTION_BUILTIN_PTRS, vm, ids_data, ap_tracking)?;
    // The output field is the first one in the BuiltinData struct
    let output_ptr = vm.get_relocatable((pre_execution_builtin_ptrs_addr + 0)?)?;
    let output_runner_data =
        util::prepare_output_runner(&task, vm.get_output_builtin_mut()?, output_ptr)?;

    exec_scopes.insert_value(vars::OUTPUT_RUNNER_DATA, output_runner_data);

    exec_scopes.enter_scope(new_task_locals);

    Ok(hint_extension)
}

// Implements hint:
// %{
//     vm_exit_scope()
//     # Note that bootloader_input will only be available in the next hint.
// %}
// also despawns the subtask from the hint processor.
pub fn execute_task_exit_scope(
    hint_processor: &mut BootloaderHintProcessor,
    exec_scopes: &mut ExecutionScopes,
) -> Result<HintExtension, HintError> {
    exit_scope(exec_scopes)?;
    hint_processor.despawn_subtask();
    Ok(HintExtension::default())
}

// TODO(idanh): can't find this hint anywhere in the starkware main repo, consider removing it.
/// Implements
/// # Validate hash.
/// from starkware.cairo.bootloaders.hash_program import compute_program_hash_chain
///
/// assert memory[ids.output_ptr + 1] == compute_program_hash_chain(
///     program=task.get_program(),
///     use_poseidon=bool(ids.use_poseidon)), 'Computed hash does not match input.'
pub fn bootloader_validate_hash(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_hash_function: HashFunc = exec_scopes.get(vars::PROGRAM_HASH_FUNCTION)?;

    if program_hash_function == HashFunc::Blake {
        // No need to compute the hash if the function is Blake, since it's computed by the program
        // using the dedicated opcodes which use the rust implementation of Blake in the lambdaclass
        // repo.
        return Ok(());
    }

    let task: Task = exec_scopes.get(vars::TASK)?;
    let program = get_program_from_task(&task)?;
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    let program_hash_ptr = (output_ptr + 1)?;
    let program_hash = vm.get_integer(program_hash_ptr)?.into_owned();
    let computed_program_hash = compute_program_hash_chain(&program, 0, program_hash_function)
        .map_err(|e| {
            HintError::CustomHint(format!("Could not compute program hash: {e}").into_boxed_str())
        })?;
    let computed_program_hash = field_element_to_felt(computed_program_hash);
    if program_hash != computed_program_hash {
        return Err(HintError::AssertionFailed(
            "Computed hash does not match input"
                .to_string()
                .into_boxed_str(),
        ));
    }
    Ok(())
}

mod util {
    // TODO: clean up / organize
    use super::*;

    /// Prepares the output builtin if the type of task is Task, so that pages of the inner program
    /// will be recorded separately.
    /// If the type of task is CairoPie, nothing should be done, as the program does not contain
    /// hints that may affect the output builtin.
    /// The return value of this function should be later passed to get_task_fact_topology().
    pub(crate) fn prepare_output_runner(
        task: &Task,
        output_builtin: &mut OutputBuiltinRunner,
        output_ptr: Relocatable,
    ) -> Result<Option<OutputBuiltinState>, HintError> {
        match task {
            Task::Cairo0Program(_) | Task::Cairo1Program(_) => {
                let output_state = output_builtin.get_state();
                output_builtin.new_state(
                    output_ptr.segment_index as usize,
                    output_ptr.offset,
                    true,
                );
                Ok(Some(output_state))
            }
            Task::Pie(_) => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hints::codes::*;
    use crate::hints::types::{Cairo0Executable, Task};
    use crate::test_utils::{get_hint_codes_at_pc, prepare_non_continuous_ids_data_for_test};
    use crate::test_utils::{prepare_ids_data_for_test, prepare_vm_for_load_program_loading_test};
    use cairo_vm::any_box;
    use cairo_vm::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::HintProcessorData;
    use cairo_vm::hint_processor::hint_processor_definition::HintProcessorLogic;
    use cairo_vm::vm::runners::builtin_runner::BuiltinRunner;
    use cairo_vm::vm::runners::cairo_pie::PublicMemoryPage;
    use rstest::{fixture, rstest};

    /// This test checks that the program data is allocated in a new segment and that the
    /// pointers in the ids_data point to it.
    #[rstest]
    fn test_allocation_in_load_program_hint(fibonacci: Program) {
        let fibonacci_task = Task::Cairo0Program(Cairo0Executable {
            program: fibonacci.clone(),
            program_input: None,
        });
        let (
            mut vm,
            ids_data,
            mut exec_scopes,
            ap_tracking,
            expected_program_data_segment_index,
            _,
            _task,
        ) = prepare_vm_for_load_program_loading_test(fibonacci_task.clone());

        load_program_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        let program_data_ptr =
            get_ptr_from_var_name("program_data_ptr", &mut vm, &ids_data, &ap_tracking)
                .expect("program_data_ptr is not set");

        let program_data_base: Relocatable = exec_scopes
            .get(vars::PROGRAM_DATA_BASE)
            .expect(format!("{} is not set", vars::PROGRAM_DATA_BASE).as_ref());
        assert_eq!(program_data_ptr, program_data_base);

        // Check that we allocated a new segment and that the pointers point to it
        assert_eq!(
            vm.segments.num_segments(),
            expected_program_data_segment_index + 1
        );
        assert_eq!(
            program_data_ptr,
            Relocatable {
                segment_index: expected_program_data_segment_index as isize,
                offset: 0
            }
        );
    }

    #[fixture]
    fn fibonacci() -> Program {
        let program_content = include_bytes!(
            "../../resources/compiled_programs/test_programs/fibonacci_compiled.json"
        )
        .to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    #[fixture]
    fn fibonacci_pie() -> CairoPie {
        let pie_bytes =
            include_bytes!("../../resources/compiled_programs/test_programs/fibonacci_pie.zip");
        CairoPie::from_bytes(pie_bytes).expect("Failed to load the program PIE")
    }

    #[fixture]
    fn builtin_usage_program() -> Program {
        let program_content = include_bytes!(
            "../../resources/compiled_programs/test_programs/builtin_usage_all_cairo_compiled.json"
        )
        .to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    /// This test checks that the program is loaded correctly into memory and that the
    /// program address is set correctly. This test does not check the content of the program,
    /// but rather that the program is loaded into a new segment and that the program address
    /// is set correctly, and the entire program is loaded into memory. The loaded content of
    /// memory is checked in program_loader.rs tests.
    #[rstest]
    fn test_load_program(fibonacci: Program) {
        let fibonacci_task = Task::Cairo0Program(Cairo0Executable {
            program: fibonacci.clone(),
            program_input: None,
        });

        let (
            mut vm,
            ids_data,
            mut exec_scopes,
            ap_tracking,
            _expected_program_data_segment_index,
            program_header_ptr,
            _task,
        ) = prepare_vm_for_load_program_loading_test(fibonacci_task.clone());

        load_program_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // The Fibonacci program has only one builtin (output) -> the header size is 4 + #builtins =
        // 5.
        let header_size = 5;
        let expected_code_address = Relocatable::from((
            program_header_ptr.segment_index,
            program_header_ptr.offset + header_size,
        ));

        let program_address: Relocatable = exec_scopes.get(vars::PROGRAM_ADDRESS).unwrap();
        assert_eq!(program_address, expected_code_address);

        // Check that the segment was finalized
        let expected_program_size = header_size + fibonacci.data_len();
        assert_eq!(
            vm.segments.segment_sizes[&(program_address.segment_index as usize)],
            expected_program_size
        );
    }

    /// This test checks that the call_task hint works correctly. It sets up the VM, loads the
    /// program, and then calls the call_task hint. It loads the program into memory, and
    /// afterwards sets up the BuiltinData from the pre-execution of the call_task hint.
    /// After it runs the hint, it asserts that the hints from the program are loaded to the hint
    /// extension, and that the output runner data is set correctly.
    #[rstest]
    fn test_call_task(fibonacci: Program) {
        let fibonacci_task = Task::Cairo0Program(Cairo0Executable {
            program: fibonacci.clone(),
            program_input: None,
        });
        let (
            mut vm,
            ids_data,
            mut exec_scopes,
            ap_tracking,
            _expected_program_data_segment_index,
            _program_header_ptr,
            _task,
        ) = prepare_vm_for_load_program_loading_test(fibonacci_task.clone());

        load_program_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Allocate space for pre-execution (8 felts), which mimics the `BuiltinData` struct in
        // the Bootloader's Cairo code. Our code only uses the first felt (`output` field in
        // the struct)
        let _ = vm
            .segments
            .load_data(Relocatable::from((1, 3)), &[MaybeRelocatable::from((3, 0))]);
        // Set FP to 3 + 8 = 11, Since now the memory at segment 1 is:
        // (1, 0): (2, 0) // program segment pointer
        // (1, 1): (2, 0) // program header pointer
        // (1, 2): (2, 0) // program data pointer
        // (1, 3): (3, 0) // pre-execution output builtin pointer
        // (1, 4) to (1, 11) -> NONE // space for pre-execution builtins (only output is used)
        vm.set_fp(11);
        vm.set_ap(11);
        let ids_data: HashMap<String, HintReference> =
            prepare_non_continuous_ids_data_for_test(&[(vars::PRE_EXECUTION_BUILTIN_PTRS, -8)]);

        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin));

        let task = Task::Cairo0Program(Cairo0Executable {
            program: fibonacci.clone(),
            program_input: None,
        });

        exec_scopes.insert_box(vars::TASK, Box::new(task));

        let hint_data =
            HintProcessorData::new_default(String::from(EXECUTE_TASK_CALL_TASK), ids_data);

        let mut hint_processor = BootloaderHintProcessor::new();

        let hint_extension = hint_processor
            .execute_hint_extensive(
                &mut vm,
                &mut exec_scopes,
                &any_box!(hint_data),
                &HashMap::new(),
            )
            .expect("Hint failed unexpectedly");

        // Fibonnacci code should be loaded after the header whose size is 5 as checked in
        // test_load_program.
        let expected_code_address_offset = 5;

        // Fibonacci program has 2 hints:
        // 1. "memory[ap] = program_input['second_element']" at instruction 8
        // 2. "memory[ap] = program_input['fibonacci_claim_index']" at instruction 9
        // they should be loaded at (2, 5 + 8) and (2, 5 + 9) respectively.
        let hint_codes_1 = get_hint_codes_at_pc(
            &hint_extension,
            Relocatable::from((2, expected_code_address_offset + 8)),
        );
        assert!(hint_codes_1.contains(&"memory[ap] = program_input['second_element']"));

        let hint_codes_2 = get_hint_codes_at_pc(
            &hint_extension,
            Relocatable::from((2, expected_code_address_offset + 9)),
        );
        assert!(hint_codes_2.contains(&"memory[ap] = program_input['fibonacci_claim_index']"));

        let _ = exec_scopes.exit_scope();
        let expected_output_runner_data = OutputBuiltinState {
            base: 3,
            base_offset: 0,
            pages: HashMap::new(),
            attributes: HashMap::new(),
        };

        // Asserting that output runner was initialized correctly, and the data is correct.
        // After exiting the scope, OUTPUT_RUNNER_DATA should be available in the current scope.
        let data = exec_scopes
            .get::<Option<OutputBuiltinState>>(vars::OUTPUT_RUNNER_DATA)
            .expect("OUTPUT_RUNNER_DATA should be available after exiting the scope")
            .unwrap();

        assert_eq!(data, expected_output_runner_data);
    }

    fn get_simple_bootloader_program() -> Program {
        let bootloader_program_content = include_bytes!(
            "../../resources/compiled_programs/bootloaders/simple_bootloader_compiled.json"
        )
        .to_vec();

        Program::from_bytes(&bootloader_program_content, Some("main"))
            .expect("Loading simple bootloader program failed unexpectedly")
    }

    /// This test checks that the call_task hint works correctly for a Cairo PIE task. It sets up
    /// the VM, to a similar state as in the execute_task function in execute_task.cairo.
    #[rstest]
    fn test_call_cairo_pie_task(fibonacci_pie: CairoPie) {
        let fibonacci_pie_task = Task::Pie(fibonacci_pie.clone());
        let (
            mut vm,
            ids_data,
            mut exec_scopes,
            ap_tracking,
            _expected_program_data_segment_index,
            _program_header_ptr,
            _task,
        ) = prepare_vm_for_load_program_loading_test(fibonacci_pie_task.clone());

        // Loading the cairo_pie program into the VM memory - emulates the load_program_segment
        // without computing the program hash. Skipping writing the program hash to output_ptr.
        // as it is not needed for the test.

        load_program_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // We set the program header pointer at (1, 0) and make it point to the start of segment#2.
        // Allocate space for pre-execution (8 values), which follows the `BuiltinData`struct in
        // the Bootloader Cairo code. Our code only uses the first felt (`output`field in the
        // struct). Finally, we put the mocked output of `select_input_builtins`in the next
        // memory address and increase the AP register accordingly.
        let _ = vm.load_data(
            Relocatable::from((1, 3)),
            &[
                MaybeRelocatable::from((4, 0)), // pre-execution builtins pointer
            ],
        );
        let _ = vm
            .load_data(
                Relocatable::from((1, 11)),
                &[MaybeRelocatable::from((4, 42))], // mocked output of select_input_builtins
            )
            .expect("Failed to load data into VM segments");
        vm.set_ap(12);
        vm.set_fp(11);

        let program_header_ptr = Relocatable::from((2, 0));
        let ids_data = prepare_non_continuous_ids_data_for_test(&[
            ("program_header", -9),
            (vars::PRE_EXECUTION_BUILTIN_PTRS, -8),
        ]);

        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin));

        let task = Task::Pie(fibonacci_pie.clone());
        exec_scopes.insert_value(vars::TASK, task);
        let bootloader_program = get_simple_bootloader_program();
        exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_header_ptr.clone());
        exec_scopes.insert_value(vars::PROGRAM_OBJECT, bootloader_program);

        // Execute the hint
        let mut hint_processor = BootloaderHintProcessor::new();
        setup_subtask_for_execution(
            &mut hint_processor,
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
        )
        .expect("Hint failed unexpectedly");

        // Check that the code section on the PIE is loaded correctly into memory
        let pie_memory = fibonacci_pie.memory;
        for (offset, value) in pie_memory.0.iter() {
            let (segment_index, base_offset) = match offset.0 {
                0 => (2, 5),
                1 => break, //checking only the code segment, so we break after the first segment
                _ => panic!("Unexpected segment index: {}", offset.0),
            };
            let vm_addr = Relocatable::from((segment_index, base_offset + offset.1));
            let vm_value = vm
                .get_maybe(&vm_addr)
                .expect("Failed to get VM memory value");
            assert_eq!(&vm_value, value, "Mismatch at offset {}", offset.1);
        }

        // TODO(idanh): Check that the ExecutionSegment is loaded correctly.

        // Check that the output runner data is set correctly to NONE,
        // since Cairo PIE tasks do not use the output runner.
        exec_scopes.exit_scope().expect("Failed to exit scope");
        let output_runner_data = exec_scopes
            .get::<Option<OutputBuiltinState>>(vars::OUTPUT_RUNNER_DATA)
            .expect("OUTPUT_RUNNER_DATA should be available after exiting the scope");
        assert_eq!(
            output_runner_data, None,
            "Output runner data should be None for Cairo PIE tasks"
        );
    }

    /// This test checks that the append_fact_topologies hint works correctly.
    /// It sets up the VM state to before the hint is called, and checks that
    /// the fact topology is updated correctly after the hint is called.
    #[rstest]
    fn test_append_fact_topologies(fibonacci: Program) {
        let fibonacci_task = Task::Cairo0Program(Cairo0Executable {
            program: fibonacci.clone(),
            program_input: None,
        });

        let mut vm = VirtualMachine::new(false, false);

        // Allocate space for the pre-execution and return builtin structs (2 x 8 felts).
        // The pre-execution struct starts at (1, 0) and the return struct at (1, 8).
        // We only set the output values to (2, 0) and (2, 10), respectively, to get an output size
        // of 10.
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment();

        vm.load_data(Relocatable::from((1, 0)), &[MaybeRelocatable::from((2, 0))])
            .expect("Failed to load data into VM segments");
        vm.load_data(
            Relocatable::from((1, 8)),
            &[MaybeRelocatable::from((2, 10))],
        )
        .expect("Failed to load data into VM segments");
        vm.set_fp(16);

        let tree_structure = vec![1, 2, 3, 4];
        let output_builtin_state = OutputBuiltinState {
            base: 0,
            base_offset: 0,
            pages: HashMap::from([
                (1, PublicMemoryPage { start: 0, size: 7 }),
                (2, PublicMemoryPage { start: 7, size: 3 }),
            ]),
            attributes: HashMap::from([("gps_fact_topology".to_string(), tree_structure.clone())]),
        };

        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.set_state(output_builtin_state.clone());
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin));

        let ids_data = prepare_non_continuous_ids_data_for_test(&[
            ("pre_execution_builtin_ptrs", -16),
            ("return_builtin_ptrs", -8),
        ]);
        let ap_tracking = ApTracking::new();
        let mut exec_scopes = ExecutionScopes::new();

        exec_scopes.insert_value(vars::OUTPUT_RUNNER_DATA, Some(output_builtin_state.clone()));
        exec_scopes.insert_value(vars::TASK, fibonacci_task);
        exec_scopes.insert_value(vars::FACT_TOPOLOGIES, Vec::<FactTopology>::new());

        append_fact_topologies(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that the fact topology matches the data from the output builtin
        let fact_topologies: Vec<FactTopology> = exec_scopes.get(vars::FACT_TOPOLOGIES).unwrap();
        assert_eq!(fact_topologies.len(), 1);
        let fact_topology = &fact_topologies[0];
        assert_eq!(fact_topology.page_sizes, vec![0, 7, 3]);
        assert_eq!(fact_topology.tree_structure, tree_structure);
    }

    /// This test checks that the write_return_builtins hint works correctly.
    /// It sets up the VM state to before the hint is called, and checks that
    /// the return builtins are written correctly after the hint is called.
    /// The builtin_usage_program uses the output, pedersen, range_check, bitwise,
    /// ecdsa, keccak, ec_op, poseidon, hint, and mul_mod builtins.
    /// The hint writes the used builtins to the return struct, which is
    /// expected to be at (1, 22) in the VM memory.
    #[rstest]
    fn test_write_output_builtins(builtin_usage_program: Program) {
        let task = Task::Cairo0Program(Cairo0Executable {
            program: builtin_usage_program.clone(),
            program_input: None,
        });

        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment(); // Segment 0
        vm.add_memory_segment(); // Segment 1
        vm.add_memory_segment(); // Segment 2

        // Allocate space for all the builtin list structs (3 x 11 felts).
        // The pre-execution struct starts at (1, 0), the used builtins list at (1, 11)
        // and the return struct at (1, 22).
        // Initialize the pre-execution struct to [1, 2, ..., 11].
        // Initialize the used builtins to {output: 30, pedersen: 31, ..., mul_mod: 40} as these are
        // used by the builtin_usage program.
        let segment_data = [
            ((1, 0), (2, 1)),
            ((1, 1), (2, 2)),
            ((1, 2), (2, 3)),
            ((1, 3), (2, 4)),
            ((1, 4), (2, 5)),
            ((1, 5), (2, 6)),
            ((1, 6), (2, 7)),
            ((1, 7), (2, 8)),
            ((1, 8), (2, 9)),
            ((1, 9), (2, 10)),
            ((1, 10), (2, 11)),
            // Used builtins
            ((1, 11), (2, 30)),
            ((1, 12), (2, 31)),
            ((1, 13), (2, 32)),
            ((1, 14), (2, 33)),
            ((1, 15), (2, 34)),
            ((1, 16), (2, 35)),
            ((1, 17), (2, 36)),
            ((1, 18), (2, 37)),
            ((1, 19), (2, 38)),
            ((1, 20), (2, 39)),
            ((1, 21), (2, 40)),
            // Return struct pointer
            ((1, 33), (1, 11)),
        ];
        for (src, dst) in segment_data.iter() {
            vm.load_data(Relocatable::from(*src), &[MaybeRelocatable::from(*dst)])
                .expect("Failed to load data into VM segments");
        }
        vm.set_fp(34);
        vm.set_ap(34);

        let ids_data = prepare_non_continuous_ids_data_for_test(&[
            ("pre_execution_builtin_ptrs", -34),
            ("return_builtin_ptrs", -12),
            ("used_builtins_addr", -1),
        ]);
        let ap_tracking = ApTracking::new();

        let mut exec_scopes = ExecutionScopes::new();
        let n_builtins = builtin_usage_program.builtins_len();
        exec_scopes.insert_value(vars::N_BUILTINS, n_builtins);
        exec_scopes.insert_value(vars::TASK, task);

        write_return_builtins_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that the return builtins were written correctly
        let return_builtins = vm
            .segments
            .memory
            .get_continuous_range(Relocatable::from((1, 22)), 11)
            .expect("Return builtin was not properly written to memory.");

        let expected_builtins = vec![
            Relocatable::from((2, 30)),
            Relocatable::from((2, 31)),
            Relocatable::from((2, 32)),
            Relocatable::from((2, 33)),
            Relocatable::from((2, 34)),
            Relocatable::from((2, 35)),
            Relocatable::from((2, 36)),
            Relocatable::from((2, 37)),
            Relocatable::from((2, 38)),
            Relocatable::from((2, 39)),
            Relocatable::from((2, 40)),
        ];
        for (expected, actual) in std::iter::zip(expected_builtins, return_builtins) {
            assert_eq!(MaybeRelocatable::RelocatableValue(expected), actual);
        }

        // Check that the exec scope changed
        assert_eq!(
            exec_scopes.data.len(),
            2,
            "A new scope should have been declared"
        );
        assert_eq!(
            exec_scopes.data[1].len(),
            1,
            "The new scope should only contain one variable"
        );
        let n_selected_builtins: usize = exec_scopes
            .get(vars::N_SELECTED_BUILTINS)
            .expect("n_selected_builtins should be set");
        assert_eq!(n_selected_builtins, n_builtins);
    }

    #[rstest(use_prev_hash, case(0), case(1))]
    fn test_determine_use_prev_hash(use_prev_hash: i32) {
        // This test checks that the determine_use_prev_hash hint works correctly.
        // It sets up the VM state to before the hint is called, and checks that
        // the use_prev_hash variable is set correctly after the hint is called in the VM's memory.
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(1);
        vm.set_ap(1);
        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::USE_PREV_HASH, use_prev_hash);
        let ids_data = prepare_ids_data_for_test(&["use_prev_hash"]);
        let ap_tracking = ApTracking::new();
        determine_use_prev_hash(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that the use_prev_hash variable is set correctly in the execution scope
        assert_eq!(
            vm.get_integer(Relocatable::from((1, 0)))
                .unwrap()
                .into_owned(),
            Felt252::from(use_prev_hash)
        );
    }
}
