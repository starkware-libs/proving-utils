use std::collections::HashMap;

use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::{
    get_constant_from_var_name, get_integer_from_var_name, get_ptr_from_var_name,
    insert_value_from_var_name, insert_value_into_ap,
};
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::errors::math_errors::MathError;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::runners::builtin_runner::EcOpBuiltinRunner;
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::Felt252;
use num_traits::ToPrimitive;
use starknet_types_core::felt::NonZeroFelt;

use crate::hints::execute_task_hints::ALL_BUILTINS;
use crate::hints::fact_topologies::FactTopology;
use crate::hints::types::SimpleBootloaderInput;
use crate::hints::vars;

/// Implements
/// n_tasks = len(simple_bootloader_input.tasks)
/// memory[ids.output_ptr] = n_tasks
///
/// # Task range checks are located right after simple bootloader validation range checks, and
/// # this is validated later in this function.
/// ids.task_range_check_ptr = ids.range_check_ptr + ids.BuiltinData.SIZE * n_tasks
///
/// # A list of fact_toplogies that instruct how to generate the fact from the program output
/// # for each task.
/// fact_topologies = []
pub fn prepare_task_range_checks(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // n_tasks = len(simple_bootloader_input.tasks)
    let simple_bootloader_input: &SimpleBootloaderInput =
        exec_scopes.get_ref(vars::SIMPLE_BOOTLOADER_INPUT)?;
    let n_tasks = simple_bootloader_input.tasks.len();

    // memory[ids.output_ptr] = n_tasks
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    vm.insert_value(output_ptr, Felt252::from(n_tasks))?;

    // ids.task_range_check_ptr = ids.range_check_ptr + ids.BuiltinData.SIZE * n_tasks
    // BuiltinData is a struct with n_builtins members defined in execute_task.cairo.
    const BUILTIN_DATA_SIZE: usize = ALL_BUILTINS.len();
    let range_check_ptr = get_ptr_from_var_name("range_check_ptr", vm, ids_data, ap_tracking)?;
    let task_range_check_ptr = (range_check_ptr + BUILTIN_DATA_SIZE * n_tasks)?;
    insert_value_from_var_name(
        "task_range_check_ptr",
        task_range_check_ptr,
        vm,
        ids_data,
        ap_tracking,
    )?;

    // fact_topologies = []
    let fact_topologies = Vec::<FactTopology>::new();
    exec_scopes.insert_value(vars::FACT_TOPOLOGIES, fact_topologies);

    Ok(())
}

/// Implements
/// %{ tasks = simple_bootloader_input.tasks %}
pub fn set_tasks_variable(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let simple_bootloader_input: &SimpleBootloaderInput =
        exec_scopes.get_ref(vars::SIMPLE_BOOTLOADER_INPUT)?;
    exec_scopes.insert_value(vars::TASKS, simple_bootloader_input.tasks.clone());

    Ok(())
}

/// Implements %{ ids.num // 2 %}
/// (compiled to %{ memory[ap] = to_felt_or_relocatable(ids.num // 2) %}).
pub fn divide_num_by_2(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let felt = get_integer_from_var_name("num", vm, ids_data, ap_tracking)?;
    // Unwrapping is safe in this context, 2 != 0
    let two = NonZeroFelt::try_from(Felt252::from(2)).unwrap();
    let felt_divided_by_2 = felt.floor_div(&two);

    insert_value_into_ap(vm, felt_divided_by_2)?;

    Ok(())
}

/// Implements %{ 0 %} (compiled to %{ memory[ap] = to_felt_or_relocatable(0) %}).
///
/// Stores 0 in the AP and returns.
/// Used as `tempvar use_poseidon = nondet %{ 0 %}`.
pub fn set_ap_to_zero(vm: &mut VirtualMachine) -> Result<(), HintError> {
    insert_value_into_ap(vm, Felt252::from(0))?;
    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.simple_bootloader.objects import Task
///
/// # Pass current task to execute_task.
/// task_id = len(simple_bootloader_input.tasks) - ids.n_tasks
/// task = simple_bootloader_input.tasks[task_id].load_task()
pub fn set_current_task(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let simple_bootloader_input: &SimpleBootloaderInput =
        exec_scopes.get_ref(vars::SIMPLE_BOOTLOADER_INPUT)?;
    let n_tasks_felt = get_integer_from_var_name("n_tasks", vm, ids_data, ap_tracking)?;
    let n_tasks = n_tasks_felt
        .to_usize()
        .ok_or(MathError::Felt252ToUsizeConversion(Box::new(n_tasks_felt)))?;

    let task_id = simple_bootloader_input.tasks.len() - n_tasks;
    let task = simple_bootloader_input.tasks[task_id].load_task();
    let use_poseidon = simple_bootloader_input.tasks[task_id].use_poseidon;

    exec_scopes.insert_value(vars::TASK, task.clone());
    exec_scopes.insert_value(vars::USE_POSEIDON, use_poseidon);

    Ok(())
}

/// Implements
/// from starkware.cairo.lang.builtins.ec.ec_op_builtin_runner import (
///     ec_op_auto_deduction_rule_wrapper,
/// )
/// ids.new_ec_op_ptr = segments.add()
/// vm_add_auto_deduction_rule(
///     segment_index=ids.new_ec_op_ptr.segment_index,
///     rule=ec_op_auto_deduction_rule_wrapper(ec_op_cache={}),
/// )
pub fn simple_bootloader_simulate_ec_op(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let mut ec_op_runner = EcOpBuiltinRunner::new(Some(1), false);
    ec_op_runner.initialize_segments(&mut vm.segments);
    let new_ec_op_ptr = Relocatable {
        segment_index: ec_op_runner.base as isize,
        offset: 0,
    };
    insert_value_from_var_name("new_ec_op_ptr", new_ec_op_ptr, vm, ids_data, ap_tracking)?;
    vm.simulated_builtin_runners.push(ec_op_runner.into());

    Ok(())
}

/// Implements
/// curr_m = ids.m
/// for i in range(ids.M_MAX_BITS):
///     memory[ids.m_bit_unpacking + i] = curr_m % 2
///     curr_m = curr_m >> 1
pub fn simulate_ec_op_fill_mem_with_bits_of_m(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let mut curr_m = get_integer_from_var_name("m", vm, ids_data, ap_tracking)?.to_biguint();
    let m_max_bits = get_constant_from_var_name("M_MAX_BITS", constants)?;
    let m_bit_unpacking = get_ptr_from_var_name("m_bit_unpacking", vm, ids_data, ap_tracking)?;
    (0..m_max_bits.to_usize().unwrap()).try_for_each(|i| {
        let bit = MaybeRelocatable::Int((&curr_m % 2u32).into());
        curr_m >>= 1;
        vm.insert_value((m_bit_unpacking + i)?, bit)
    })?;

    Ok(())
}

/// Implements
/// assert False, "ec_op failed."
pub fn simulate_ec_op_assert_false() -> Result<(), HintError> {
    Err(HintError::CustomHint("ec_op failed.".into()))
}

#[cfg(test)]
mod tests {
    use std::any::Any;
    use std::collections::HashMap;
    use std::collections::HashMap;

    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::{
        get_ptr_from_var_name, get_relocatable_from_var_name, insert_value_from_var_name,
    };
    use cairo_vm::hint_processor::hint_processor_definition::HintReference;
    use cairo_vm::serde::deserialize_program::{ApTracking, BuiltinName, Identifier};
    use cairo_vm::types::exec_scope::ExecutionScopes;
    use cairo_vm::types::program::Program;
    use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
    use cairo_vm::vm::errors::hint_errors::HintError;
    use cairo_vm::vm::errors::memory_errors::MemoryError;
    use cairo_vm::vm::runners::builtin_runner::OutputBuiltinRunner;
    use cairo_vm::vm::runners::cairo_pie::{
        CairoPie, OutputBuiltinAdditionalData, StrippedProgram,
    };
    use cairo_vm::vm::vm_core::VirtualMachine;
    use cairo_vm::vm::vm_memory::memory::Memory;
    use cairo_vm::{any_box, Felt252};
    use num_traits::ToPrimitive;
    use num_traits::ToPrimitive;
    use rstest::{fixture, rstest};
    use starknet_crypto::FieldElement;

    use crate::hints::fact_topologies::{get_task_fact_topology, FactTopology};
    use crate::hints::load_cairo_pie::load_cairo_pie;
    use crate::hints::program_hash::compute_program_hash_chain;
    use crate::hints::program_loader::ProgramLoader;
    use crate::hints::types::{BootloaderVersion, Task, TaskSpec};
    use crate::hints::vars;

    use super::*;

    #[fixture]
    fn fibonacci() -> Program {
        let program_content =
            include_bytes!("../../../../../cairo_programs/fibonacci.json").to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    #[fixture]
    fn simple_bootloader_input(fibonacci: Program) -> SimpleBootloaderInput {
        SimpleBootloaderInput {
            fact_topologies_path: None,
            single_page: false,
            tasks: vec![
                TaskSpec {
                    task: Task::Program(fibonacci.clone()),
                    use_poseidon: true,
                },
                TaskSpec {
                    task: Task::Program(fibonacci.clone()),
                    use_poseidon: true,
                },
            ],
        }
    }

    #[rstest]
    fn test_prepare_task_range_checks(simple_bootloader_input: SimpleBootloaderInput) {
        let mut vm = vm!();
        vm.run_context.fp = 3;
        vm.segments = segments![((1, 0), (2, 0)), ((1, 1), (2, 2))];
        let ids_data = ids_data!["output_ptr", "range_check_ptr", "task_range_check_ptr"];
        vm.add_memory_segment();

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(
            vars::SIMPLE_BOOTLOADER_INPUT,
            simple_bootloader_input.clone(),
        );

        let ap_tracking = ApTracking::new();

        prepare_task_range_checks(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        let task_range_check_ptr =
            get_ptr_from_var_name("task_range_check_ptr", &mut vm, &ids_data, &ap_tracking)
                .unwrap();

        // Assert *output_ptr == n_tasks
        let output = vm
            .segments
            .memory
            .get_integer(Relocatable {
                segment_index: 2,
                offset: 0,
            })
            .unwrap()
            .to_usize()
            .unwrap();
        assert_eq!(output, simple_bootloader_input.tasks.len());

        // Assert task_range_check_ptr == range_check_ptr (2, 2) + BUILTIN_DATA_SIZE (8) * n_tasks
        // (2)
        assert_eq!(
            task_range_check_ptr,
            Relocatable {
                segment_index: 2,
                offset: 18
            }
        );

        let fact_topologies: Vec<FactTopology> = exec_scopes
            .get(vars::FACT_TOPOLOGIES)
            .expect("Fact topologies missing from scope");
        assert!(fact_topologies.is_empty());
    }

    #[rstest]
    fn test_set_tasks_variable(simple_bootloader_input: SimpleBootloaderInput) {
        let bootloader_tasks = simple_bootloader_input.tasks.clone();

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::SIMPLE_BOOTLOADER_INPUT, simple_bootloader_input);

        set_tasks_variable(&mut exec_scopes).expect("Hint failed unexpectedly");

        let tasks: Vec<TaskSpec> = exec_scopes
            .get(vars::TASKS)
            .expect("Tasks variable is not set");
        assert_eq!(tasks, bootloader_tasks);
    }

    #[rstest]
    #[case(128u128, 64u128)]
    #[case(1001u128, 500u128)]
    fn test_divide_num_by_2(#[case] num: u128, #[case] expected: u128) {
        let num_felt = Felt252::from(num);
        let expected_num_felt = Felt252::from(expected);

        let mut vm = vm!();
        add_segments!(vm, 2);
        vm.run_context.ap = 1;
        vm.run_context.fp = 1;

        let ids_data = ids_data!["num"];
        let ap_tracking = ApTracking::new();

        insert_value_from_var_name("num", num_felt, &mut vm, &ids_data, &ap_tracking).unwrap();

        divide_num_by_2(&mut vm, &ids_data, &ap_tracking).expect("Hint failed unexpectedly");

        let divided_num = vm
            .segments
            .memory
            .get_integer(vm.run_context.get_ap())
            .unwrap();
        assert_eq!(divided_num.into_owned(), expected_num_felt);
    }

    #[rstest]
    fn test_set_to_zero() {
        let mut vm = vm!();
        add_segments!(vm, 2);

        set_ap_to_zero(&mut vm).expect("Hint failed unexpectedly");

        let ap_value = vm
            .segments
            .memory
            .get_integer(vm.run_context.get_ap())
            .unwrap()
            .into_owned();

        assert_eq!(ap_value, Felt252::from(0));
    }

    #[rstest]
    fn test_set_current_task(simple_bootloader_input: SimpleBootloaderInput) {
        // Set n_tasks to 1
        let mut vm = vm!();
        vm.run_context.fp = 2;
        vm.segments = segments![((1, 0), 1)];

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::SIMPLE_BOOTLOADER_INPUT, simple_bootloader_input);

        let ids_data = ids_data!["n_tasks", "task"];
        let ap_tracking = ApTracking::new();

        set_current_task(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that `task` is set
        let _task: Task = exec_scopes
            .get(vars::TASK)
            .expect("task variable is not set.");
    }
}
