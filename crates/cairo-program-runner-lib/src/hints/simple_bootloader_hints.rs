use std::collections::HashMap;

use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::{
    get_constant_from_var_name, get_integer_from_var_name, get_ptr_from_var_name,
    get_relocatable_from_var_name, insert_value_from_var_name, insert_value_into_ap,
};
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::errors::math_errors::MathError;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::runners::builtin_runner::{
    EcOpBuiltinRunner, KeccakBuiltinRunner, SignatureBuiltinRunner,
};
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::Felt252;
use num_bigint::BigUint;
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

/// Implements
/// from starkware.cairo.common.keccak_utils.keccak_utils import keccak_func
/// from starkware.cairo.lang.builtins.keccak.keccak_builtin_runner import (
///     keccak_auto_deduction_rule_wrapper,
/// )
/// ids.new_keccak_ptr = segments.add()
/// vm_add_auto_deduction_rule(
///     segment_index=ids.new_keccak_ptr.segment_index,
///     rule=keccak_auto_deduction_rule_wrapper(keccak_cache={}),
/// )
pub fn simple_bootloader_simulate_keccak(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let mut keccak_runner = KeccakBuiltinRunner::new(Some(1), false);
    keccak_runner.initialize_segments(&mut vm.segments);
    let new_keccak_ptr = Relocatable {
        segment_index: keccak_runner.base as isize,
        offset: 0,
    };
    insert_value_from_var_name("new_keccak_ptr", new_keccak_ptr, vm, ids_data, ap_tracking)?;
    vm.simulated_builtin_runners.push(keccak_runner.into());

    Ok(())
}

/// Implements
/// full_num = ids.keccak_builtin_state.s0
/// full_num += (2**200) * ids.keccak_builtin_state.s1
/// full_num += (2**400) * ids.keccak_builtin_state.s2
/// full_num += (2**600) * ids.keccak_builtin_state.s3
/// full_num += (2**800) * ids.keccak_builtin_state.s4
/// full_num += (2**1000) * ids.keccak_builtin_state.s5
/// full_num += (2**1200) * ids.keccak_builtin_state.s6
/// full_num += (2**1400) * ids.keccak_builtin_state.s7
/// for i in range(25):
///     memory[ids.felt_array + i] = full_num % (2**64)
///     full_num = full_num >> 64
pub fn simulate_keccak_fill_mem_with_state(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let keccak_builtin_state_addr =
        get_relocatable_from_var_name("keccak_builtin_state", vm, ids_data, ap_tracking)?;
    let felt_array = get_ptr_from_var_name("felt_array", vm, ids_data, ap_tracking)?;
    let mut full_num = (0..8).try_fold(BigUint::ZERO, |acc, i| {
        let s = vm.get_integer((keccak_builtin_state_addr + i)?)?;
        Ok::<_, HintError>(acc + (s.to_biguint() << (i * 200)))
    })?;
    let modulo = BigUint::from(1u128 << 64);
    (0..25).try_for_each(|i| {
        let felt = MaybeRelocatable::Int((&full_num % &modulo).into());
        full_num >>= 64;
        vm.insert_value((felt_array + i)?, felt)
    })?;

    Ok(())
}

/// Implements hints of the form
/// ids.high{index}, ids.low{index} = divmod(memory[ids.felt_array + {index}], 256 ** {x})
/// Where {index} is a number in [3,6,9,12,15,18,21] and {x} is a number in [1,2,3,4,5,6,7]
pub fn simulate_keccak_calc_high_low(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    index: usize,
) -> Result<(), HintError> {
    let felt_array = get_ptr_from_var_name("felt_array", vm, ids_data, ap_tracking)?;
    let felt = vm.get_integer((felt_array + index)?)?;
    let x = index / 3;
    let divisor = NonZeroFelt::try_from(Felt252::from(1u64 << (x * 8))).unwrap();
    let (high_felt, low_felt) = felt.div_rem(&divisor);
    insert_value_from_var_name(
        &format!("high{}", index),
        high_felt,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        &format!("low{}", index),
        low_felt,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

/// Implements
/// from starkware.cairo.lang.builtins.signature.signature_builtin_runner import (
///     signature_rule_wrapper,
/// )
/// from starkware.cairo.lang.vm.cairo_runner import verify_ecdsa_sig
/// ids.new_ecdsa_ptr = segments.add()
/// vm_add_validation_rule(
///     segment_index=ids.new_ecdsa_ptr.segment_index,
///     rule=signature_rule_wrapper(
///         verify_signature_func=verify_ecdsa_sig,
///         # Store signatures inside the vm's state. vm_ecdsa_additional_data is dropped
///         # into the execution scope by the vm.
///         signature_cache=vm_ecdsa_additional_data,
///         ),
/// )
pub fn simple_bootloader_simulate_ecdsa(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let mut ecdsa_runner = SignatureBuiltinRunner::new(Some(1), false);
    ecdsa_runner.initialize_segments(&mut vm.segments);
    let new_ecdsa_ptr = Relocatable {
        segment_index: ecdsa_runner.base as isize,
        offset: 0,
    };
    insert_value_from_var_name("new_ecdsa_ptr", new_ecdsa_ptr, vm, ids_data, ap_tracking)?;
    ecdsa_runner.add_validation_rule(&mut vm.segments.memory);
    vm.simulated_builtin_runners.push(ecdsa_runner.into());
    Ok(())
}

/// Implements
/// (ids.r, ids.s) = vm_ecdsa_additional_data[ids.start.address_]
pub fn simulate_ecdsa_get_r_and_s(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let start = get_ptr_from_var_name("start", vm, ids_data, ap_tracking)?;
    let ecdsa_builtin = vm.get_signature_builtin()?;
    let (r, s) = {
        let signatures = ecdsa_builtin.signatures.borrow();
        let signature = signatures
            .get(&start)
            .ok_or_else(|| HintError::CustomHint("No signature found for start pointer.".into()))?;
        (signature.r, signature.s)
    };
    insert_value_from_var_name("r", r, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name("s", s, vm, ids_data, ap_tracking)?;

    Ok(())
}

/// Implements
/// # ids.StarkCurve.ORDER is parsed as a negative number.
/// order = ids.StarkCurve.ORDER + PRIME
/// ids.w = pow(ids.signature_s, -1, order)
/// ids.wz = ids.w*ids.message % order
/// ids.wr = ids.w*ids.signature_r % order
pub fn simulate_ecdsa_compute_w_wr_wz(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let order_const_id = "starkware.cairo.common.ec.StarkCurve.ORDER";
    let order = constants
        .get(order_const_id)
        .ok_or_else(|| HintError::MissingConstant(Box::new(order_const_id)))?;
    let order = &NonZeroFelt::from_felt_unchecked(*order);
    let s = get_integer_from_var_name("signature_s", vm, ids_data, ap_tracking)?;
    let r = get_integer_from_var_name("signature_r", vm, ids_data, ap_tracking)?;
    let message = get_integer_from_var_name("message", vm, ids_data, ap_tracking)?;
    let w = s.mod_inverse(order).unwrap();
    let wz = w.mul_mod(&message, order);
    let wr = w.mul_mod(&r, order);
    insert_value_from_var_name("w", w, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name("wz", wz, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name("wr", wr, vm, ids_data, ap_tracking)?;
    Ok(())
}

/// Implements
/// num = ids.num
/// memory[ids.res_96_felts] = num % (2**96)
/// memory[ids.res_96_felts+1] = (num>>96) % (2**96)
/// memory[ids.res_96_felts+2] = (num>>(2*96)) % (2**96)
pub fn simulate_ecdsa_fill_mem_with_felt_96_bit_limbs(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let num = get_integer_from_var_name("num", vm, ids_data, ap_tracking)?;
    let res_96_felts = get_ptr_from_var_name("res_96_felts", vm, ids_data, ap_tracking)?;
    let mut num = num.to_biguint();
    let modulo = BigUint::from(1u128 << 96);
    (0..3).try_for_each(|i| {
        let felt = MaybeRelocatable::Int((&num % &modulo).into());
        num >>= 96;
        vm.insert_value((res_96_felts + i)?, felt)
    })?;

    Ok(())
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
