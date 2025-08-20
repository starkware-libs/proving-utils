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

use super::types::HashFunc;
use crate::hints::fact_topologies::FactTopology;
use crate::hints::types::SimpleBootloaderInput;
use crate::hints::vars;

use super::utils::get_program_from_task;

/// Implements a hint that:
/// 1. Writes the number of tasks into `output_ptr[0]`.
/// 2. Sets `initial_subtasks_range_check_ptr` to a new temporary segment.
/// 3. Initializes `fact_topologies` hint variable to an empty array.
pub fn setup_run_simple_bootloader_before_task_execution(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let simple_bootloader_input: &SimpleBootloaderInput =
        exec_scopes.get_ref(vars::SIMPLE_BOOTLOADER_INPUT)?;

    let n_tasks = simple_bootloader_input.tasks.len();
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    vm.insert_value(output_ptr, Felt252::from(n_tasks))?;

    let temp_segment = vm.add_temporary_segment();
    insert_value_from_var_name(
        "initial_subtasks_range_check_ptr",
        temp_segment,
        vm,
        ids_data,
        ap_tracking,
    )?;

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

// Implements hint: "memory[ap] = to_felt_or_relocatable(1 if task.program_hash_function else 0)"
// Note: The python code above is obsolete and we just use this hint code to map to the below
// function which implements the required logic.
pub fn program_hash_function_to_ap(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let program_hash_function: HashFunc = exec_scopes.get(vars::PROGRAM_HASH_FUNCTION)?;
    insert_value_into_ap(vm, program_hash_function as usize)
}

/// Sets the current task for the simple bootloader run -
/// it extracts the task and the program hash function from the `SimpleBootloaderInput`
/// and inserts them into the execution scopes. It also determines whether to use the previous
/// task's hash based on whether the current task is the first one or if it has the same program as
/// the previous task. (This is an optimization to avoid recomputing the hash if the program is the
/// same).
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
    let program_hash_function = simple_bootloader_input.tasks[task_id].program_hash_function;

    let mut use_prev_hash = 0;
    if task_id > 0 {
        let prev_task = simple_bootloader_input.tasks[task_id - 1].load_task();
        use_prev_hash =
            if get_program_from_task(task).unwrap() == get_program_from_task(prev_task).unwrap() {
                1
            } else {
                0
            };
    }
    exec_scopes.insert_value(vars::TASK, task.clone());
    exec_scopes.insert_value(vars::USE_PREV_HASH, use_prev_hash);
    exec_scopes.insert_value(vars::PROGRAM_HASH_FUNCTION, program_hash_function);

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
        &format!("high{index}"),
        high_felt,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(&format!("low{index}"), low_felt, vm, ids_data, ap_tracking)?;

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
    // s is not allowed to be 0 in a valid signature, so the inverse always exists.
    if s == Felt252::from(0u8) {
        return Err(HintError::CustomHint("signature_s cannot be zero".into()));
    }
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
    use crate::hints::fact_topologies::FactTopology;
    use crate::hints::types::{Cairo0Executable, Task, TaskSpec};
    use crate::hints::vars;
    use crate::test_utils::prepare_ids_data_for_test;
    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::insert_value_from_var_name;
    use cairo_vm::hint_processor::hint_processor_definition::HintReference;
    use cairo_vm::serde::deserialize_program::ApTracking;
    use cairo_vm::types::exec_scope::ExecutionScopes;
    use cairo_vm::types::program::Program;
    use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
    use cairo_vm::vm::errors::hint_errors::HintError;
    use cairo_vm::vm::runners::builtin_runner::BuiltinRunner;
    use cairo_vm::vm::vm_core::VirtualMachine;
    use cairo_vm::Felt252;
    use num_traits::ToPrimitive;
    use rstest::{fixture, rstest};
    use starknet_crypto::{Felt, Signature};
    use std::collections::HashMap;

    use super::*;

    type SimulateBuiltinFn = fn(
        &mut VirtualMachine,
        &HashMap<String, HintReference>,
        &ApTracking,
    ) -> Result<(), HintError>;

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
    fn simple_bootloader_input(fibonacci: Program) -> SimpleBootloaderInput {
        let fib_cairo0_exec = Cairo0Executable {
            program: fibonacci.clone(),
            program_input: None,
        };
        SimpleBootloaderInput {
            fact_topologies_path: None,
            single_page: false,
            tasks: vec![
                TaskSpec {
                    task: Task::Cairo0Program(fib_cairo0_exec.clone()),
                    program_hash_function: HashFunc::Poseidon,
                },
                TaskSpec {
                    task: Task::Cairo0Program(fib_cairo0_exec),
                    program_hash_function: HashFunc::Poseidon,
                },
            ],
        }
    }

    /// This test checks that set_tasks_variable hint correctly sets the tasks variable
    /// in the execution scopes to be equal to the tasks in the SimpleBootloaderInput.
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

    /// This test checks that divide_num_by_2 hint correctly divides the number by 2
    /// and stores the result in the AP.
    #[rstest]
    #[case(128u128, 64u128)]
    #[case(1001u128, 500u128)]
    fn test_divide_num_by_2(#[case] num: u128, #[case] expected: u128) {
        let num_felt = Felt252::from(num);
        let expected_num_felt = Felt252::from(expected);

        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(1);
        vm.set_fp(1);

        let ids_data = prepare_ids_data_for_test(&["num"]);
        let ap_tracking = ApTracking::new();

        insert_value_from_var_name("num", num_felt, &mut vm, &ids_data, &ap_tracking).unwrap();

        divide_num_by_2(&mut vm, &ids_data, &ap_tracking).expect("Hint failed unexpectedly");

        let divided_num = vm.segments.memory.get_integer(vm.get_ap()).unwrap();
        assert_eq!(divided_num.into_owned(), expected_num_felt);
    }

    /// This test checks that set_current_task hint correctly sets the current task
    /// in the execution scopes based on the number of remaining tasks.
    /// It tests two cases:
    /// 1. When there is only one task, it should set the first task and use_prev_hash to 1.
    /// 2. When there are two tasks, it should set the second task and use_prev_hash to 0.
    #[rstest]
    #[case::n_tasks_1(1, 0)]
    #[case::n_tasks_2(2, 1)]
    fn test_set_current_task(
        simple_bootloader_input: SimpleBootloaderInput,
        #[case] n_tasks: usize,
        #[case] expected_task_idx: usize,
    ) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(2);
        vm.set_ap(2);
        let _ = vm
            .load_data(
                Relocatable::from((1, 0)),
                &[MaybeRelocatable::from(n_tasks)], // n_tasks
            )
            .unwrap();

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(
            vars::SIMPLE_BOOTLOADER_INPUT,
            simple_bootloader_input.clone(),
        );

        let ids_data = prepare_ids_data_for_test(&["n_tasks", "task"]);
        let ap_tracking = ApTracking::new();

        set_current_task(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that `task` is set
        let task: Task = exec_scopes
            .get(vars::TASK)
            .expect("task variable is not set.");

        // Check that the task is the expected one in the input
        let expected_task = simple_bootloader_input.tasks[expected_task_idx].load_task();
        assert_eq!(&task, expected_task);

        // Check that the program hash function is set
        let program_hash_function: HashFunc = exec_scopes
            .get(vars::PROGRAM_HASH_FUNCTION)
            .expect("program_hash_function variable is not set.");
        assert_eq!(
            program_hash_function,
            simple_bootloader_input.tasks[expected_task_idx].program_hash_function
        );

        // Assert that `use_prev_hash` is set only when n_tasks <= 1
        // This means that we are not working with the first task - so we can use a previous hash.
        let use_prev_hash: i32 = exec_scopes
            .get(vars::USE_PREV_HASH)
            .expect("use_prev_hash variable is not set.");
        if n_tasks > 1 {
            assert_eq!(use_prev_hash, 0);
        } else {
            assert_eq!(use_prev_hash, 1);
        }
    }

    /// This test checks that setup_run_simple_bootloader_before_task_execution hint functions
    /// correctly. We expect the following result:
    /// 1. Write the number of tasks into `output_ptr[0]`.
    /// 2. Set `initial_subtasks_range_check_ptr` to a new temporary segment.
    /// 3. Initialize the `fact_topologies` hint variable to an empty array.
    #[rstest]
    fn test_setup_run_simple_bootloader_before_task_execution(
        simple_bootloader_input: SimpleBootloaderInput,
    ) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment(); // Temporary segment for initial_subtasks_range_check_ptr
        vm.set_ap(2);
        vm.set_fp(2);

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(
            vars::SIMPLE_BOOTLOADER_INPUT,
            simple_bootloader_input.clone(),
        );

        // Load output_ptr addr to execution scopes memory
        // We assume that output_ptr points to (2,0)
        let _ = vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from((2, 0)), // Number of tasks
            ],
        );

        let ids_data =
            prepare_ids_data_for_test(&["output_ptr", "initial_subtasks_range_check_ptr"]);
        let ap_tracking = ApTracking::new();

        setup_run_simple_bootloader_before_task_execution(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
        )
        .expect("Hint failed unexpectedly");

        // Check that output_ptr is set correctly. We expect it to be (2,0) with the number of
        // tasks.
        assert_eq!(
            vm.get_integer(Relocatable::from((2, 0)))
                .unwrap()
                .into_owned(),
            Felt252::from(simple_bootloader_input.tasks.len())
        );

        // Check that initial_subtasks_range_check_ptr is set to a new temporary segment. We expect
        // it to be (-1,0).
        let temp_range_check_address = vm
            .get_relocatable(Relocatable::from((1, 1)))
            .expect("Failed to get temp_range_check_ptr");
        assert_eq!(temp_range_check_address, Relocatable::from((-1, 0)));

        // Check that fact_topologies is initialized to an empty array.
        let fact_topologies: Vec<FactTopology> = exec_scopes.get(vars::FACT_TOPOLOGIES).unwrap();
        assert!(fact_topologies.is_empty());
    }

    /// This test checks that set_ap_to_zero hint sets the AP to zero.
    #[test]
    fn test_set_ap_to_zero() {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(1);

        set_ap_to_zero(&mut vm).expect("Hint failed unexpectedly");
        assert_eq!(
            vm.get_integer(vm.get_ap())
                .expect("Failed to get AP")
                .into_owned(),
            Felt252::from(0)
        );
    }

    /// This test checks that program_hash_function_to_ap hint sets the AP to the program hash
    /// function value of the current task.
    #[rstest]
    fn test_program_hash_function_to_ap(simple_bootloader_input: SimpleBootloaderInput) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(1);

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(
            vars::PROGRAM_HASH_FUNCTION,
            simple_bootloader_input.tasks[0].program_hash_function,
        );

        program_hash_function_to_ap(&mut vm, &mut exec_scopes).expect("Hint failed unexpectedly");

        let program_hash_function: usize = vm
            .get_integer(vm.get_ap())
            .expect("Failed to get AP")
            .to_usize()
            .expect("Failed to convert Felt252 to usize");
        assert_eq!(
            program_hash_function,
            simple_bootloader_input.tasks[0].program_hash_function as usize
        );
    }

    /// This function prepares a VirtualMachine instance for testing simulate_builtin hints.
    fn prepare_vm_for_simulate_builtin(
        builtin_name: &str,
    ) -> (VirtualMachine, HashMap<String, HintReference>) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(1);
        vm.set_fp(1);

        let ids_data = prepare_ids_data_for_test(&[&format!("new_{}_ptr", builtin_name)]);
        (vm, ids_data)
    }

    /// This test checks that simple_bootloader_simulate_<<builtin_name>> {ec_op, keccak, ecdsa}
    /// hints correctly initializes the builtin runner and sets the new_builtin_ptr to a
    /// new temporary segment.
    #[rstest]
    #[case("ec_op", simple_bootloader_simulate_ec_op)]
    #[case("keccak", simple_bootloader_simulate_keccak)]
    #[case("ecdsa", simple_bootloader_simulate_ecdsa)]
    fn test_simple_bootloader_simulate_builtin_runner(
        #[case] builtin_name: &str,
        #[case] simulate_builtin_fn: SimulateBuiltinFn,
    ) {
        let (mut vm, ids_data) = prepare_vm_for_simulate_builtin(builtin_name);
        let ap_tracking = ApTracking::new();

        simulate_builtin_fn(&mut vm, &ids_data, &ap_tracking).expect("Hint failed unexpectedly");

        // Check that new_builtin_ptr is set to a new segment - should be (2,0) since we previous
        // allocated two segments.
        let new_builtin_ptr = vm
            .get_relocatable(Relocatable::from((1, 0)))
            .expect("Failed to get new_builtin_ptr");
        assert_eq!(new_builtin_ptr, Relocatable::from((2, 0)));

        // Check that the builtin runner is added to the simulated_builtin_runners and points at the
        // new segment.
        let runner = vm
            .simulated_builtin_runners
            .last()
            .expect("No simulated builtin runners found");

        match runner {
            BuiltinRunner::EcOp(runner) if builtin_name == "ec_op" => {
                assert_eq!(runner.base, 2);
            }
            BuiltinRunner::Keccak(runner) if builtin_name == "keccak" => {
                assert_eq!(runner.base, 2);
            }
            BuiltinRunner::Signature(runner) if builtin_name == "ecdsa" => {
                assert_eq!(runner.base, 2);
            }
            _ => panic!(
                "Expected {} BuiltinRunner, found {:?}",
                builtin_name, runner
            ),
        }
    }

    /// This function calculates the bit unpacking of m and asserts that the VM memory at
    /// (segment, offset) matches (LSB first). For example, if m = 10 (binary 1010) and
    /// num_bits = 4, We expect the memory to be filled like so: (2, 0) -> 0, (2, 1) ->
    /// 1, (2, 2) -> 0, (2, 3) -> 1
    fn assert_vm_bit_unpacking_matches(
        vm: &VirtualMachine,
        m: u64,
        segment: isize,
        offset: usize,
        num_bits: usize,
    ) {
        // Calculate expected bits (LSB first)
        let mut expected_bits = Vec::with_capacity(num_bits);
        let mut value = m;
        for _ in 0..num_bits {
            expected_bits.push((value & 1) as u8);
            value >>= 1;
        }

        // Assert each bit in VM memory matches expected
        for (i, &expected_bit) in expected_bits.iter().enumerate() {
            let actual = vm
                .get_integer(Relocatable::from((segment, i + offset)))
                .expect("Failed to get bit from VM")
                .into_owned();
            assert_eq!(
                actual,
                Felt252::from(expected_bit),
                "Bit at index {} does not match",
                i
            );
        }
    }

    /// This test checks that simulate_ec_op_fill_mem_with_bits_of_m hint correctly fills the
    /// memory with bits of m.
    /// For example, if m = 10 (binary 1010) and num_bits = 4,
    /// we expect the memory to be filled with [0, 1, 0, 1] (LSB first).
    /// If m = 15 (binary 1111) and num_bits = 4,
    /// we expect the memory to be filled with [1, 1, 1, 1] (LSB first).
    #[rstest]
    #[case(10u64, 4)]
    #[case(15u64, 4)]
    #[case(255u64, 8)]
    #[case(1023u64, 10)]
    #[case(0u64, 10)]
    #[case(1u64, 12)]
    fn test_simulate_ec_op_fill_mem_with_bits_of_m(#[case] m: u64, #[case] num_bits: usize) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment(); // Segment for m_bit_unpacking
        vm.set_ap(2);
        vm.set_fp(2);

        let ids_data = prepare_ids_data_for_test(&["m", "m_bit_unpacking"]);
        let ap_tracking = ApTracking::new();

        // Set m and m_bit_unpacking to (2,0)
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from(Felt252::from(m)),
                MaybeRelocatable::from((2, 0)),
            ], // m, m_bit_unpacking
        )
        .expect("Failed to load m into memory");
        let mut constants = HashMap::new();
        constants.insert("M_MAX_BITS".to_string(), Felt252::from(num_bits));
        simulate_ec_op_fill_mem_with_bits_of_m(&mut vm, &ids_data, &ap_tracking, &constants)
            .expect("Hint failed unexpectedly");

        assert_vm_bit_unpacking_matches(&vm, m, 2, 0, num_bits);
    }

    /// This test checks that simulate_ec_op_assert_false hint raises a HintError with the
    /// expected message "ec_op failed.".
    #[test]
    fn test_simulate_ec_op_assert_false() {
        let result = simulate_ec_op_assert_false();
        assert!(result.is_err());
        match result {
            Err(HintError::CustomHint(msg)) => assert_eq!(msg, "ec_op failed.".to_string().into()),
            _ => panic!("Expected a HintError with custom message, got {:?}", result),
        }
    }

    /// This test checks that simulate_keccak_fill_mem_with_state hint correctly fills the memory
    /// with the keccak state. We provide a known keccak state and the expected felts after
    /// processing. The expected felts are calculated based on the keccak state representation.
    ///
    /// The following python code was used to calculate the expected felts:
    /// ```python
    /// def keccak_state_to_felts(state):
    ///     full_num = 0
    ///     for i, s in enumerate(state):
    ///         full_num += s << (i * 200)
    ///     felts = []
    ///     for _ in range(25):
    ///         felts.append(full_num % (2**64))
    ///         full_num >>= 64
    ///     return felts
    /// ```
    #[rstest]
    #[case([0u64; 8], [0u64; 25])]
    #[case([1u64; 8], [1, 0, 0, 256, 0, 0, 65536, 0, 0, 16777216, 0, 0, 4294967296, 0, 0, 1099511627776, 0, 0, 281474976710656, 0, 0, 72057594037927936, 0, 0, 0])]
    #[case([0xFFFFFFFFFFFFFFFFu64; 8], [18446744073709551615, 0, 0, 18446744073709551360, 255, 0, 18446744073709486080, 65535, 0, 18446744073692774400, 16777215, 0, 18446744069414584320, 4294967295, 0, 18446742974197923840, 1099511627775, 0, 18446462598732840960, 281474976710655, 0, 18374686479671623680, 72057594037927935, 0, 0])]
    #[case([0,1,2,3,4,5,6,7],[0, 0, 0, 256, 0, 0, 131072, 0, 0, 50331648, 0, 0, 17179869184, 0, 0, 5497558138880, 0, 0, 1688849860263936, 0, 0, 504403158265495552, 0, 0, 0])]
    fn test_simulate_keccak_fill_mem_with_state(
        #[case] state: [u64; 8],
        #[case] expected_felts: [u64; 25],
    ) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment(); // Segment for felt_array
        vm.set_ap(2);
        vm.set_fp(2);

        let ids_data = prepare_ids_data_for_test(&["felt_array", "keccak_builtin_state"]);
        let ap_tracking = ApTracking::new();

        // Set keccak_builtin_state to (1,0) and felt_array to (2,0)
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from((2, 0)), // felt_array
            ],
        )
        .expect("Failed to load addresses into memory");

        // Load the keccak state into memory at (2,0)
        let keccak_state_data: Vec<MaybeRelocatable> = state
            .iter()
            .map(|&x| MaybeRelocatable::from(Felt252::from(x)))
            .collect();
        vm.load_data(Relocatable::from((1, 1)), &keccak_state_data)
            .expect("Failed to load keccak state into memory");

        simulate_keccak_fill_mem_with_state(&mut vm, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Assert that the felt_array is filled correctly
        for (i, &expected) in expected_felts.iter().enumerate() {
            let actual = vm
                .get_integer(Relocatable::from((2, i)))
                .expect("Failed to get felt from VM")
                .into_owned();
            assert_eq!(
                actual,
                Felt252::from(expected),
                "Felt at index {} does not match",
                i
            );
        }
    }

    /// This test checks that simulate_keccak_calc_high_low hint correctly calculates the high
    /// and low values from the felt_array at the given index.
    /// The test cases were genrated using the following python code:
    /// ```python
    /// def calc_high_low(index):
    ///          # The test value used in Rust: 0x123456789ABCDEF + index
    ///          test_value = 0x123456789ABCDEF + index
    ///          x = index // 3
    ///          divisor = 1 << (x * 8)
    ///          high = test_value // divisor
    ///          low = test_value % divisor
    ///          return high, low
    ///
    ///     # Indices from your test cases
    ///     indices = [3,6,9,12,15,18,21]
    ///
    ///     for idx in indices:
    ///         high, low = calc_high_low(idx)
    ///         print(f"#[case({idx}, {high}, {low})]
    /// ```
    #[rstest]
    #[case(3, 320255973501901, 242)]
    #[case(6, 1250999896491, 52725)]
    #[case(9, 4886718345, 11259384)]
    #[case(12, 19088743, 2309737979)]
    #[case(15, 74565, 444691369470)]
    #[case(18, 291, 76310993686017)]
    #[case(21, 1, 9927935178558980)]
    fn test_simulate_keccak_calc_high_low(
        #[case] index: usize,
        #[case] expected_high: u64,
        #[case] expected_low: u64,
    ) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment(); // Segment for felt_array
        vm.set_ap(3);
        vm.set_fp(3);

        let ids_data = prepare_ids_data_for_test(&[
            "felt_array",
            &format!("high{index}"),
            &format!("low{index}"),
        ]);
        let ap_tracking = ApTracking::new();

        // Set felt_array to (2,0)
        vm.load_data(
            Relocatable::from((1, 0)),
            &[MaybeRelocatable::from((2, 0))], // felt_array
        )
        .expect("Failed to load addresses into memory");

        // Load a test value into felt_array at the given index
        let test_value = Felt252::from(0x123456789ABCDEFu64 + index as u64);
        vm.load_data(
            Relocatable::from((2, index)),
            &[MaybeRelocatable::from(test_value)],
        )
        .expect("Failed to load test value into felt_array");

        simulate_keccak_calc_high_low(&mut vm, &ids_data, &ap_tracking, index)
            .expect("Hint failed unexpectedly");

        // Assert that the high and low values are set correctly in the VM
        let actual_high = vm
            .get_integer(Relocatable::from((1, 1))) // high is stored at AP - 2
            .expect("Failed to get high from VM")
            .into_owned();

        let actual_low = vm
            .get_integer(Relocatable::from((1, 2))) // low is stored at AP - 1
            .expect("Failed to get low from VM")
            .into_owned();

        assert_eq!(
            actual_high,
            Felt252::from(expected_high),
            "High value does not match for index {}",
            index
        );
        assert_eq!(
            actual_low,
            Felt252::from(expected_low),
            "Low value does not match for index {}",
            index
        );
    }

    /// This test checks that simulate_ecdsa_get_r_and_s hint correctly retrieves the r and s
    /// values from the signature builtin additional data for the given start pointer.
    /// We also check that these values are correctly set in the VM memory.
    #[rstest]
    fn test_simulate_ecdsa_get_r_and_s() {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(3);
        vm.set_fp(3);

        let ids_data = prepare_ids_data_for_test(&["start", "r", "s"]);
        let ap_tracking = ApTracking::new();

        // Set start to (1,0)
        vm.load_data(
            Relocatable::from((1, 0)),
            &[MaybeRelocatable::from((1, 0))], // start
        )
        .expect("Failed to load start into memory");

        // Add signature builtin runner and set a signature for (1,0)
        let mut ecdsa_runner = SignatureBuiltinRunner::new(Some(1), false);
        ecdsa_runner.initialize_segments(&mut vm.segments);
        let start_ptr = Relocatable {
            segment_index: 1,
            offset: 0,
        };
        let r =
            Felt::from_hex("0x123456789ABCDEF123456789ABCDEF123456789ABCDEF123456789ABCDEF1234")
                .unwrap();
        let s =
            Felt::from_hex("0xFEDCBA9876543210FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210")
                .unwrap();
        {
            let mut signatures = ecdsa_runner.signatures.borrow_mut();
            signatures.insert(start_ptr, Signature { r, s });
        }
        vm.simulated_builtin_runners.push(ecdsa_runner.into());

        simulate_ecdsa_get_r_and_s(&mut vm, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Assert that r and s are set correctly in the VM
        let actual_r = vm
            .get_integer(Relocatable::from((1, 1))) // r is stored at AP - 2
            .expect("Failed to get r from VM")
            .into_owned();
        let actual_s = vm
            .get_integer(Relocatable::from((1, 2))) // s is stored at AP - 1
            .expect("Failed to get s from VM")
            .into_owned();
        let expected_r = Felt252::from_bytes_be(&r.to_bytes_be());
        let expected_s = Felt252::from_bytes_be(&s.to_bytes_be());
        assert_eq!(actual_r, expected_r, "r value does not match");
        assert_eq!(actual_s, expected_s, "s value does not match");
    }

    /// This test checks that simulate_ecdsa_compute_w_wr_wz hint correctly computes the values of
    /// w, wr, and wz based on the provided signature_r, signature_s, and message.
    /// We use a small prime order for the elliptic curve to simplify calculations.
    /// The test cases were generated using the following python code:
    /// ```python
    /// def modinv(a, n):
    ///     # Extended Euclidean Algorithm for modular inverse
    ///     t, newt = 0, 1
    ///     r, newr = n, a
    ///     while newr != 0:
    ///         quotient = r // newr
    ///         t, newt = newt, t - quotient * newt
    ///         r, newr = newr, r - quotient * newr
    ///     if r > 1:
    ///         raise Exception("No inverse")
    ///     if t < 0:
    ///         t += n
    ///     return t
    ///
    /// ORDER = 13
    /// cases = [
    ///     (1, 2, 3),
    ///     (2, 3, 4),
    ///     (3, 4, 5),
    ///     (4, 5, 6),
    ///     (5, 6, 7),
    /// ]
    ///
    /// for signature_r, signature_s, message in cases:
    ///     w = modinv(signature_s, ORDER)
    ///     wr = (w * signature_r) % ORDER
    ///     wz = (w * message) % ORDER
    ///     print(f"#[case({signature_r}, {signature_s}, {message}, {w}, {wr}, {wz})]")
    /// ``
    #[rstest]
    #[case(1, 2, 3, 7, 7, 8)]
    #[case(2, 3, 4, 9, 5, 10)]
    #[case(3, 4, 5, 10, 4, 11)]
    #[case(4, 5, 6, 8, 6, 9)]
    #[case(5, 6, 7, 11, 3, 12)]
    fn test_simulate_ecdsa_compute_w_wr_wz(
        #[case] signature_r: usize,
        #[case] signature_s: usize,
        #[case] message: usize,
        #[case] expected_w: usize,
        #[case] expected_wr: usize,
        #[case] expected_wz: usize,
    ) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(6);
        vm.set_fp(6);
        let ids_data =
            prepare_ids_data_for_test(&["signature_r", "signature_s", "message", "w", "wr", "wz"]);
        let ap_tracking = ApTracking::new();
        let mut constants = HashMap::new();
        constants.insert(
            "starkware.cairo.common.ec.StarkCurve.ORDER".to_string(),
            Felt252::from(13u8),
        );
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from(Felt252::from(signature_r)), // signature_r
                MaybeRelocatable::from(Felt252::from(signature_s)), // signature_s
                MaybeRelocatable::from(Felt252::from(message)),     // message
            ],
        )
        .expect("Failed to load data into memory");

        simulate_ecdsa_compute_w_wr_wz(&mut vm, &ids_data, &ap_tracking, &constants)
            .expect("Hint failed unexpectedly");

        let actual_w = vm
            .get_integer(Relocatable::from((1, 3))) // w is stored at AP - 2
            .expect("Failed to get w from VM")
            .into_owned();
        let actual_wr = vm
            .get_integer(Relocatable::from((1, 4))) // wr is stored at AP - 1
            .expect("Failed to get wr from VM")
            .into_owned();
        let actual_wz = vm
            .get_integer(Relocatable::from((1, 5))) // wz is stored at AP
            .expect("Failed to get wz from VM")
            .into_owned();
        assert_eq!(
            actual_w,
            Felt252::from(expected_w),
            "w value does not match"
        );
        assert_eq!(
            actual_wr,
            Felt252::from(expected_wr),
            "wr value does not match"
        );
        assert_eq!(
            actual_wz,
            Felt252::from(expected_wz),
            "wz value does not match"
        );
    }

    /// This test checks that simulate_ecdsa_compute_w_wr_wz fails when signature_s is zero.
    /// Since the hint calculates s^-1 mod ORDER, having s=0 should raise an error.
    #[test]
    fn test_simulate_ecdsa_compute_w_wr_wz_fails_when_s_is_zero() {
        // This test checks that simulate_ecdsa_compute_w_wr_wz fails when signature_s is zero.
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(6);
        vm.set_fp(6);
        let ids_data =
            prepare_ids_data_for_test(&["signature_r", "signature_s", "message", "w", "wr", "wz"]);
        let ap_tracking = ApTracking::new();
        let mut constants = HashMap::new();
        constants.insert(
            "starkware.cairo.common.ec.StarkCurve.ORDER".to_string(),
            Felt252::from(13u8),
        );
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from(Felt252::from(1)), // signature_r
                MaybeRelocatable::from(Felt252::from(0)), // signature_s = 0
                MaybeRelocatable::from(Felt252::from(1)), // message
            ],
        )
        .expect("Failed to load data into memory");

        let result = simulate_ecdsa_compute_w_wr_wz(&mut vm, &ids_data, &ap_tracking, &constants);
        assert!(result.is_err(), "Expected error when signature_s is zero");
    }

    /// This test checks that simulate_ecdsa_fill_mem_with_felt_96_bit_limbs hint correctly
    /// fills the memory with the 96-bit limbs of the given number.
    /// The test cases were generated using the following python code:
    /// ```python
    ///     import random
    ///
    /// FELT252_PRIME = 2**251 + 17 * 2**192 + 1
    ///
    /// def felt252_mod(n: int) -> int:
    ///     return n % FELT252_PRIME
    ///
    /// def extract_96_bit_limbs(n: int):
    ///     n = felt252_mod(n)
    ///     limbs = []
    ///     for _ in range(3):
    ///         limbs.append(n & ((1 << 96) - 1))
    ///         n >>= 96
    ///     return limbs
    ///
    /// def print_test_case(num_bytes: bytes):
    ///     n = int.from_bytes(num_bytes, "big")
    ///     limbs = extract_96_bit_limbs(n)
    ///     print(f"#[case(Felt252::from(BigUint::from_bytes_be(&[{', '.join(str(b) for b in num_bytes)}])), [{', '.join(str(limb) for limb in limbs)}])]")
    ///
    /// # Example test cases
    /// test_cases = [
    ///     bytes([0]),  # Zero
    ///     bytes([1]),  # One
    ///     FELT252_PRIME.to_bytes(32, "big"),  # Felt252 prime (should wrap to zero)
    ///     (FELT252_PRIME - 1).to_bytes(32, "big"),  # Felt252 prime - 1
    ///     (2**96 - 1).to_bytes(12, "big"),  # Max single limb
    ///     random.getrandbits(252).to_bytes(32, "big"),  # Random 252-bit value
    ///     random.getrandbits(251).to_bytes(32, "big"),  # Random 251-bit value
    ///     random.getrandbits(200).to_bytes(25, "big"),  # Random 200-bit value
    ///     bytes([18, 52, 86, 120, 154, 188, 222, 241, 35, 69, 103, 137, 171, 205, 239, 18, 52, 86, 120, 154, 188, 222, 241, 35, 69, 103, 137, 171, 205, 239, 18, 52]),  # Provided example
    /// ]
    ///
    /// for num_bytes in test_cases:
    ///     print_test_case(num_bytes)
    /// ```
    #[rstest]
    #[case(Felt252::from(BigUint::from_bytes_be(&[0])), [0, 0, 0])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[1])), [1, 0, 0])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[8, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])), [0, 0, 0])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[8, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])), [0, 0, 576460752303423505])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])), [79228162514264337593543950335, 0, 0])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[14, 252, 118, 170, 245, 122, 158, 182, 162, 154, 92, 157, 173, 9, 88, 5, 198, 199, 181, 141, 251, 190, 183, 126, 178, 120, 130, 59, 137, 237, 180, 178])), [77911299901100682153777018033, 50323183533602391431263532429, 503407734993624741])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[4, 221, 180, 118, 244, 232, 39, 199, 28, 193, 142, 152, 230, 233, 138, 23, 80, 178, 157, 130, 15, 146, 13, 122, 182, 161, 123, 45, 89, 5, 75, 122])), [4818841971410901209182456698, 8899576354767934179524124034, 350634769012762567])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[74, 67, 205, 139, 5, 241, 171, 54, 11, 16, 39, 147, 128, 11, 112, 36, 235, 76, 173, 126, 50, 209, 100, 52, 132])), [3539909145535085927091942532, 20983981969640029639909282688, 74])]
    #[case(Felt252::from(BigUint::from_bytes_be(&[18, 52, 86, 120, 154, 188, 222, 241, 35, 69, 103, 137, 171, 205, 239, 18, 52, 86, 120, 154, 188, 222, 241, 35, 69, 103, 137, 171, 205, 239, 18, 52])), [58452702119326852043580052018, 10915880168631974302265538714, 158846962856943311])]
    fn test_simulate_ecdsa_fill_mem_with_felt_96_bit_limbs(
        #[case] num: Felt252,
        #[case] expected: [u128; 3],
    ) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment(); // Segment for limbs
        vm.set_ap(2);
        vm.set_fp(2);
        println!("num as hex: 0x{}", num.to_biguint().to_str_radix(16));
        let ids_data = prepare_ids_data_for_test(&["num", "res_96_felts"]);
        let ap_tracking = ApTracking::new();

        // Set num and limbs to (2,0)
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from(num),    // num
                MaybeRelocatable::from((2, 0)), // limbs
            ],
        )
        .expect("Failed to load num into memory");

        simulate_ecdsa_fill_mem_with_felt_96_bit_limbs(&mut vm, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Assert that the limbs are filled correctly
        for (i, &expected_limb) in expected.iter().enumerate() {
            let actual = vm
                .get_integer(Relocatable::from((2, i)))
                .expect("Failed to get limb from VM")
                .into_owned();
            assert_eq!(
                actual,
                Felt252::from(expected_limb),
                "Limb at index {} does not match",
                i
            );
        }
    }
}
