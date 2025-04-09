use cairo_vm::{
    hint_processor::builtin_hint_processor::hint_utils::insert_value_into_ap,
    types::exec_scope::ExecutionScopes,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
};

use super::{types::FibonacciInput, PROGRAM_INPUT};

const FIBONACCI_CLAIM_INDEX: &str = "fibonacci_claim_index";

/// Implements hint: %{ memory[ap] = program_input['second_element'] %}
pub fn fibonacci_load_second_element(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;
    let fibonacci_input: FibonacciInput = serde_json::from_str(program_input).unwrap();
    exec_scopes.insert_value(FIBONACCI_CLAIM_INDEX, fibonacci_input.fibonacci_claim_index);
    insert_value_into_ap(vm, fibonacci_input.second_element)
}

/// Implements hint: %{ memory[ap] = program_input['fibonacci_claim_index'] %}
pub fn fibonacci_load_claim_idx(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let fibonacci_claim_index: usize = exec_scopes.get(FIBONACCI_CLAIM_INDEX)?;
    insert_value_into_ap(vm, fibonacci_claim_index)
}
