use std::collections::HashMap;

use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{get_ptr_from_var_name, insert_value_into_ap},
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::{exec_scope::ExecutionScopes, relocatable::MaybeRelocatable},
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
    Felt252,
};

use super::{types::SimpleOutputInput, vars::SIMPLE_OUTPUT_INPUT, PROGRAM_INPUT};

/// Implements %{ output = program_input["output"] %}
pub fn load_simple_output_input(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;
    let simple_output_input: SimpleOutputInput = serde_json::from_str(program_input).unwrap();
    let output_as_maybe: Vec<MaybeRelocatable> = simple_output_input
        .output
        .iter()
        .map(|number| {
            let dec_str = number.to_string();
            Felt252::from_dec_str(&dec_str).unwrap().into()
        })
        .collect();
    exec_scopes.insert_value(SIMPLE_OUTPUT_INPUT, output_as_maybe);
    Ok(())
}

/// Implements %{ segments.write_arg(ids.output_ptr, output) %}
pub fn write_simple_output(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let simple_output_input: &Vec<MaybeRelocatable> = exec_scopes.get_ref(SIMPLE_OUTPUT_INPUT)?;
    let output = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    vm.write_arg(output, simple_output_input)
        .map_err(|_| HintError::CustomHint("Failed to write output of simple_output".into()))?;
    Ok(())
}

/// Implements nondet %{ len(output) %}
/// Compiles to: memory[ap] = to_felt_or_relocatable(len(output))
pub fn len_output_to_ap(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let simple_output_input: &Vec<MaybeRelocatable> = exec_scopes.get_ref(SIMPLE_OUTPUT_INPUT)?;
    let output_len = simple_output_input.len();
    insert_value_into_ap(vm, output_len)
}
