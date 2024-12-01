use std::{any::Any, collections::HashMap};

use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{insert_value_from_var_name, insert_value_into_ap},
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::exec_scope::ExecutionScopes,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
    Felt252,
};

use crate::maybe_relocatable_box;
use cairo_vm::types::relocatable::MaybeRelocatable;

use super::{
    types::MockCairoVerifierInput, utils::gen_arg, vars::MOCK_CAIRO_VERIFIER_INPUT, PROGRAM_INPUT,
};

/// Implements
/// %{
///     from starkware.cairo.cairo_verifier.mock_cairo_verifier_input import MockCairoVerifierInput
///
///     # Get output to apply hash state.
///     mock_cairo_verifier_input = MockCairoVerifierInput.load(program_input)
///     program_hash = mock_cairo_verifier_input.program_hash
///     program_output = mock_cairo_verifier_input.program_output
///     ids.output = segments.gen_arg(program_output)
/// %}
pub fn load_mock_cairo_verifier_input(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;
    let mock_cairo_verifier_input: MockCairoVerifierInput =
        serde_json::from_str(program_input).unwrap();
    let converted_args: Vec<Box<dyn Any>> = mock_cairo_verifier_input
        .program_output
        .iter()
        .map(|item| maybe_relocatable_box!(*item))
        .collect();
    let output_base = gen_arg(vm, &converted_args)?;
    insert_value_from_var_name("output", output_base, vm, ids_data, ap_tracking)?;
    exec_scopes.insert_value(MOCK_CAIRO_VERIFIER_INPUT, mock_cairo_verifier_input);
    Ok(())
}

/// Implements local output_len = nondet %{ len(program_output) %}
/// Compiles to: memory[fp + 1] = to_felt_or_relocatable(len(program_output))
pub fn mock_cairo_verifier_len_output_to_fp(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let mock_cairo_verifier_input: &MockCairoVerifierInput =
        exec_scopes.get_ref(MOCK_CAIRO_VERIFIER_INPUT)?;
    let output_len = mock_cairo_verifier_input.program_output.len();

    // Insert output_len into memory at `fp + 1`
    let dest = (vm.get_fp() + 1)?;
    Ok(vm.insert_value(dest, output_len)?)
}

/// Implements local program_hash = nondet %{ program_hash %}
/// Compiles to: memory[fp + 2] = to_felt_or_relocatable(program_hash)
pub fn mock_cairo_verifier_hash_to_fp(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let mock_cairo_verifier_input: &MockCairoVerifierInput =
        exec_scopes.get_ref(MOCK_CAIRO_VERIFIER_INPUT)?;

    // Insert output_len into memory at `fp + 1`
    let dest = (vm.get_fp() + 2)?;
    Ok(vm.insert_value(dest, mock_cairo_verifier_input.program_hash)?)
}

/// Implements n_mock_steps=nondet %{ n_steps %}
/// Compiles to: memory[ap] = to_felt_or_relocatable(n_steps)
pub fn mock_cairo_verifier_n_steps_to_ap(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let mock_cairo_verifier_input: &MockCairoVerifierInput =
        exec_scopes.get_ref(MOCK_CAIRO_VERIFIER_INPUT)?;
    let felt_n_steps =
        Felt252::from_dec_str(&mock_cairo_verifier_input.n_steps.to_string()).unwrap();
    insert_value_into_ap(vm, felt_n_steps)
}
