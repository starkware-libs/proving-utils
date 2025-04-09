use std::collections::HashMap;

use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{
            get_integer_from_var_name, get_ptr_from_var_name, insert_value_into_ap,
        },
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::exec_scope::ExecutionScopes,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
    Felt252,
};
use num_traits::ToPrimitive;

use super::{types::PedersenMerkleInput, PROGRAM_INPUT};
const AUTH_PATH: &str = "auth_path";

/// Implements hint:
/// %{
///     ids.output.height = program_input['height']
///     ids.output.prev_leaf = int(program_input['prev_leaf'], 16)
///     ids.output.new_leaf = int(program_input['new_leaf'], 16)
///     ids.output.node_index = program_input['node_index']
///
///     auth_path = [int(x, 16) for x in program_input['path']][::-1]
/// %}
/// Note: output is a ptr of type:
///       struct PedersenOutput {
///           height: felt,
///           prev_leaf: felt,
///           new_leaf: felt,
///           node_index: felt,
///       }
pub fn pedersen_merkle_load_input(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;
    let pedersen_merkle_input: PedersenMerkleInput = serde_json::from_str(program_input).unwrap();
    let output = get_ptr_from_var_name("output", vm, ids_data, ap_tracking)?;
    vm.insert_value(output, pedersen_merkle_input.height)?;
    vm.insert_value((output + 1)?, pedersen_merkle_input.prev_leaf)?;
    vm.insert_value((output + 2)?, pedersen_merkle_input.new_leaf)?;
    vm.insert_value(
        (output + 3)?,
        Felt252::from_dec_str(&pedersen_merkle_input.node_index.to_string()).map_err(|_| {
            HintError::CustomHint("Failed to convert node_index to Felt252.".into())
        })?,
    )?;
    let reversed_path: Vec<Felt252> = pedersen_merkle_input.path.into_iter().rev().collect();
    exec_scopes.insert_value(AUTH_PATH, reversed_path);
    Ok(())
}

/// Implements hint:
/// %{
///     # Check that auth_path had the right number of elements.
///     assert len(auth_path) == 0, 'Got too many values in auth_path.'
/// %}
pub fn pedersen_merkle_verify_auth_path_len(
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let auth_path: &Vec<Felt252> = exec_scopes.get_ref(AUTH_PATH)?;
    if !auth_path.is_empty() {
        return Err(HintError::CustomHint(
            "Got too many values in auth_path.".into(),
        ));
    }
    Ok(())
}

/// Implements hint: %{ memory[ap] = ids.index % 2 %}
pub fn pedersen_merkle_idx_parity_to_ap(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let index = get_integer_from_var_name("index", vm, ids_data, ap_tracking)?
        .to_u128()
        .ok_or_else(|| HintError::CustomHint("Failed to convert index to u128.".into()))?;
    insert_value_into_ap(vm, (index % 2) as usize)
}

/// Implements hint:
/// %{
///     # Hash hints.
///     sibling = auth_path.pop()
///     ids.prev_node_hash.y = sibling
///     ids.new_node_hash.y = sibling
/// %}
/// OR
/// %{
///     # Hash hints.
///     sibling = auth_path.pop()
///     ids.prev_node_hash.x = sibling
///     ids.new_node_hash.x = sibling
/// %}
/// The choice between y and x is flagged by the `is_left` boolean.
pub fn pedersen_merkle_update(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    is_left: bool,
) -> Result<(), HintError> {
    let auth_path: &mut Vec<Felt252> = exec_scopes.get_mut_ref(AUTH_PATH)?;
    let sibling = auth_path.pop().ok_or_else(|| {
        HintError::CustomHint("auth_path is empty. Cannot pop a sibling value.".into())
    })?;

    let prev_node_hash_ptr = get_ptr_from_var_name("prev_node_hash", vm, ids_data, ap_tracking)?;
    let new_node_hash_ptr = get_ptr_from_var_name("new_node_hash", vm, ids_data, ap_tracking)?;

    let is_left_usize = is_left as usize;
    vm.insert_value((prev_node_hash_ptr + is_left_usize)?, sibling)?;
    vm.insert_value((new_node_hash_ptr + is_left_usize)?, sibling)?;
    Ok(())
}
