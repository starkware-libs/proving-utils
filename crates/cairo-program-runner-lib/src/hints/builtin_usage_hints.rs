use std::collections::HashMap;

use super::{
    execute_task_hints::field_element_to_felt, fact_topologies::GPS_FACT_TOPOLOGY,
    types::FlexibleBuiltinUsageInput, PROGRAM_INPUT,
};
use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{
            get_ptr_from_var_name, insert_value_from_var_name, insert_value_into_ap,
        },
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::exec_scope::ExecutionScopes,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
    Felt252,
};
use starknet_crypto::{pedersen_hash, FieldElement};

/// Implements hint:
/// %{
///     # Add a segment to test pie relocation in the bootloader.
///     ids.other_segment = segments.add()
///     segments.finalize(ids.other_segment.segment_index, size=1)
/// %}
///
/// OR
///
/// %{
///     # Add a segment to test pie relocation in the bootloader.
///     ids.other_segment = segments.add()
/// %}
/// Where the finalize part is flagged by the `finalize` boolean.
pub fn builtin_usage_add_other_segment(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    finalize: bool,
) -> Result<(), HintError> {
    let new_segment_base = vm.add_memory_segment();
    insert_value_from_var_name("other_segment", new_segment_base, vm, ids_data, ap_tracking)?;

    if finalize {
        vm.segments
            .finalize(Some(1), new_segment_base.segment_index as usize, None);
    }
    Ok(())
}

/// Implements hint:
/// %{
///     ecdsa_builtin.add_signature(ids.ecdsa_ptr, (
///         3086480810278599376317923499561306189851900463386393948998357832163236918254,
///         598673427589502599949712887611119751108407514580626464031881322743364689811))
/// %}
pub fn builtin_usage_add_signature(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let ecdsa_ptr = get_ptr_from_var_name("ecdsa_ptr", vm, ids_data, ap_tracking)?;
    let ecdsa_builtin = vm.get_signature_builtin()?;
    let (r_str, s_str) = (
        "3086480810278599376317923499561306189851900463386393948998357832163236918254",
        "598673427589502599949712887611119751108407514580626464031881322743364689811",
    );
    let r = Felt252::from_dec_str(r_str)
        .map_err(|e| HintError::CustomHint(format!("Failed to parse r dec str: {e:?}").into()))?;
    let s = Felt252::from_dec_str(s_str)
        .map_err(|e| HintError::CustomHint(format!("Failed to parse s dec str: {e:?}").into()))?;
    ecdsa_builtin.add_signature(ecdsa_ptr, &(r, s))?;
    Ok(())
}

/// Implements hint: %{ memory[ap] = 5 %}
pub fn builtin_usage_5_to_ap(vm: &mut VirtualMachine) -> Result<(), HintError> {
    insert_value_into_ap(vm, 5)
}

/// Implements hint:
/// %{
///     from starkware.crypto.signature.signature import pedersen_hash
///     assert memory[ids.output_ptr] == pedersen_hash(123, 456)
///
///     # Place the output in 3 pages.
///     output_builtin.add_page(page_id=1, page_start=ids.output_ptr + 1, page_size=2)
///     output_builtin.add_page(page_id=2, page_start=ids.output_ptr + 3, page_size=2)
///     # Don't use the GPS_FACT_TOPOLOGY constant to avoid unnecessary dependencies in the
///     # CMake target cairo_run_venv.
///     output_builtin.add_attribute('gps_fact_topology', [3, 2, 0, 1, 0, 2])
/// %}
pub fn builtin_usage_set_pages_and_fact_topology(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    let output_ptr_val = vm.get_integer(output_ptr)?.into_owned();
    let ped_hash_val = pedersen_hash(
        &FieldElement::from(123_usize),
        &FieldElement::from(456_usize),
    );
    if output_ptr_val != field_element_to_felt(ped_hash_val) {
        return Err(HintError::CustomHint(
            format!("Pedersen hash mismatch: expected {ped_hash_val}, got {output_ptr_val}").into(),
        ));
    }
    let output_builtin = vm.get_output_builtin_mut()?;
    output_builtin
        .add_page(1, (output_ptr + 1)?, 2)
        .map_err(|e| {
            HintError::CustomHint(format!("Failed to add page to output builtin: {e:?}").into())
        })?;
    output_builtin
        .add_page(2, (output_ptr + 3)?, 2)
        .map_err(|e| {
            HintError::CustomHint(format!("Failed to add page to output builtin: {e:?}").into())
        })?;
    output_builtin.add_attribute(GPS_FACT_TOPOLOGY.into(), [3, 2, 0, 1, 0, 2].to_vec());
    Ok(())
}

/// Implements hint:
/// %{
///     ids.n_output = program_input.get("n_output", 0)
///     ids.n_pedersen = program_input.get("n_pedersen", 0)
///     ids.n_range_check = program_input.get("n_range_check", 0)
///     ids.n_ecdsa = program_input.get("n_ecdsa", 0)
///     ids.n_bitwise = program_input.get("n_bitwise", 0)
///     ids.n_ec_op = program_input.get("n_ec_op", 0)
///     ids.n_keccak = program_input.get("n_keccak", 0)
///     ids.n_poseidon = program_input.get("n_poseidon", 0)
///     ids.n_range_check96 = program_input.get("n_range_check96", 0)
///     ids.n_add_mod = program_input.get("n_add_mod", 0)
///     ids.n_mul_mod = program_input.get("n_mul_mod", 0)
///     ids.n_memory_holes = program_input.get("n_memory_holes", 0)
/// %}
pub fn flexible_builtin_usage_from_input(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;
    let usage_input: FlexibleBuiltinUsageInput = serde_json::from_str(program_input).unwrap();

    insert_value_from_var_name("n_output", usage_input.n_output, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name(
        "n_pedersen",
        usage_input.n_pedersen,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "n_range_check",
        usage_input.n_range_check,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name("n_ecdsa", usage_input.n_ecdsa, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name(
        "n_bitwise",
        usage_input.n_bitwise,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name("n_ec_op", usage_input.n_ec_op, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name("n_keccak", usage_input.n_keccak, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name(
        "n_poseidon",
        usage_input.n_poseidon,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "n_range_check96",
        usage_input.n_range_check96,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "n_add_mod",
        usage_input.n_add_mod,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "n_mul_mod",
        usage_input.n_mul_mod,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "n_memory_holes",
        usage_input.n_memory_holes,
        vm,
        ids_data,
        ap_tracking,
    )
}
