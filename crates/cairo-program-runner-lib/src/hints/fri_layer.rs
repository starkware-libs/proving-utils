use std::collections::HashMap;

use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_relocatable_from_var_name;
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::vm_core::VirtualMachine;

/// Implements
// local coset_index = nondet %{ ids.queries.index // ids.params.coset_size %};
// Compiled: memory[fp + 1] = to_felt_or_relocatable(ids.queries.index // ids.params.coset_size)
pub fn divide_queries_ind_by_coset_size_to_fp_offset(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let queries_base = get_relocatable_from_var_name("queries", vm, ids_data, ap_tracking)?;
    let params_base = get_relocatable_from_var_name("params", vm, ids_data, ap_tracking)?;

    // queries_addr is the base of an array of the following Cairo structs:
    // struct FriLayerQuery {
    //     index: felt,
    //     y_value: felt,
    //     x_inv_value: felt,
    // }
    // We need to get the value of `index` from the first struct.
    //
    // params_addr is the base of an array of the following Cairo struct:
    // struct FriLayerComputationParams {
    //     coset_size: felt,
    //     fri_group: felt*,
    //     eval_point: felt,
    // }
    // We need to get the value of `coset_size` from the first struct.

    let first_query_addr = vm.get_relocatable(queries_base).map_err(|_| {
        HintError::CustomHint("Failed to retrieve `first_query_addr` as relocatable.".into())
    })?;

    let first_params_addr = vm.get_relocatable(params_base).map_err(|_| {
        HintError::CustomHint("Failed to retrieve `first_params_addr` as relocatable.".into())
    })?;

    // Perform integer division
    let index = vm
        .get_integer(first_query_addr)
        .map_err(|_| {
            HintError::CustomHint("Failed to retrieve `queries.index` as integer.".into())
        })?
        .to_biguint();

    // Get `coset_size` from `params`
    let coset_size = vm
        .get_integer(first_params_addr)
        .map_err(|_| {
            HintError::CustomHint("Failed to retrieve `params.coset_size` as integer.".into())
        })?
        .to_biguint();
    let result = MaybeRelocatable::Int((index / coset_size).into());

    // Insert result into memory at `fp + 1`
    let dest = (vm.get_fp() + 1)?;
    Ok(vm.insert_value(dest, result)?)
}
