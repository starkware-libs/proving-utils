use std::collections::HashMap;

use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{
            get_relocatable_from_var_name, insert_value_from_var_name,
        },
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::relocatable::MaybeRelocatable,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
};
use num_bigint::BigUint;

/// Implements
// %{ ids.bit = ids.current.index & 1 %}
pub fn set_bit_from_index(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // Retrieve the `index` value from `ids.current`
    let current_addr = get_relocatable_from_var_name("current", vm, ids_data, ap_tracking)?;

    // Address is to the base of the following Cairo struct:
    // struct VectorQueryWithDepth {
    //     index: felt,
    //     value: felt,
    //     depth: felt,
    // }
    // We need to get the value of `index` from the struct.
    let index = vm.get_integer(current_addr)?.to_biguint();

    let bit = MaybeRelocatable::Int((index & BigUint::from(1u8)).into());
    insert_value_from_var_name("bit", bit, vm, ids_data, ap_tracking)?;

    Ok(())
}
