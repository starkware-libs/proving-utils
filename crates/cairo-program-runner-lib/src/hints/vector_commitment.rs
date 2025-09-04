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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::prepare_ids_data_for_test;
    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_maybe_relocatable_from_var_name;
    use cairo_vm::types::relocatable::Relocatable;
    use cairo_vm::Felt252;
    use rstest::rstest;

    /// This test verifies that the `set_bit_from_index` hint correctly sets the bit
    /// based on the least significant bit of the provided index.
    #[rstest]
    #[case(0)]
    #[case(1)]
    #[case(2)]
    #[case(7)]
    fn test_set_bit_from_index(#[case] index: u64) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(2);
        vm.set_ap(2);

        vm.load_data(
            Relocatable::from((1, 0)),
            &[MaybeRelocatable::Int(Felt252::from(index))],
        )
        .expect("Failed to load data into VM memory");

        let ids_data = prepare_ids_data_for_test(&["current", "bit"]);
        let ap_tracking = ApTracking::new();

        set_bit_from_index(&mut vm, &ids_data, &ap_tracking).expect("Failed to set bit from index");
        let bit = get_maybe_relocatable_from_var_name("bit", &vm, &ids_data, &ap_tracking)
            .expect("Failed to get bit from VM memory");
        assert_eq!(bit, MaybeRelocatable::Int(Felt252::from(index % 2)));
    }
}
