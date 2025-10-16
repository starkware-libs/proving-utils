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

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_utils::fill_ids_data_for_test;
    use cairo_vm::types::relocatable::Relocatable;
    use cairo_vm::Felt252;
    use rstest::rstest;

    /// This test checks the hint implementation of `divide_queries_ind_by_coset_size_to_fp_offset`.
    /// It tests that the hint correctly divides the query index by the coset size and stores the
    /// result in fp + 1.
    #[rstest]
    #[case(42, 7, 6)]
    #[case(100, 25, 4)]
    #[case(0, 5, 0)]
    fn test_divide_queries_ind_by_coset_size_to_fp_offset(
        #[case] index: u64,
        #[case] coset_size: u64,
        #[case] expected: u64,
    ) {
        let mut vm = VirtualMachine::new(false, false);
        let mut ids_data = fill_ids_data_for_test(&["queries", "params"]);
        let ap_tracking = ApTracking::default();
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_ap(2);
        vm.set_fp(2);

        let queries_addr = Relocatable::from((2, 0));
        let params_addr = Relocatable::from((2, 3));
        let fp = vm.get_fp();
        vm.insert_value(
            Relocatable::from((fp.segment_index, fp.offset - 2)),
            MaybeRelocatable::from(queries_addr),
        )
        .expect("Failed to insert queries pointer");
        vm.insert_value(
            Relocatable::from((fp.segment_index, fp.offset - 1)),
            MaybeRelocatable::from(params_addr),
        )
        .expect("Failed to insert params pointer");

        let _ = vm.segments.load_data(
            queries_addr,
            &[
                MaybeRelocatable::from(Felt252::from(index)), // index
                MaybeRelocatable::from(100),                  // y_value
                MaybeRelocatable::from(200),                  // x_inv_value
            ],
        );
        let _ = vm.segments.load_data(
            params_addr,
            &[
                MaybeRelocatable::from(Felt252::from(coset_size)), // coset_size
                MaybeRelocatable::from(300),                       /* fri_group (pointer, not
                                                                    * used here) */
                MaybeRelocatable::from(400), // eval_point
            ],
        );
        divide_queries_ind_by_coset_size_to_fp_offset(&mut vm, &mut ids_data, &ap_tracking)
            .expect("Failed to run hint");
        // Assert result at fp+1 is 42/7 = 6
        let fp = vm.get_fp();
        let result_addr = Relocatable::from((fp.segment_index, fp.offset + 1));
        let result = vm.get_integer(result_addr).expect("Failed to get result");
        assert_eq!(*result.as_ref(), Felt252::from(expected));
    }
}
