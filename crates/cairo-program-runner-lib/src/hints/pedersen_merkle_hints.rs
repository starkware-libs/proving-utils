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
/// The choice between y and x is flagged by the `is_left_sibling` boolean.
pub fn pedersen_merkle_update(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    is_left_sibling: bool,
) -> Result<(), HintError> {
    let auth_path: &mut Vec<Felt252> = exec_scopes.get_mut_ref(AUTH_PATH)?;
    let sibling = auth_path.pop().ok_or_else(|| {
        HintError::CustomHint("auth_path is empty. Cannot pop a sibling value.".into())
    })?;

    let prev_node_hash_ptr = get_ptr_from_var_name("prev_node_hash", vm, ids_data, ap_tracking)?;
    let new_node_hash_ptr = get_ptr_from_var_name("new_node_hash", vm, ids_data, ap_tracking)?;

    let is_left_sibling_usize = is_left_sibling as usize;
    vm.insert_value((prev_node_hash_ptr + is_left_sibling_usize)?, sibling)?;
    vm.insert_value((new_node_hash_ptr + is_left_sibling_usize)?, sibling)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::fill_ids_data_for_test;
    use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
    use cairo_vm::vm::vm_core::VirtualMachine;
    use num_bigint::BigUint;
    use rstest::{fixture, rstest};

    /// Provides a sample PedersenMerkleInput in JSON format for testing.
    #[fixture]
    fn pedersen_merkle_input() -> String {
        let input = PedersenMerkleInput {
            height: 3,
            prev_leaf: Felt252::from(123456789u64),
            new_leaf: Felt252::from(987654321u64),
            node_index: 5,
            path: vec![
                // Use BigUint for large integer literals
                Felt252::from(
                    BigUint::parse_bytes(b"1111111111111111111111111111111111111111", 10).unwrap(),
                ),
                Felt252::from(
                    BigUint::parse_bytes(b"2222222222222222222222222222222222222222", 10).unwrap(),
                ),
                Felt252::from(
                    BigUint::parse_bytes(b"3333333333333333333333333333333333333333", 10).unwrap(),
                ),
            ],
        };
        serde_json::to_string(&input).unwrap()
    }

    /// Tests the `pedersen_merkle_load_input` hint function.
    /// It verifies that the input is correctly loaded into the VM memory and that the
    /// reversed auth_path is correctly set in the execution scopes.
    #[rstest]
    fn test_pedersen_merkle_load_input(pedersen_merkle_input: String) {
        let mut vm = VirtualMachine::new(false, false);
        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(PROGRAM_INPUT, pedersen_merkle_input.clone());
        let ids_data = fill_ids_data_for_test(&["output"]);
        let ap_tracking = ApTracking::new();

        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(1);
        vm.set_ap(2);
        vm.load_data(Relocatable::from((1, 0)), &[MaybeRelocatable::from((2, 0))])
            .expect("Failed to load initial data into VM memory.");

        pedersen_merkle_load_input(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint execution failed unexpectedly");

        // Assert that the input was correctly loaded into memory
        let expected_pedersen_merkle_input: PedersenMerkleInput =
            serde_json::from_str(&pedersen_merkle_input)
                .expect("Failed to deserialize pedersen_merkle_input");
        // assert that output values are correctly set
        let got_height = vm
            .get_integer(Relocatable::from((2, 0)))
            .expect("Failed to read height from VM memory")
            .as_ref()
            .clone();
        assert_eq!(
            got_height,
            Felt252::from(expected_pedersen_merkle_input.height),
            "height mismatch in VM memory"
        );

        // Assert that auth_path is correctly set in exec_scopes
        let auth_path: &Vec<Felt252> = exec_scopes.get_ref(AUTH_PATH).unwrap();
        let expected_reversed_path: Vec<Felt252> = expected_pedersen_merkle_input
            .path
            .into_iter()
            .rev()
            .collect();
        assert_eq!(auth_path, &expected_reversed_path);
    }

    /// Tests the `pedersen_merkle_verify_auth_path_len` hint function.
    /// It verifies that the function correctly checks the length of auth_path in exec_scopes.
    /// Iyt should pass for an empty auth_path and fail for a non-empty one.
    #[test]
    fn test_pedersen_merkle_verify_auth_path_len() {
        let mut exec_scopes = ExecutionScopes::new();
        // Test with empty auth_path
        exec_scopes.insert_value::<Vec<Felt252>>(AUTH_PATH, vec![]);
        assert!(pedersen_merkle_verify_auth_path_len(&mut exec_scopes).is_ok());

        // Test with non-empty auth_path
        exec_scopes.insert_value::<Vec<Felt252>>(AUTH_PATH, vec![Felt252::from(1)]);
        let result = pedersen_merkle_verify_auth_path_len(&mut exec_scopes);
        assert!(result.is_err());
        match result.unwrap_err() {
            HintError::CustomHint(ref msg) => assert!(msg.contains("Got too many values")),
            _ => panic!("Expected CustomHint"),
        }
    }

    /// Tests the `pedersen_merkle_idx_parity_to_ap` hint function.
    /// It verifies that the function correctly computes index % 2 and stores it at memory[ap].
    #[rstest]
    #[case(4)]
    #[case(5)]
    fn test_pedersen_merkle_idx_parity_to_ap(#[case] index: usize) {
        let mut vm = VirtualMachine::new(false, false);
        let ids_data = fill_ids_data_for_test(&["index"]);
        let ap_tracking = ApTracking::new();

        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(1);
        vm.set_ap(1);
        vm.load_data(Relocatable::from((1, 0)), &[MaybeRelocatable::from(index)])
            .expect("Failed to load initial data into VM memory.");

        pedersen_merkle_idx_parity_to_ap(&mut vm, &ids_data, &ap_tracking)
            .expect("Hint execution failed unexpectedly");

        assert_eq!(
            vm.get_integer(Relocatable::from((1, 1))).unwrap().as_ref(),
            &Felt252::from(index % 2)
        );
    }

    /// Tests the `pedersen_merkle_update` hint function for the case when auth_path is empty.
    /// It verifies that the function returns an error when trying to pop from an empty auth_path.
    #[test]
    fn test_pedersen_merkle_update_empty_auth_path_errors() {
        let mut vm = VirtualMachine::new(false, false);
        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = fill_ids_data_for_test(&["prev_node_hash", "new_node_hash"]);
        let ap_tracking = ApTracking::new();

        exec_scopes.insert_value::<Vec<Felt252>>(AUTH_PATH, vec![]);

        // Setup VM pointers as in other test...
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(1);
        vm.set_ap(1);
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from((1, 0)),
                MaybeRelocatable::from((1, 2)),
            ],
        )
        .expect("Failed to load initial data");

        let result =
            pedersen_merkle_update(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking, true);

        match result {
            Err(HintError::CustomHint(msg)) => assert!(msg.contains("auth_path is empty")),
            _ => panic!("Expected a CustomHint error when auth_path is empty"),
        }
    }

    /// Tests the `pedersen_merkle_update` hint function.
    /// It verifies that the function correctly pops a sibling from auth_path and updates
    /// the prev_node_hash and new_node_hash in VM memory based on the is_left_sibling flag.
    #[rstest]
    #[case(true)]
    #[case(false)]
    fn test_pedersen_merkle_update(#[case] is_left_sibling: bool) {
        let mut vm = VirtualMachine::new(false, false);
        let mut exec_scopes = ExecutionScopes::new();
        let ids_data = fill_ids_data_for_test(&["prev_node_hash", "new_node_hash"]);
        let ap_tracking = ApTracking::new();

        // Prepare auth_path with two siblings
        let sibling1 = Felt252::from(111u64);
        let sibling2 = Felt252::from(222u64);
        exec_scopes.insert_value::<Vec<Felt252>>(AUTH_PATH, vec![sibling1.clone(), sibling2]);

        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(2);
        vm.set_ap(2);
        // prev_node_hash and new_node_hash are pointers to arrays of size 2 (x, y)
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from((2, 0)),
                MaybeRelocatable::from((2, 2)),
            ],
        )
        .expect("Failed to load initial data into VM memory.");

        // First call with is_left_sibling = true (update x)
        pedersen_merkle_update(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            is_left_sibling,
        )
        .expect("Hint execution failed unexpectedly");

        // Assert that the sibling was chosen correctly
        let hash_offset = if is_left_sibling { 1 } else { 0 };
        assert_eq!(
            vm.get_integer(Relocatable::from((2, hash_offset)))
                .unwrap()
                .as_ref(),
            &Felt252::from(222u64)
        );
        assert_eq!(
            vm.get_integer(Relocatable::from((2, 2 + hash_offset)))
                .unwrap()
                .as_ref(),
            &Felt252::from(222u64)
        );
    }
}
