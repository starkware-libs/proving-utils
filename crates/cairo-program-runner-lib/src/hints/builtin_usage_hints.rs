use std::collections::HashMap;

use super::{
    execute_task_hints::felt_to_felt252, fact_topologies::GPS_FACT_TOPOLOGY,
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
use starknet_crypto::{pedersen_hash, Felt};

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
    let ped_hash_val = pedersen_hash(&Felt::from(123_usize), &Felt::from(456_usize));
    if output_ptr_val != felt_to_felt252(ped_hash_val) {
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
///     ids.n_qm31 = program_input.get("n_qm31", 0)
///     ids.n_memory_holes = program_input.get("n_memory_holes", 0)
///     ids.n_blake2s = program_input.get("n_blake2s", 0)
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
    insert_value_from_var_name("n_qm31", usage_input.n_qm31, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name(
        "n_memory_holes",
        usage_input.n_memory_holes,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "n_blake2s",
        usage_input.n_blake2s,
        vm,
        ids_data,
        ap_tracking,
    )
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::fill_ids_data_for_test;
    use cairo_vm::serde::deserialize_program::OffsetValue;
    use cairo_vm::types::relocatable::MaybeRelocatable;
    use cairo_vm::types::relocatable::Relocatable;
    use cairo_vm::vm::runners::builtin_runner::{
        BuiltinRunner, OutputBuiltinRunner, OutputBuiltinState, SignatureBuiltinRunner,
    };
    use cairo_vm::vm::runners::cairo_pie::PublicMemoryPage;
    use cairo_vm::vm::vm_core::VirtualMachine;
    use rstest::rstest;
    use std::borrow::Cow;
    use std::collections::BTreeMap;

    fn prepare_vm_for_flexible_builtin_usage_test(
        input: &FlexibleBuiltinUsageInput,
    ) -> (
        VirtualMachine,
        ExecutionScopes,
        HashMap<String, HintReference>,
        ApTracking,
    ) {
        // Prepare a VirtualMachine instance, ids_data, exec_scopes, and ap_tracking for testing.
        // Should mimic the vm's state after running the following Cairo0 code:
        // alloc_locals;
        // local n_output;
        // local n_pedersen;
        // local n_range_check;
        // local n_ecdsa;
        // local n_bitwise;
        // local n_ec_op;
        // local n_keccak;
        // local n_poseidon;
        // local n_range_check96;
        // local n_add_mod;
        // local n_mul_mod;
        // local n_qm31;
        // local n_memory_holes;
        // local n_blake2s;
        let mut vm = VirtualMachine::new(false, false);
        let ids_data = fill_ids_data_for_test(&[
            "n_output",
            "n_pedersen",
            "n_range_check",
            "n_ecdsa",
            "n_bitwise",
            "n_ec_op",
            "n_keccak",
            "n_poseidon",
            "n_range_check96",
            "n_add_mod",
            "n_mul_mod",
            "n_qm31",
            "n_memory_holes",
            "n_blake2s",
        ]);
        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(PROGRAM_INPUT, serde_json::to_string(input).unwrap());
        let ap_tracking = ApTracking::default();
        vm.set_fp(14);
        vm.set_ap(14);
        vm.segments.add();
        vm.segments.add();
        (vm, exec_scopes, ids_data, ap_tracking)
    }

    /// Test the builtin_usage_add_other_segment function with finalize set to true and false.
    /// Checks that other_segment is added correctly and segment is finalized based on the flag.
    #[rstest(finalize, case(true), case(false))]
    fn test_builtin_usage_add_other_segment(finalize: bool) {
        let mut vm = VirtualMachine::new(false, false);
        let ids_data = fill_ids_data_for_test(&["other_segment"]);
        vm.segments.add();
        vm.segments.add();
        vm.set_fp(1);
        let ap_tracking = ApTracking::default();
        let result = builtin_usage_add_other_segment(&mut vm, &ids_data, &ap_tracking, finalize);
        assert!(result.is_ok());

        // Check that other_segment was added correctly.
        let other_segment = vm
            .segments
            .memory
            .get_relocatable(Relocatable::from((1, 0)))
            .expect("Failed to get other_segment");
        assert_eq!(other_segment, Relocatable::from((2, 0)));

        // Check that the segment is finalized based on the finalize flag.
        if finalize {
            assert_eq!(vm.segments.get_segment_size(2), Some(1));
        } else {
            assert_eq!(vm.segments.get_segment_size(2), None);
        }
    }

    /// Test the builtin_usage_add_signature hint with a sample signature.
    /// Checks that the signature is added correctly to the VM's state.
    #[test]
    fn test_builtin_usage_add_signature() {
        let mut vm = VirtualMachine::new(false, false);
        let ids_data = fill_ids_data_for_test(&["ecdsa_ptr"]);
        let ap_tracking = ApTracking::default();
        vm.segments.add();
        vm.segments.add();
        vm.set_fp(1);
        vm.set_ap(1);

        // Initialize the SignatureBuiltinRunner with a base of 2.
        let mut ecdsa_builtin = SignatureBuiltinRunner::new(Some(512), true);
        ecdsa_builtin.initialize_segments(&mut vm.segments);
        assert_eq!(ecdsa_builtin.base, 2);
        vm.builtin_runners = vec![ecdsa_builtin.into()];

        // Load the ecdsa_ptr (2,0) into the VM's memory
        let _ = vm
            .load_data(
                Relocatable::from((1, 0)),
                &[MaybeRelocatable::from(Relocatable::from((2, 0)))],
            )
            .unwrap();

        builtin_usage_add_signature(&mut vm, &ids_data, &ap_tracking)
            .expect("Failed to add signature");

        // Check that the signature was added correctly.
        if let BuiltinRunner::Signature(sig_runner) = &vm.builtin_runners[0] {
            let signatures = sig_runner.signatures.try_borrow_mut().unwrap();
            let signature = signatures
                .get(&Relocatable::from((2, 0)))
                .expect("Signature not found at ecdsa_ptr");
            let expected_signature = (
                Felt252::from_dec_str(
                    "3086480810278599376317923499561306189851900463386393948998357832163236918254",
                )
                .unwrap(),
                Felt252::from_dec_str(
                    "598673427589502599949712887611119751108407514580626464031881322743364689811",
                )
                .unwrap(),
            );
            assert_eq!(signature.r, expected_signature.0);
            assert_eq!(signature.s, expected_signature.1);
        } else {
            panic!("Not a SignatureBuiltinRunner");
        }
    }

    /// Test the builtin_usage_5_to_ap function - checks that the value 5 is inserted into the AP.
    /// Checks that Ap indeed has the value 5 and not 6.
    #[test]
    fn test_builtin_usage_5_to_ap() {
        let mut vm = VirtualMachine::new(false, false);
        vm.segments.add();
        vm.segments.add();
        vm.set_fp(1);
        vm.set_ap(1);
        let result = builtin_usage_5_to_ap(&mut vm);
        assert!(result.is_ok());
        // Check that the value 5 was inserted into the AP.
        let ap = vm.get_ap();
        let value = vm
            .segments
            .memory
            .get_integer(ap)
            .expect("Failed to get AP value");
        assert_eq!(value, Cow::Borrowed(&Felt252::from(5)));

        //Check that 6 is not in ap.
        assert_ne!(value, Cow::Borrowed(&Felt252::from(6)));

        //Also check that 5 is still in ap.
        assert_eq!(value, Cow::Borrowed(&Felt252::from(5)));
    }

    /// Test the builtin_usage_set_pages_and_fact_topology function.
    /// Checks the assertion of the pedersen hash and the addition of pages and fact topology to the
    /// output builtin.
    #[rstest(
        left_pedersen_hash,
        case::hash_matches(123_usize),
        case::hash_mismatch(122_usize)
    )]
    fn test_builtin_usage_set_pages_and_fact_topology(left_pedersen_hash: usize) {
        let mut vm = VirtualMachine::new(false, false);
        let ids_data = fill_ids_data_for_test(&["output_ptr"]);
        let ap_tracking = ApTracking::default();
        vm.segments.add();
        vm.segments.add();
        vm.set_fp(1);
        vm.set_ap(1);
        // Load the output_ptr (2,0) into the VM's memory
        let _ = vm
            .load_data(
                Relocatable::from((1, 0)),
                &[MaybeRelocatable::from(Relocatable::from((2, 0)))],
            )
            .unwrap();

        // Initialize the OutputBuiltinRunner with a base of 2.
        let output_segment = vm.add_memory_segment();
        let mut output_builtin_runner = OutputBuiltinRunner::new(true);
        let temp_output_builtin_state = OutputBuiltinState {
            base: output_segment.segment_index as usize,
            base_offset: 0,
            pages: Default::default(),
            attributes: Default::default(),
        };
        output_builtin_runner.set_state(temp_output_builtin_state);
        vm.builtin_runners = vec![output_builtin_runner.into()];

        // Load pedersen hash into output builtin_ptr
        let ped_hash = pedersen_hash(&Felt::from(left_pedersen_hash), &Felt::from(456_usize));
        let ped_hash_felt = felt_to_felt252(ped_hash);
        let _ = vm
            .load_data(
                Relocatable::from((2, 0)),
                &[MaybeRelocatable::from(ped_hash_felt)],
            )
            .unwrap();

        let result = builtin_usage_set_pages_and_fact_topology(&mut vm, &ids_data, &ap_tracking);

        // Hint should succeed if the pedersen hash matches the expected value.
        if left_pedersen_hash == 123_usize {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
            return;
        }

        // Assert that OutputBuiltinRunner has the expected pages and attributes.
        if let BuiltinRunner::Output(output_runner) = &mut vm.builtin_runners[0] {
            let output_builtin_state = output_runner.get_state();
            let expected_output_builtin_state = OutputBuiltinState {
                base: 2,
                base_offset: 0,
                pages: BTreeMap::from([
                    (1, PublicMemoryPage { start: 1, size: 2 }),
                    (2, PublicMemoryPage { start: 3, size: 2 }),
                ]),
                attributes: BTreeMap::from([(GPS_FACT_TOPOLOGY.into(), vec![3, 2, 0, 1, 0, 2])]),
            };
            assert_eq!(output_builtin_state, expected_output_builtin_state);
        } else {
            panic!("Not an OutputBuiltinRunner");
        }
    }

    /// Test the flexible_builtin_usage_from_input function with a sample input.
    /// Asserts that the hint puts all values into the VM's locals as expected.
    #[test]
    fn test_flexible_builtin_usage_from_input() {
        let input = FlexibleBuiltinUsageInput {
            n_output: 1,
            n_pedersen: 2,
            n_range_check: 3,
            n_ecdsa: 4,
            n_bitwise: 5,
            n_ec_op: 6,
            n_keccak: 7,
            n_poseidon: 8,
            n_range_check96: 9,
            n_add_mod: 10,
            n_mul_mod: 11,
            n_qm31: 12,
            n_memory_holes: 13,
            n_blake2s: 14,
        };
        let (mut vm, mut exec_scopes, ids_data, ap_tracking) =
            prepare_vm_for_flexible_builtin_usage_test(&input);

        let result =
            flexible_builtin_usage_from_input(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking);
        assert!(result.is_ok());

        // Check that the VM state was modified as expected.
        let local_names = [
            "n_output",
            "n_pedersen",
            "n_range_check",
            "n_ecdsa",
            "n_bitwise",
            "n_ec_op",
            "n_keccak",
            "n_poseidon",
            "n_range_check96",
            "n_add_mod",
            "n_mul_mod",
            "n_qm31",
            "n_memory_holes",
            "n_blake2s",
        ];
        let expected_values = [
            input.n_output,
            input.n_pedersen,
            input.n_range_check,
            input.n_ecdsa,
            input.n_bitwise,
            input.n_ec_op,
            input.n_keccak,
            input.n_poseidon,
            input.n_range_check96,
            input.n_add_mod,
            input.n_mul_mod,
            input.n_qm31,
            input.n_memory_holes,
            input.n_blake2s,
        ];

        // Check that the VM's locals match the expected values.
        // The locals are stored at FP + offset2, where offset2 is the offset in the HintReference.
        // The offset2 is always a Value, so we can safely use it
        // to calculate the address of the local variable.
        for (i, (&name, &expected)) in local_names.iter().zip(expected_values.iter()).enumerate() {
            let hint_ref = ids_data.get(name).expect("Missing HintReference");
            // Calculate address: FP + offset2
            let offset: i32 = match hint_ref.offset1 {
                OffsetValue::Immediate(_) => panic!("Unexpected Immediate in offset2 for {name}"),
                OffsetValue::Value(_) => panic!("Unexpected Value in offset2 for {name}"),
                OffsetValue::Reference(_, offset, _, _) => offset,
            };
            let fp = vm.get_fp();
            let addr = Relocatable::from((fp.segment_index, (fp.offset as i32 + offset) as usize));
            let value_owned = vm.segments.memory.get_integer(addr).unwrap();
            let value = value_owned.as_ref();
            assert_eq!(
                value,
                &Felt252::from(expected),
                "Mismatch for {name} at local {i}"
            );
        }
    }
}
