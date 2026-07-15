//! Hint of the mock circuit verifier
//! (`starkware/cairo/cairo_verifier/mock_circuit_verifier.cairo`).

use std::collections::HashMap;

use cairo_vm::Felt252;
use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::insert_value_from_var_name;
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::vm_core::VirtualMachine;

use super::types::MockCircuitVerifierInput;
use super::utils::get_program_input_value;

/// Loads a list of u32 words into a fresh memory segment and returns its base.
fn load_words_segment(
    vm: &mut VirtualMachine,
    words: &[u32],
) -> Result<MaybeRelocatable, HintError> {
    let base = vm.add_memory_segment();
    let data: Vec<MaybeRelocatable> = words
        .iter()
        .map(|w| MaybeRelocatable::from(Felt252::from(*w)))
        .collect();
    vm.load_data(base, &data).map_err(HintError::Memory)?;
    Ok(MaybeRelocatable::from(base))
}

/// Implements hint: %{ MOCK_CIRCUIT_VERIFIER_LOAD_INPUT %}
///
/// Sets ids.preprocessed_root / ids.output_values (eight u32 words each, loaded into fresh
/// segments) and ids.n_steps from the MockCircuitVerifierInput program input.
pub fn load_mock_circuit_verifier_input(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let input: MockCircuitVerifierInput = get_program_input_value(exec_scopes)?;
    let preprocessed_root_ptr = load_words_segment(vm, &input.preprocessed_root)?;
    let output_values_ptr = load_words_segment(vm, &input.output_values)?;
    insert_value_from_var_name(
        "preprocessed_root",
        preprocessed_root_ptr,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "output_values",
        output_values_ptr,
        vm,
        ids_data,
        ap_tracking,
    )?;
    insert_value_from_var_name(
        "n_steps",
        Felt252::from(input.n_steps),
        vm,
        ids_data,
        ap_tracking,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::{
        get_integer_from_var_name, get_ptr_from_var_name,
    };

    use super::*;
    use crate::test_utils::fill_ids_data_for_test;
    use crate::{PROGRAM_INPUT, ProgramInput};

    /// Number of u32 words in a blake2s digest (and hence in a preprocessed root).
    const BLAKE2S_DIGEST_N_WORDS: usize = 8;

    /// A VM with the program/execution segments and fp/ap set past `n_ids` ids slots.
    fn vm_with_ids(names: &[&str]) -> (VirtualMachine, HashMap<String, HintReference>, ApTracking) {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        vm.set_fp(names.len());
        vm.set_ap(names.len());
        (vm, fill_ids_data_for_test(names), ApTracking::new())
    }

    fn sample_root(seed: u32) -> Vec<u32> {
        (0..BLAKE2S_DIGEST_N_WORDS as u32)
            .map(|i| seed + i)
            .collect()
    }

    #[test]
    fn test_load_mock_circuit_verifier_input() {
        let (mut vm, ids_data, ap_tracking) =
            vm_with_ids(&["preprocessed_root", "output_values", "n_steps"]);
        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(
            PROGRAM_INPUT,
            ProgramInput::Json(
                serde_json::json!({
                    "n_steps": 17,
                    "preprocessed_root": sample_root(10),
                    "output_values": sample_root(20),
                })
                .to_string(),
            ),
        );
        load_mock_circuit_verifier_input(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .unwrap();

        assert_eq!(
            get_integer_from_var_name("n_steps", &vm, &ids_data, &ap_tracking).unwrap(),
            Felt252::from(17)
        );
        for (name, seed) in [("preprocessed_root", 10u32), ("output_values", 20)] {
            let ptr = get_ptr_from_var_name(name, &vm, &ids_data, &ap_tracking).unwrap();
            let words: Vec<Felt252> = vm
                .get_integer_range(ptr, BLAKE2S_DIGEST_N_WORDS)
                .unwrap()
                .into_iter()
                .map(|f| *f.as_ref())
                .collect();
            let expected: Vec<Felt252> = sample_root(seed)
                .iter()
                .map(|&w| Felt252::from(w))
                .collect();
            assert_eq!(words, expected, "words mismatch for {name}");
        }
    }
}
