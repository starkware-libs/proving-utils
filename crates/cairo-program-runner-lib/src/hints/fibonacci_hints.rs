use cairo_vm::{
    hint_processor::builtin_hint_processor::hint_utils::insert_value_into_ap,
    types::exec_scope::ExecutionScopes,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
};

use super::{types::FibonacciInput, PROGRAM_INPUT};

const FIBONACCI_CLAIM_INDEX: &str = "fibonacci_claim_index";

/// Implements hint: %{ memory[ap] = program_input['second_element'] %}
pub fn fibonacci_load_second_element(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;
    let fibonacci_input: FibonacciInput = serde_json::from_str(program_input).unwrap();
    exec_scopes.insert_value(FIBONACCI_CLAIM_INDEX, fibonacci_input.fibonacci_claim_index);
    insert_value_into_ap(vm, fibonacci_input.second_element)
}

/// Implements hint: %{ memory[ap] = program_input['fibonacci_claim_index'] %}
pub fn fibonacci_load_claim_idx(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let fibonacci_claim_index: usize = exec_scopes.get(FIBONACCI_CLAIM_INDEX)?;
    insert_value_into_ap(vm, fibonacci_claim_index)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cairo_vm::types::relocatable::Relocatable;
    use cairo_vm::vm::vm_core::VirtualMachine;
    use cairo_vm::Felt252;

    fn prepare_vm_for_fibonacci_test(
        fibonacci_input: &FibonacciInput,
    ) -> (VirtualMachine, ExecutionScopes) {
        let mut vm = VirtualMachine::new(false, true);
        vm.segments.add();
        vm.segments.add();
        vm.set_ap(0);
        vm.set_fp(0);
        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(
            PROGRAM_INPUT,
            serde_json::to_string(&fibonacci_input).unwrap(),
        );
        (vm, exec_scopes)
    }

    #[test]
    fn test_fibonacci_load_second_element() {
        // Runs fibonacci_load_second_element hint and asserts that the second element is loaded
        // correctly into ap.

        let fibonacci_input = FibonacciInput {
            second_element: 5,
            fibonacci_claim_index: 3,
        };

        let (mut vm, mut exec_scopes) = prepare_vm_for_fibonacci_test(&fibonacci_input);
        let result = fibonacci_load_second_element(&mut vm, &mut exec_scopes);
        assert!(result.is_ok());
        assert_eq!(vm.get_ap(), Relocatable::from((1, 0)));
        assert_eq!(
            vm.segments
                .memory
                .get_integer(vm.get_ap())
                .unwrap()
                .as_ref(),
            &Felt252::from(fibonacci_input.second_element)
        );
    }

    #[test]
    fn test_fibonacci_load_claim_idx() {
        // Runs fibonacci_load_second_element and afterwards fibonacci_load_claim_idx hint and
        // asserts that the claim index is loaded correctly into ap.
        let fibonacci_input = FibonacciInput {
            second_element: 5,
            fibonacci_claim_index: 3,
        };

        let (mut vm, mut exec_scopes) = prepare_vm_for_fibonacci_test(&fibonacci_input);
        fibonacci_load_second_element(&mut vm, &mut exec_scopes).unwrap();
        vm.set_ap(1); // Set AP to 1 to simulate the hint's behavior
        fibonacci_load_claim_idx(&mut vm, &mut exec_scopes).unwrap();
        assert_eq!(vm.get_ap(), Relocatable::from((1, 1)));
        assert_eq!(
            vm.segments
                .memory
                .get_integer(vm.get_ap())
                .unwrap()
                .as_ref(),
            &Felt252::from(fibonacci_input.fibonacci_claim_index)
        );
    }
}
