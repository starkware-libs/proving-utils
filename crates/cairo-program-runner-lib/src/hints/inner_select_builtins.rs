use cairo_vm::Felt252;
use std::collections::HashMap;

use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::{
    get_ptr_from_var_name, insert_value_from_var_name,
};
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::vm_core::VirtualMachine;

use crate::hints::vars;

/// Sets ids.select_builtin to 1 if the first builtin should be selected and 0 otherwise.
/// Also sets ids.is_simulated_builtin to 1 if the builtin is a simulated builtin and 0 otherwise.
///
/// Implements hint:
/// %{
///     # A builtin should be selected iff its encoding appears in the selected encodings list
///     # and the list wasn't exhausted.
///     # Note that testing inclusion by a single comparison is possible since the lists are sorted.
///     ids.select_builtin = int(
///         n_selected_builtins > 0
///         and memory[ids.selected_encodings] == memory[ids.all_encodings]
///     )
///     if ids.select_builtin:
///         n_selected_builtins = n_selected_builtins - 1
///
///     # A builtin is considered a simulated builtin iff its encoding appears in the
///     # task_simulated_builtins_encodings list and the list wasn't exhausted.
///     # Note that testing inclusion by a single comparison is possible since the
///     simulated builtins list is sorted according to the program's builtin order.
///     ids.is_simulated_builtin = int(
///         n_task_simulated_builtins_left > 0
///         and memory[ids.task_simulated_builtins_encodings] == memory[ids.all_encodings]
///     )
///     if ids.is_simulated_builtin:
///         n_task_simulated_builtins_left -= 1
/// %}
pub fn select_builtin(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let n_selected_builtins: usize = exec_scopes.get(vars::N_SELECTED_BUILTINS)?;
    let n_simulated_builtins_left: usize = exec_scopes.get(vars::N_SIMULATED_BUILTINS_LEFT)?;

    let compute_flags =
        |n_selected: usize, n_simulated_left: usize| -> Result<(bool, bool), HintError> {
            if n_selected == 0 {
                return Ok((false, false));
            }

            let selected_encodings =
                get_ptr_from_var_name("selected_encodings", vm, ids_data, ap_tracking)?;
            let all_encodings = get_ptr_from_var_name("all_encodings", vm, ids_data, ap_tracking)?;
            let selected_encoding = vm.get_integer(selected_encodings)?.into_owned();
            let builtin_encoding = vm.get_integer(all_encodings)?.into_owned();
            let select_builtin = selected_encoding == builtin_encoding;

            if !select_builtin {
                // By assumption, `is_simulated_builtin ⇒ select_builtin`.
                return Ok((false, false));
            }

            if n_simulated_left == 0 {
                return Ok((true, false));
            }
            let task_simulated_encodings = get_ptr_from_var_name(
                "task_simulated_builtins_encodings",
                vm,
                ids_data,
                ap_tracking,
            )?;
            let simulated_encoding = vm.get_integer(task_simulated_encodings)?.into_owned();

            Ok((true, builtin_encoding == simulated_encoding))
        };

    let (select_builtin, is_simulated_builtin) =
        compute_flags(n_selected_builtins, n_simulated_builtins_left)?;

    let select_builtin_felt = Felt252::from(select_builtin);
    insert_value_from_var_name(
        "select_builtin",
        select_builtin_felt,
        vm,
        ids_data,
        ap_tracking,
    )?;
    let is_simulated_builtin_felt = Felt252::from(is_simulated_builtin);
    insert_value_from_var_name(
        "is_simulated_builtin",
        is_simulated_builtin_felt,
        vm,
        ids_data,
        ap_tracking,
    )?;

    if select_builtin {
        exec_scopes.insert_value(vars::N_SELECTED_BUILTINS, n_selected_builtins - 1);
    }
    if is_simulated_builtin {
        exec_scopes.insert_value(
            vars::N_SIMULATED_BUILTINS_LEFT,
            n_simulated_builtins_left - 1,
        );
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_integer_from_var_name;
    use cairo_vm::Felt252;
    use rstest::rstest;

    use super::*;

    #[rstest]
    #[case::should_select_builtin(1usize, true)]
    #[case::should_not_select_builtin(1usize, false)]
    #[case::no_builtins(0usize, true)]
    fn test_select_builtin(#[case] n_builtins: usize, #[case] should_select_builtin: bool) {
        let mut vm = vm!();

        let builtin_value = 10;
        let expected_value = if should_select_builtin {
            builtin_value
        } else {
            builtin_value + 1
        };

        vm.segments = segments![
            ((1, 0), (2, 0)),
            ((1, 1), (2, 1)),
            ((2, 0), builtin_value),
            ((2, 1), expected_value)
        ];
        // Allocate space for program_data_ptr
        vm.run_context.fp = 3;
        add_segments!(vm, 2);
        let ids_data = ids_data!["selected_encodings", "all_encodings", "select_builtin"];
        let ap_tracking = ApTracking::new();

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::N_SELECTED_BUILTINS, n_builtins);

        select_builtin(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        let select_builtin =
            get_integer_from_var_name("select_builtin", &vm, &ids_data, &ap_tracking)
                .unwrap()
                .into_owned();
        let n_selected_builtins: usize = exec_scopes.get(vars::N_SELECTED_BUILTINS).unwrap();

        if (n_builtins != 0) && should_select_builtin {
            assert_eq!(select_builtin, Felt252::from(1));
            assert_eq!(n_selected_builtins, n_builtins - 1);
        } else {
            assert_eq!(select_builtin, Felt252::from(0));
            assert_eq!(n_selected_builtins, n_builtins);
        }
    }
}
