use std::collections::HashMap;

use super::{types::ConcatAggregatorInput, PROGRAM_INPUT};
use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{
            get_integer_from_var_name, get_ptr_from_var_name, insert_value_from_var_name,
        },
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::{exec_scope::ExecutionScopes, relocatable::MaybeRelocatable},
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
    Felt252,
};
use num_traits::ToPrimitive;

const TASKS_OUTPUTS: &str = "tasks_outputs";

/// Implements hint:
/// %{
///     def parse_bootloader_tasks_outputs(output):
///         """
///         Parses the output of the bootloader, returning the raw outputs of the tasks.
///         """
///         output_iter = iter(output)
///         # Skip the bootloader_config.
///         [next(output_iter) for _ in range(3)]
///
///         n_tasks = next(output_iter)
///         tasks_outputs = []
///         for _ in range(n_tasks):
///             task_output_size = next(output_iter)
///             tasks_outputs.append([next(output_iter) for _ in range(task_output_size - 1)])
///
///         assert next(output_iter, None) is None, "Bootloader output wasn't fully consumed."
///
///         return tasks_outputs
///
///     tasks_outputs = parse_bootloader_tasks_outputs(program_input["bootloader_output"])
///     assert len(tasks_outputs) > 0, "No tasks found in the bootloader output."
///     ids.n_tasks = len(tasks_outputs)
/// %}
pub fn concat_aggregator_parse_task(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;
    let concat_aggregator_input: ConcatAggregatorInput = serde_json::from_str(program_input)
        .map_err(|e| HintError::CustomHint(format!("JSON decode error: {e}").into()))?;

    let bl_numbers = concat_aggregator_input
        .bootloader_output
        .iter()
        .map(|number| {
            Felt252::from_dec_str(&number.to_string())
                .map(|felt| felt.into())
                .map_err(|e| HintError::CustomHint(format!("Conversion failed: {e:?}").into()))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let mut iter = bl_numbers.into_iter();
    let mut next_item = || {
        iter.next()
            .ok_or_else(|| HintError::CustomHint("Unexpected end of bootloader output.".into()))
    };

    let extract_usize = |mr: MaybeRelocatable| -> Result<usize, HintError> {
        match mr {
            MaybeRelocatable::Int(felt) => felt
                .to_usize()
                .ok_or_else(|| HintError::CustomHint("Failed to convert value to usize.".into())),
            _ => Err(HintError::CustomHint("Expected Int variant.".into())),
        }
    };

    for _ in 0..3 {
        next_item()?;
    }

    let n_tasks = extract_usize(next_item()?)?;

    let tasks_outputs = (0..n_tasks)
        .map(|_| -> Result<Vec<MaybeRelocatable>, HintError> {
            let task_size = extract_usize(next_item()?)?;
            (0..task_size.saturating_sub(1))
                .map(|_| next_item())
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;

    if iter.next().is_some() {
        return Err(HintError::CustomHint(
            "Bootloader output wasn't fully consumed.".into(),
        ));
    }
    if tasks_outputs.is_empty() {
        return Err(HintError::CustomHint(
            "No tasks found in the bootloader output.".into(),
        ));
    }

    insert_value_from_var_name("n_tasks", tasks_outputs.len(), vm, ids_data, ap_tracking)?;
    exec_scopes.insert_value(TASKS_OUTPUTS, tasks_outputs);
    Ok(())
}

/// Implements hint:
/// %{
///     task_index = len(tasks_outputs) - ids.n_tasks
///     segments.load_data(ptr=ids.output_ptr, data=tasks_outputs[task_index])
///     ids.output_size = len(tasks_outputs[task_index]) + size_offset
/// %}
/// Where `size_offset` is in {0, 1}.
pub fn concat_aggregator_get_handle_task_output(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    size_offset: usize,
) -> Result<(), HintError> {
    let tasks_outputs: &Vec<Vec<MaybeRelocatable>> = exec_scopes.get_ref(TASKS_OUTPUTS)?;
    let n_tasks = get_integer_from_var_name("n_tasks", vm, ids_data, ap_tracking)?
        .to_usize()
        .ok_or_else(|| HintError::CustomHint("Failed to convert value to usize.".into()))?;
    let task_index = tasks_outputs.len() - n_tasks;
    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    vm.segments
        .load_data(output_ptr, &tasks_outputs[task_index])?;

    insert_value_from_var_name(
        "output_size",
        tasks_outputs[task_index].len() + size_offset,
        vm,
        ids_data,
        ap_tracking,
    )
}
