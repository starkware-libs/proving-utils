use std::collections::HashMap;
use std::path::PathBuf;

use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_ptr_from_var_name;
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::vm_core::VirtualMachine;
use starknet_types_core::felt::Felt;

use crate::hints::types::PrivacySimpleBootloaderInput;
use crate::hints::vars;
use crate::hints::SIMPLE_BOOTLOADER_INPUT;

use super::utils::get_program_input_value;

/// Loads privacy simple bootloader input from the program input.
/// Stores the inner `SimpleBootloaderInput` and the `output_preimage_dump_path` separately
/// in the execution scopes.
pub fn load_privacy_simple_bootloader_input(
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let privacy_input: PrivacySimpleBootloaderInput = get_program_input_value(exec_scopes)?;
    exec_scopes.insert_value(SIMPLE_BOOTLOADER_INPUT, privacy_input.simple_bootloader_input);
    exec_scopes.insert_value(
        vars::OUTPUT_PREIMAGE_DUMP_PATH,
        privacy_input.output_preimage_dump_path,
    );
    Ok(())
}

/// Reads the output elements between `simple_bl_output_start` and `simple_bl_output` pointers
/// and dumps them as JSON to the file path stored in exec scopes under `OUTPUT_PREIMAGE_DUMP_PATH`.
pub fn dump_privacy_simple_bootloader_output_preimage(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let output_start =
        get_ptr_from_var_name("simple_bl_output_start", vm, ids_data, ap_tracking)?;
    let output_end = get_ptr_from_var_name("simple_bl_output", vm, ids_data, ap_tracking)?;
    let size = (output_end - output_start)?;

    let elements: Vec<Felt> = vm
        .get_integer_range(output_start, size)?
        .into_iter()
        .map(|v| v.into_owned())
        .collect();

    let dump_path: PathBuf = exec_scopes.get(vars::OUTPUT_PREIMAGE_DUMP_PATH)?;
    let json = serde_json::to_string_pretty(&elements).map_err(|e| {
        HintError::CustomHint(format!("Failed to serialize output preimage: {e}").into())
    })?;
    std::fs::write(&dump_path, json).map_err(|e| {
        HintError::CustomHint(
            format!("Failed to write output preimage to {dump_path:?}: {e}").into(),
        )
    })?;

    Ok(())
}
