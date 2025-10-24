use std::collections::HashMap;

use cairo_vm::{
    hint_processor::{
        hint_processor_definition::HintReference,
        builtin_hint_processor::sha256_utils::sha256_finalize,
        builtin_hint_processor::hint_utils::get_ptr_from_var_name,
    },
    serde::deserialize_program::ApTracking,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
};

const SHA256_INPUT_CHUNK_SIZE_FELTS: usize = 16;
const SHA256_STATE_SIZE_FELTS: usize = 8;
const SHA256_INSTANCE_SIZE: usize = SHA256_INPUT_CHUNK_SIZE_FELTS + 2 * SHA256_STATE_SIZE_FELTS;

/// Implements hint: %{ SHA256_DEBUG }
pub fn sha256_debug(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {

    // Get the pointer values for sha256_array_start and sha256_array_end
    let sha256_array_start = get_ptr_from_var_name("sha256_array_start", vm, ids_data, ap_tracking)?;
    let sha256_array_end = get_ptr_from_var_name("sha256_array_end", vm, ids_data, ap_tracking)?;
    let diff = (sha256_array_end - sha256_array_start)?;

    // Print the values
    println!("=== debug sha256 ===");
    println!("sha256_array_start: {:?}", sha256_array_start);
    println!("sha256_array_end: {:?}", sha256_array_end);
    println!("sha256_array_end - sha256_array_start: {:?}", diff);
    println!("sha2 instances: {:?}", diff / SHA256_INSTANCE_SIZE);
    println!("====================");

    Ok(())
}

/// Implements hint: %{ SHA256_FINALIZE }
pub fn sha2_finalize(
    vm: &mut VirtualMachine,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // All the logic that is needed here is already implemented in cairo-vm
    // Check sha256_utils.rs for implementation details
    sha256_finalize(vm, ids_data, ap_tracking)?;

    Ok(())
} 