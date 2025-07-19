use std::collections::HashMap;

use cairo_vm::{
    hint_processor::{
        hint_processor_definition::HintReference,
        builtin_hint_processor::sha256_utils::sha256_finalize,
    },
    serde::deserialize_program::ApTracking,
    vm::{errors::hint_errors::HintError, vm_core::VirtualMachine},
};

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