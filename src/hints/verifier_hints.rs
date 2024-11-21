use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::insert_value_from_var_name;
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::vm::vm_core::VirtualMachine;
use cairo_vm::{types::exec_scope::ExecutionScopes, vm::errors::hint_errors::HintError};
use serde_json::from_value;
use std::collections::HashMap;

use super::types::{ExtractedProofValues, OwnedPublicInput};
use super::utils::gen_arg;
use super::verifier_utils::extract_from_ids_and_public_input;
use crate::hints::cairo_structs::ToVec;
use crate::hints::verifier_utils::{extract_proof_values, get_stark_proof_cairo_struct};

use super::utils::get_program_identifies;
use super::{CairoVerifierInput, PROGRAM_INPUT, PROGRAM_OBJECT};

/// Implements
///
/// %{
///     from starkware.cairo.stark_verifier.air.parser import parse_proof
///     ids.proof = segments.gen_arg(parse_proof(
///         identifiers=ids._context.identifiers,
///         proof_json=program_input["proof"]))
/// %}
pub fn load_and_parse_proof(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(PROGRAM_INPUT)?;

    let cairo_verifier_input: CairoVerifierInput =
        serde_json::from_str(program_input).map_err(|_| {
            HintError::CustomHint(
                "Failed to deserialize program_input into cairo_verifier_input".into(),
            )
        })?;

    // Retrieve verifier identifiers from execution scopes
    let verifier_identifiers = get_program_identifies(exec_scopes, PROGRAM_OBJECT)?;

    // Extract the "public_input" section from proof
    let public_input_json = cairo_verifier_input
        .proof
        .get("public_input")
        .ok_or_else(|| HintError::CustomHint("Missing 'public_input' in proof JSON.".into()))?;

    // Deserialize "public_input" JSON to OwnedPublicInput struct
    let public_input: OwnedPublicInput = from_value(public_input_json.clone())
        .map_err(|_| HintError::CustomHint("Failed to deserialize 'public_input' JSON.".into()))?;

    // Extract proof values into a struct
    let extracted_proof_vals: ExtractedProofValues =
        extract_proof_values(&cairo_verifier_input.proof)?;

    // Extract identifiers and public input values
    let extracted_ids_and_pub_in_vals = extract_from_ids_and_public_input(
        &public_input,
        &verifier_identifiers,
        &extracted_proof_vals,
    )?;

    // Generate the Cairo-compatible Stark proof structure
    let stark_proof_cairo_struct = get_stark_proof_cairo_struct(
        &extracted_proof_vals,
        &extracted_ids_and_pub_in_vals,
        &public_input,
    )?;
    let proof_relocatable = gen_arg(vm, &stark_proof_cairo_struct.to_vec())?;

    insert_value_from_var_name("proof", proof_relocatable, vm, ids_data, ap_tracking)?;

    Ok(())
}
