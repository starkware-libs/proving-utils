use cairo_vm::{types::exec_scope::ExecutionScopes, vm::errors::hint_errors::HintError};
use std::collections::HashMap;

use super::utils::get_program_identifies;
use super::VERIFIER_PROOF_INPUT;

/// Implements
///
/// %{
///     from starkware.cairo.stark_verifier.air.parser import parse_proof
///     ids.proof = segments.gen_arg(parse_proof(
///         identifiers=ids._context.identifiers,
///         proof_json=program_input["proof"]))
/// %}
pub fn load_and_parse_proof(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let _proof: HashMap<String, serde_json::Value> = exec_scopes.get(VERIFIER_PROOF_INPUT)?;
    let _verifier_identifiers = get_program_identifies(exec_scopes)?;

    // TODO: Add the rest of the logic here

    Ok(())
}
