use cairo_vm::{types::exec_scope::ExecutionScopes, vm::errors::hint_errors::HintError};
use std::collections::HashMap;

use super::utils::get_program_identifies;
use super::VERIFIER_PROOF_INPUT;

pub fn load_and_parse_proof(exec_scopes: &mut ExecutionScopes) -> Result<(), HintError> {
    let _proof: HashMap<String, serde_json::Value> = exec_scopes.get(VERIFIER_PROOF_INPUT)?;
    let _verifier_identifiers = get_program_identifies(exec_scopes)?;

    // TODO: Add the rest of the logic here

    Ok(())
}
