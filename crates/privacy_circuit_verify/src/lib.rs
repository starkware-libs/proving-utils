pub mod consts;
#[cfg(test)]
mod tests;

use std::error::Error;
use std::path::PathBuf;

use anyhow::Result;
use cairo_air::verifier::INTERACTION_POW_BITS;
use cairo_vm::types::program::Program;
use circuit_cairo_air::all_components::all_components;
use circuit_cairo_air::preprocessed_columns::PREPROCESSED_COLUMNS_ORDER;
use circuit_cairo_air::statement::PUBLIC_DATA_LEN;
use circuit_cairo_air::verify::{
    CairoVerifierConfig, get_preprocessed_root, verify_fixed_cairo_circuit,
};
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::empty_component::EmptyComponent;
use circuits_stark_verifier::proof::ProofConfig;
use starknet_types_core::felt::Felt;
use starknet_types_core::hash::Blake2Felt252;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_cairo_common::prover_types::cpu::{FELT252_N_WORDS, Felt252};
use tracing::{Level, info, span};

use crate::consts::{
    LIFTING_LOG_SIZE, NUM_OUTPUTS, PCS_CONFIG, PRIVACY_BOOTLOADER_PATH,
    PRIVACY_TRANSACTION_COMPONENTS,
};

pub struct PrivacyProofOutput {
    pub proof: Vec<u32>,
    pub output_preimage: Vec<Felt>,
}

pub fn verify(proof_output: &PrivacyProofOutput) -> Result<(), Box<dyn Error>> {
    let _span = span!(Level::INFO, "privacy_circuit_verify").entered();

    info!("Deserialize the proof");
    let bootloader_program = get_privacy_bootloader_program()?;
    let program_len = bootloader_program.data_len();
    let (public_claim, mut serialized_proof) = proof_output
        .proof
        .split_at(PUBLIC_DATA_LEN + NUM_OUTPUTS + program_len);
    let proof_config = get_proof_config();
    let proof = deserialize_proof_with_config(&mut serialized_proof, &proof_config)?;
    if !serialized_proof.is_empty() {
        return Err("Proof deserialization failed".into());
    }

    info!("Compute the bootloader output");
    let output =
        Blake2Felt252::encode_felt252_data_and_calc_blake_hash(&proof_output.output_preimage);
    let outputs: [M31; FELT252_N_WORDS] = Felt252::from(output).get_limbs();

    info!("Prepare the program");
    let mut program = vec![];
    for value in bootloader_program.iter_data() {
        let value = value.get_int().ok_or("Failed to get value")?;
        program.push(Felt252::from(value).get_limbs());
    }

    let verifier_config = CairoVerifierConfig {
        proof_config,
        program,
        n_outputs: NUM_OUTPUTS,
        preprocessed_root: get_preprocessed_root(LIFTING_LOG_SIZE),
    };

    info!("Call the verifier");
    verify_fixed_cairo_circuit(verifier_config, proof, public_claim.to_vec(), vec![outputs])?;

    Ok(())
}

pub fn get_proof_config() -> ProofConfig {
    let components: Vec<Box<dyn CircuitEval<QM31>>> = all_components::<QM31>()
        .into_iter()
        .map(|(component_name, component)| {
            let component_in_set = PRIVACY_TRANSACTION_COMPONENTS.contains(&component_name);
            if component_in_set {
                component
            } else {
                Box::new(EmptyComponent {})
            }
        })
        .collect();

    ProofConfig::from_components(
        &components,
        PREPROCESSED_COLUMNS_ORDER.len(),
        &PCS_CONFIG,
        INTERACTION_POW_BITS,
    )
}

pub fn get_privacy_bootloader_program() -> Result<Program, Box<dyn Error>> {
    let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let bootloader_compiled_path = project_dir.join(PRIVACY_BOOTLOADER_PATH);
    let bootloader_program = Program::from_file(bootloader_compiled_path.as_path(), Some("main"))?;
    Ok(bootloader_program)
}
