pub mod consts;
#[cfg(test)]
mod tests;

use std::error::Error;

use anyhow::Result;
use cairo_air::verifier::INTERACTION_POW_BITS;
use cairo_vm::types::program::Program;
use circuit_air::components::prelude::PreProcessedColumnId;
use circuit_air::statement::{
    INTERACTION_POW_BITS as CIRCUIT_INTERACTION_POW_BITS, all_circuit_components,
};
use circuit_air::verify::{CircuitConfig, CircuitPublicData, verify_circuit};
use circuit_cairo_air::all_components::all_components;
use circuit_cairo_air::preprocessed_columns::PREPROCESSED_COLUMNS_ORDER;
use circuit_cairo_air::statement::PUBLIC_DATA_LEN;
use circuit_cairo_air::verify::{
    CairoVerifierConfig, build_cairo_verifier_circuit, get_preprocessed_root,
    verify_fixed_cairo_circuit,
};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuits::blake::HashValue;
use circuits::ivalue::IValue;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::empty_component::EmptyComponent;
use circuits_stark_verifier::proof::ProofConfig;
use circuits_stark_verifier::proof_from_stark_proof::pack_into_qm31s;
use starknet_types_core::felt::Felt;
use starknet_types_core::hash::Blake2Felt252;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_cairo_common::prover_types::cpu::{FELT252_N_WORDS, Felt252};
use tracing::{Level, info, span};

use crate::consts::{
    CAIRO_PCS_CONFIG, CIRCUIT_N_BLAKE_GATES, CIRCUIT_OUTPUT_ADDRESSES, CIRCUIT_PCS_CONFIG,
    NUM_OUTPUTS, PRIVACY_BOOTLOADER_BYTES, PRIVACY_CAIRO_VERIFIER_CONSTS_HASH,
    PRIVACY_CIRCUIT_PREPROCESSED_IDS, PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT,
    PRIVACY_TRANSACTION_COMPONENTS,
};

pub struct PrivacyProofOutput {
    pub proof: Vec<u32>,
    pub output_preimage: Vec<Felt>,
}

pub fn verify_cairo(proof_output: &PrivacyProofOutput) -> Result<(), Box<dyn Error>> {
    let _span = span!(Level::INFO, "verify_privacy_bootloader").entered();

    let verifier_config = get_cairo_verifier_config()?;

    info!("Deserialize the proof");
    let bootloader_program = get_privacy_bootloader_program()?;
    let program_len = bootloader_program.data_len();
    let (public_claim, mut serialized_proof) = proof_output
        .proof
        .split_at(PUBLIC_DATA_LEN + NUM_OUTPUTS + program_len);
    let proof =
        deserialize_proof_with_config(&mut serialized_proof, &verifier_config.proof_config)?;
    if !serialized_proof.is_empty() {
        return Err("Proof deserialization failed".into());
    }

    info!("Compute the output");
    let outputs = compute_privacy_bootloader_output(&proof_output.output_preimage);

    info!("Call the verifier");
    verify_fixed_cairo_circuit(
        &verifier_config,
        proof,
        public_claim.to_vec(),
        vec![outputs],
    )?;

    Ok(())
}

pub fn verify_recursive_circuit(proof_output: &PrivacyProofOutput) -> Result<(), Box<dyn Error>> {
    let _span = span!(Level::INFO, "verify_privacy_circuit").entered();

    let circuit_config = get_recursive_circuit_config();
    let proof_config = get_proof_config();

    info!("Deserialize the proof");
    let mut serialized_proof: &[u32] = &proof_output.proof;
    let proof = deserialize_proof_with_config(&mut serialized_proof, &proof_config)?;
    if !serialized_proof.is_empty() {
        return Err("Proof deserialization failed".into());
    }

    info!("Compute the output values");
    let outputs = compute_privacy_bootloader_output(&proof_output.output_preimage);
    let output_qm31s = pack_into_qm31s(outputs.into_iter());
    let output_hash = QM31::blake(output_qm31s.as_slice(), output_qm31s.len() * 16);
    let constants_hash: HashValue<QM31> = PRIVACY_CAIRO_VERIFIER_CONSTS_HASH.into();
    let output_values = vec![
        output_hash.0,
        output_hash.1,
        constants_hash.0,
        constants_hash.1,
    ];

    info!("Call the verifier");
    verify_circuit(circuit_config, proof, CircuitPublicData { output_values })?;

    Ok(())
}

pub fn get_cairo_proof_config() -> ProofConfig {
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
        &CAIRO_PCS_CONFIG,
        INTERACTION_POW_BITS,
    )
}

pub fn get_cairo_verifier_config() -> Result<CairoVerifierConfig, Box<dyn Error>> {
    // Get the cairo proof config
    let cairo_proof_config = get_cairo_proof_config();

    // Get the bootloader program
    let bootloader_program = get_privacy_bootloader_program()?;
    let mut program = vec![];
    for value in bootloader_program.iter_data() {
        let value = value.get_int().ok_or("Failed to get value")?;
        program.push(Felt252::from(value).get_limbs());
    }

    let cairo_lifting_log_size: u32 = cairo_proof_config.fri.log_evaluation_domain_size() as u32;

    Ok(CairoVerifierConfig {
        proof_config: cairo_proof_config,
        program,
        n_outputs: NUM_OUTPUTS,
        preprocessed_root: get_preprocessed_root(cairo_lifting_log_size),
    })
}

pub fn get_privacy_bootloader_program() -> Result<Program, Box<dyn Error>> {
    let bootloader_program = Program::from_bytes(PRIVACY_BOOTLOADER_BYTES, Some("main"))?;
    Ok(bootloader_program)
}

pub fn compute_privacy_bootloader_output(output_preimage: &[Felt]) -> [M31; FELT252_N_WORDS] {
    let output = Blake2Felt252::encode_felt252_data_and_calc_blake_hash(output_preimage);
    Felt252::from(output).get_limbs()
}

pub fn get_recursive_circuit_config() -> CircuitConfig {
    CircuitConfig {
        config: CIRCUIT_PCS_CONFIG,
        output_addresses: CIRCUIT_OUTPUT_ADDRESSES.to_vec(),
        n_blake_gates: CIRCUIT_N_BLAKE_GATES,
        preprocessed_column_ids: PRIVACY_CIRCUIT_PREPROCESSED_IDS
            .iter()
            .map(|id| PreProcessedColumnId { id: id.to_string() })
            .collect(),
        preprocessed_root: PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT.into(),
    }
}

pub fn get_proof_config() -> ProofConfig {
    ProofConfig::from_components(
        &all_circuit_components::<QM31>(),
        PRIVACY_CIRCUIT_PREPROCESSED_IDS.len(),
        &CIRCUIT_PCS_CONFIG,
        CIRCUIT_INTERACTION_POW_BITS,
    )
}

pub fn get_preprocessed_cairo_circuit(
    cairo_verifier_config: &CairoVerifierConfig,
) -> PreprocessedCircuit {
    let mut novalue_context = build_cairo_verifier_circuit(cairo_verifier_config);
    PreprocessedCircuit::preprocess_circuit(&mut novalue_context)
}
