pub mod consts;
#[cfg(test)]
mod tests;

use std::error::Error;
use std::path::PathBuf;

use anyhow::Result;
use cairo_air::verifier::INTERACTION_POW_BITS;
use cairo_vm::types::program::Program;
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
use circuits::context::Context;
use circuits::ivalue::{IValue, NoValue};
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::empty_component::EmptyComponent;
use circuits_stark_verifier::proof::ProofConfig;
use circuits_stark_verifier::proof_from_stark_proof::pack_into_qm31s;
use starknet_types_core::felt::Felt;
use starknet_types_core::hash::Blake2Felt252;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo_cairo_common::prover_types::cpu::{FELT252_N_WORDS, Felt252};
use tracing::{Level, info, span};

use crate::consts::{
    CAIRO_PCS_CONFIG, CIRCUIT_FRI_CONFIG, LIFTING_LOG_SIZE, NUM_OUTPUTS, PRIVACY_BOOTLOADER_PATH,
    PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT, PRIVACY_TRANSACTION_COMPONENTS,
};

pub struct PrivacyProofOutput {
    pub proof: Vec<u32>,
    pub output_preimage: Vec<Felt>,
}

pub struct CircuitVerifierConfigs {
    pub preprocessed_circuit: PreprocessedCircuit,
    pub novalue_context: Context<NoValue>,
    pub circuit_config: CircuitConfig,
    pub proof_config: ProofConfig,
}

pub fn verify_privacy_bootloader(
    proof_output: &PrivacyProofOutput,
) -> Result<Context<QM31>, Box<dyn Error>> {
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
    let context = verify_fixed_cairo_circuit(
        &verifier_config,
        proof,
        public_claim.to_vec(),
        vec![outputs],
    )?;

    Ok(context)
}

pub fn verify_privacy_circuit(
    proof_output: &PrivacyProofOutput,
) -> Result<Context<QM31>, Box<dyn Error>> {
    let _span = span!(Level::INFO, "verify_privacy_circuit").entered();

    let cairo_verifier_config = get_cairo_verifier_config()?;
    let circuit_verifier_configs = get_circuit_verifier_configs(&cairo_verifier_config);

    info!("Deserialize the proof");
    let mut serialized_proof: &[u32] = &proof_output.proof;
    let proof = deserialize_proof_with_config(
        &mut serialized_proof,
        &circuit_verifier_configs.proof_config,
    )?;
    if !serialized_proof.is_empty() {
        return Err("Proof deserialization failed".into());
    }

    info!("Compute the output values");
    let outputs = compute_privacy_bootloader_output(&proof_output.output_preimage);
    let output_qm31s = pack_into_qm31s(outputs.into_iter());
    let output_hash = QM31::blake(output_qm31s.as_slice(), output_qm31s.len() * 16);
    let constants = circuit_verifier_configs
        .novalue_context
        .constants()
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let constants_hash = QM31::blake(constants.as_slice(), constants.len() * 16);
    let output_values = vec![
        output_hash.0,
        output_hash.1,
        constants_hash.0,
        constants_hash.1,
    ];

    info!("Call the verifier");
    let context = verify_circuit(
        circuit_verifier_configs.circuit_config,
        proof,
        CircuitPublicData { output_values },
    )?;

    Ok(context)
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

    Ok(CairoVerifierConfig {
        proof_config: cairo_proof_config,
        program,
        n_outputs: NUM_OUTPUTS,
        preprocessed_root: get_preprocessed_root(LIFTING_LOG_SIZE),
    })
}

pub fn get_privacy_bootloader_program() -> Result<Program, Box<dyn Error>> {
    let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let bootloader_compiled_path = project_dir.join(PRIVACY_BOOTLOADER_PATH);
    let bootloader_program = Program::from_file(bootloader_compiled_path.as_path(), Some("main"))?;
    Ok(bootloader_program)
}

pub fn compute_privacy_bootloader_output(output_preimage: &[Felt]) -> [M31; FELT252_N_WORDS] {
    let output = Blake2Felt252::encode_felt252_data_and_calc_blake_hash(output_preimage);
    Felt252::from(output).get_limbs()
}

pub fn get_circuit_verifier_configs(
    cairo_verifier_config: &CairoVerifierConfig,
) -> CircuitVerifierConfigs {
    // Get the preprocessed circuit
    let mut novalue_context = build_cairo_verifier_circuit(cairo_verifier_config);
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut novalue_context);

    // Get the circuit config
    let lifting_log_size =
        preprocessed_circuit.params.trace_log_size + CIRCUIT_FRI_CONFIG.log_blowup_factor;
    let circuit_pcs_config = PcsConfig {
        pow_bits: CIRCUIT_INTERACTION_POW_BITS,
        fri_config: CIRCUIT_FRI_CONFIG,
        lifting_log_size: Some(lifting_log_size),
    };
    let circuit_config = CircuitConfig {
        config: circuit_pcs_config,
        output_addresses: preprocessed_circuit.params.output_addresses.clone(),
        n_blake_gates: preprocessed_circuit.params.n_blake_gates,
        preprocessed_column_ids: preprocessed_circuit.preprocessed_trace.ids(),
        preprocessed_root: PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT.into(),
    };

    // Get the proof config
    let proof_config = ProofConfig::from_components(
        &all_circuit_components::<QM31>(),
        preprocessed_circuit.preprocessed_trace.ids().len(),
        &circuit_pcs_config,
        CIRCUIT_INTERACTION_POW_BITS,
    );

    CircuitVerifierConfigs {
        preprocessed_circuit,
        novalue_context,
        circuit_config,
        proof_config,
    }
}
