pub mod consts;
#[cfg(test)]
mod tests;
pub mod utils;

use std::error::Error;
use std::sync::Arc;

use anyhow::Result;
use cairo_air::verifier::INTERACTION_POW_BITS;
use cairo_vm::types::program::Program;
use circuit_cairo_verifier::all_components::all_components;
use circuit_cairo_verifier::statement::AUX_DATA_FIXED_LEN;
use circuit_cairo_verifier::verify::{
    CairoVerifierConfig, build_cairo_verifier_circuit, get_preprocessed_root,
    verify_fixed_cairo_circuit,
};
use circuit_common::finalize::add_zk_blinding;
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuit_verifier::components::prelude::PreProcessedColumnId;
use circuit_verifier::statement::{
    INTERACTION_POW_BITS as CIRCUIT_INTERACTION_POW_BITS, all_circuit_components,
};
use circuit_verifier::verify::{CircuitConfig, CircuitPublicData, verify_circuit};
use circuits::context::FinalizedContext;
use circuits::ivalue::IValue;
use circuits::ivalue::NoValue;
use circuits_stark_verifier::proof::ProofConfig;
use circuits_stark_verifier::proof_from_stark_proof::pack_into_qm31s;
use itertools::Itertools;
use starknet_types_core::felt::Felt;
use starknet_types_core::hash::Blake2Felt252;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTraceVariant;
use stwo_cairo_common::prover_types::cpu::{FELT252_N_WORDS, Felt252};
use tracing::{Level, info, span};

use crate::consts::{
    CAIRO_PCS_CONFIG, CIRCUIT_FRI_CONFIG, CIRCUIT_OUTPUT_ADDRESSES, CIRCUIT_PCS_CONFIG,
    MAX_CAIRO_PROOF_UNCOMPRESSED_BYTES, MAX_RECURSIVE_PROOF_UNCOMPRESSED_BYTES, NUM_OUTPUTS,
    PRIVACY_BOOTLOADER_JSON, PRIVACY_CIRCUIT_PREPROCESSED_IDS,
    PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES, PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT,
    PRIVACY_TRANSACTION_COMPONENTS,
};

pub use utils::{VERSION_BYTES, Version};

pub struct PrivacyProofOutput {
    /// Proof bytes, laid out as the serialized [`Version`] of the `privacy-prove` crate that
    /// generated the proof, followed by the compressed proof. The format must be consistent
    /// between the prover and verifier:
    /// - `privacy_prove` / `verify_cairo`
    /// - `privacy_recursive_prove` / `verify_recursive_circuit`
    pub proof: Vec<u8>,
    pub output_preimage: Vec<Felt>,
}

/// Splits the version-prefixed proof bytes into the embedded [`Version`] and the remaining
/// compressed proof bytes.
pub(crate) fn split_proof_version(proof: &[u8]) -> Result<(Version, &[u8]), Box<dyn Error>> {
    let (version_bytes, compressed_proof) = proof
        .split_first_chunk::<VERSION_BYTES>()
        .ok_or("Proof is too short to contain a version")?;
    Ok((Version::deserialize(*version_bytes), compressed_proof))
}

pub(crate) fn decompress_proof(
    compressed: &[u8],
    max_bytes: usize,
) -> Result<Vec<u8>, Box<dyn Error>> {
    Ok(zstd::bulk::decompress(compressed, max_bytes)?)
}

pub fn verify_cairo(proof_output: &PrivacyProofOutput) -> Result<(), Box<dyn Error>> {
    let _span = span!(Level::INFO, "verify_privacy_bootloader").entered();

    let verifier_config = get_cairo_verifier_config()?;

    info!("Decompress and deserialize the proof");
    let (_version, compressed_proof) = split_proof_version(&proof_output.proof)?;
    let proof_bytes = decompress_proof(compressed_proof, MAX_CAIRO_PROOF_UNCOMPRESSED_BYTES)?;
    let bootloader_program = get_privacy_bootloader_program()?;
    let program_len = bootloader_program.data_len();
    let n_components = verifier_config.proof_config.n_components();
    let (serialized_aux_data_bytes, serialized_proof_bytes) =
        proof_bytes.split_at((AUX_DATA_FIXED_LEN + NUM_OUTPUTS + program_len + n_components) * 4);
    let serialized_aux_data: Vec<M31> = serialized_aux_data_bytes
        .chunks_exact(4)
        .map(|c| M31::from(u32::from_le_bytes(c.try_into().unwrap())))
        .collect();
    let mut serialized_proof: &[u8] = serialized_proof_bytes;
    let proof =
        deserialize_proof_with_config(&mut serialized_proof, &verifier_config.proof_config)?;
    if !serialized_proof.is_empty() {
        return Err("Proof deserialization failed".into());
    }

    info!("Compute the output");
    let outputs = compute_privacy_bootloader_output(&proof_output.output_preimage);

    info!("Call the verifier");
    verify_fixed_cairo_circuit(&verifier_config, proof, serialized_aux_data, vec![outputs])?;

    Ok(())
}

pub fn verify_recursive_circuit(proof_output: &PrivacyProofOutput) -> Result<(), Box<dyn Error>> {
    let _span = span!(Level::INFO, "verify_privacy_circuit").entered();

    let circuit_config = get_recursive_circuit_config();
    let proof_config = get_proof_config();

    info!("Decompress and deserialize the proof");
    let (_version, compressed_proof) = split_proof_version(&proof_output.proof)?;
    let proof_bytes = decompress_proof(compressed_proof, MAX_RECURSIVE_PROOF_UNCOMPRESSED_BYTES)?;
    let mut serialized_proof: &[u8] = &proof_bytes;
    let proof = deserialize_proof_with_config(&mut serialized_proof, &proof_config)?;
    if !serialized_proof.is_empty() {
        return Err("Proof deserialization failed".into());
    }

    info!("Compute the output values");
    let outputs = compute_privacy_bootloader_output(&proof_output.output_preimage);
    let output_qm31s = pack_into_qm31s(outputs.into_iter());
    let output_hash = QM31::blake2s(&output_qm31s, output_qm31s.len() * 16);
    // The circuit outputs the full unreduced Blake2s digest (8 words) at the reserved output
    // wires. The `u` anchor wire is appended internally by the verifier, so it must not be part
    // of `output_values`.
    let output_values: Vec<QM31> = output_hash.iter().map(|w| *w.get()).collect();

    info!("Call the verifier");
    verify_circuit(circuit_config, proof, CircuitPublicData { output_values })?;

    Ok(())
}

/// Returns, for each component in `all_components()` order, whether it is enabled in the privacy
/// transaction.
fn get_cairo_enabled_bits() -> Vec<bool> {
    all_components::<NoValue>()
        .keys()
        .map(|name| PRIVACY_TRANSACTION_COMPONENTS.contains(name))
        .collect()
}

pub fn get_cairo_proof_config() -> ProofConfig {
    let enabled_components = all_components::<NoValue>()
        .into_iter()
        .filter(|(name, _)| PRIVACY_TRANSACTION_COMPONENTS.contains(name))
        .collect();

    ProofConfig::new(
        &enabled_components,
        PreProcessedTraceVariant::CanonicalSmall.n_columns(),
        &CAIRO_PCS_CONFIG,
        INTERACTION_POW_BITS,
    )
}

pub fn get_cairo_verifier_config() -> Result<CairoVerifierConfig, Box<dyn Error>> {
    let cairo_proof_config = get_cairo_proof_config();
    let enabled_bits = get_cairo_enabled_bits();

    let bootloader_program = get_privacy_bootloader_program()?;
    let mut program_entries = vec![];
    for value in bootloader_program.iter_data() {
        let value = value.get_int().ok_or("Failed to get value")?;
        program_entries.push(Felt252::from(value).get_limbs());
    }

    let cairo_lifting_log_size: u32 = cairo_proof_config.fri.log_evaluation_domain_size() as u32;
    let preprocessed_trace_variant = PreProcessedTraceVariant::CanonicalSmall;

    Ok(CairoVerifierConfig {
        proof_config: cairo_proof_config,
        enabled_bits,
        program: Arc::from(program_entries.as_slice()),
        n_outputs: NUM_OUTPUTS,
        preprocessed_root: get_preprocessed_root(cairo_lifting_log_size),
        preprocessed_trace_variant,
    })
}

pub fn get_privacy_bootloader_program() -> Result<Program, Box<dyn Error>> {
    let bootloader_program = Program::from_bytes(PRIVACY_BOOTLOADER_JSON, Some("main"))?;
    Ok(bootloader_program)
}

pub fn compute_privacy_bootloader_output(output_preimage: &[Felt]) -> [M31; FELT252_N_WORDS] {
    let output = Blake2Felt252::encode_felt252_data_and_calc_blake_hash(output_preimage);
    Felt252::from(output).get_limbs()
}

pub fn get_recursive_circuit_config() -> CircuitConfig {
    let preprocessed_column_log_sizes = PRIVACY_CIRCUIT_PREPROCESSED_IDS
        .iter()
        .zip_eq(PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES.iter())
        .map(|(&id, &log_size)| (PreProcessedColumnId { id: id.to_string() }, log_size))
        .collect();
    CircuitConfig {
        config: CIRCUIT_PCS_CONFIG,
        // `n_outputs` counts only the real output gates (the hash at addresses 3 and 4); the `u`
        // anchor wire (address 2, also in `CIRCUIT_OUTPUT_ADDRESSES`) is appended by the verifier.
        n_outputs: CIRCUIT_OUTPUT_ADDRESSES.len() - 1,
        preprocessed_column_log_sizes,
        preprocessed_root: PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT.into(),
    }
}

pub fn get_proof_config() -> ProofConfig {
    let components = all_circuit_components::<QM31>();
    ProofConfig::new(
        &components,
        PRIVACY_CIRCUIT_PREPROCESSED_IDS.len(),
        &CIRCUIT_PCS_CONFIG,
        CIRCUIT_INTERACTION_POW_BITS,
    )
}

pub fn get_cairo_preprocessed_circuit(
    cairo_verifier_config: &CairoVerifierConfig,
) -> PreprocessedCircuit {
    let mut novalue_context = get_cairo_novalue_context(cairo_verifier_config);
    PreprocessedCircuit::preprocess_circuit(&mut novalue_context)
}

fn get_cairo_novalue_context(
    cairo_verifier_config: &CairoVerifierConfig,
) -> FinalizedContext<NoValue> {
    let mut novalue_context = build_cairo_verifier_circuit(cairo_verifier_config);
    // [0; 32] is a stub seed to get the correct circuit structure. In practice, we will use a
    // random seed.
    add_zk_blinding(&mut novalue_context, [0; 32], CIRCUIT_FRI_CONFIG.n_queries);
    novalue_context
}
