use circuit_air::statement::{
    INTERACTION_POW_BITS as CIRCUIT_INTERACTION_POW_BITS, all_circuit_components,
};
use circuit_air::verify::CircuitConfig;
use circuit_cairo_air::all_components::all_components;
use circuits_stark_verifier::proof::ProofConfig;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;

use crate::consts::{
    CIRCUIT_FRI_CONFIG, CIRCUIT_LOG_BLOWUP_FACTOR, CIRCUIT_PCS_CONFIG,
    PRIVACY_CAIRO_VERIFIER_CONSTS_HASH, PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT,
    PRIVACY_TRANSACTION_COMPONENTS,
};
use crate::{
    build_cairo_verifier_circuit, get_cairo_verifier_config, get_preprocessed_cairo_circuit,
    get_proof_config, get_recursive_circuit_config,
};
use circuits::ivalue::IValue;

#[test]
fn check_components() {
    let all_components = all_components::<QM31>();
    for component_name in PRIVACY_TRANSACTION_COMPONENTS {
        assert!(
            all_components.contains_key(component_name),
            "Component {component_name} is not in the all_components"
        );
    }
}

#[test]
fn check_cairo_circuit_verifier_constants() {
    let cairo_verifier_config = get_cairo_verifier_config().unwrap();
    let novalue_context = build_cairo_verifier_circuit(&cairo_verifier_config);
    let constants = novalue_context
        .constants()
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let constants_hash = QM31::blake(constants.as_slice(), constants.len() * 16);

    assert_eq!(constants_hash, PRIVACY_CAIRO_VERIFIER_CONSTS_HASH.into());
}

#[test]
fn check_circuit_verifier_configs() {
    let cairo_verifier_config = get_cairo_verifier_config().unwrap();
    let preprocessed_circuit = get_preprocessed_cairo_circuit(&cairo_verifier_config);

    // compute the circuit config
    let lifting_log_size = preprocessed_circuit.params.trace_log_size + CIRCUIT_LOG_BLOWUP_FACTOR;
    let circuit_pcs_config = PcsConfig {
        pow_bits: CIRCUIT_PCS_CONFIG.pow_bits,
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

    // compute the proof config
    let proof_config = ProofConfig::from_components(
        &all_circuit_components::<QM31>(),
        preprocessed_circuit.preprocessed_trace.ids().len(),
        &circuit_pcs_config,
        CIRCUIT_INTERACTION_POW_BITS,
    );

    assert_eq!(circuit_config, get_recursive_circuit_config());
    assert_eq!(proof_config, get_proof_config());
}
