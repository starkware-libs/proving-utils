use circuit_cairo_verifier::all_components::all_components;
use circuits::blake::HashValue;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::circle::PolyOps;

use crate::consts::{
    CAIRO_LOG_BLOWUP_FACTOR, CAIRO_PCS_CONFIG, CAIRO_TRACE_LOG_SIZE, CIRCUIT_LOG_BLOWUP_FACTOR,
    CIRCUIT_OUTPUT_ADDRESSES, CIRCUIT_PCS_CONFIG, CIRCUIT_TRACE_LOG_SIZE,
    PRIVACY_CIRCUIT_PREPROCESSED_IDS, PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES,
    PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT, PRIVACY_TRANSACTION_COMPONENTS,
};
use crate::{
    get_cairo_preprocessed_circuit, get_cairo_verifier_config, get_proof_config,
    get_recursive_circuit_config,
};

const CONJECTURED_SECURITY_BITS: u32 = 96;

#[test]
fn check_proof_config() {
    let proof_config = get_proof_config();
    // All circuit components should be enabled.
    assert!(
        proof_config
            .component_shapes
            .iter()
            .all(|s| s.trace_columns > 0)
    );
}

#[test]
fn check_recursive_circuit_config_log_sizes() {
    let config = get_recursive_circuit_config();
    let log_sizes: Vec<u32> = config
        .preprocessed_column_log_sizes
        .values()
        .copied()
        .collect();
    assert_eq!(log_sizes.as_slice(), PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES);
}

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
fn check_privacy_recursion_circuit_preprocessed_root() {
    let cairo_verifier_config = get_cairo_verifier_config().unwrap();
    let preprocessed_circuit = get_cairo_preprocessed_circuit(&cairo_verifier_config);
    let preprocessed_trace = preprocessed_circuit
        .preprocessed_trace
        .get_trace::<SimdBackend>();
    let max_domain_size = CIRCUIT_PCS_CONFIG.lifting_log_size.unwrap();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_domain_size)
            .circle_domain()
            .half_coset,
    );
    let preprocessed_trace_polys = SimdBackend::interpolate_columns(preprocessed_trace, &twiddles);
    let store_polynomials_coefficients = true;
    let base_column_pool = BaseColumnPool::<SimdBackend>::new();
    let preprocessed_tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        preprocessed_trace_polys,
        CIRCUIT_PCS_CONFIG.fri_config.log_blowup_factor,
        &twiddles,
        store_polynomials_coefficients,
        CIRCUIT_PCS_CONFIG.lifting_log_size,
        &base_column_pool,
    );
    let expected_root: HashValue<QM31> = preprocessed_tree.commitment.root().into();

    assert_eq!(
        expected_root,
        PRIVACY_RECURSION_CIRCUIT_PREPROCESSED_ROOT.into()
    );
}

#[test]
fn check_circuit_verifier_configs() {
    let cairo_verifier_config = get_cairo_verifier_config().unwrap();
    let preprocessed_circuit = get_cairo_preprocessed_circuit(&cairo_verifier_config);

    // Compare fields of the circuit config that are easily computed from the preprocessed circuit
    // to the expected values
    assert_eq!(
        preprocessed_circuit.trace_log_size + CIRCUIT_LOG_BLOWUP_FACTOR,
        CIRCUIT_PCS_CONFIG.lifting_log_size.unwrap()
    );
    // `params.n_outputs` counts the circuit output gates excluding the `u` constant wire, while
    // `CIRCUIT_OUTPUT_ADDRESSES` includes the `u` anchor address.
    assert_eq!(
        preprocessed_circuit.n_outputs,
        CIRCUIT_OUTPUT_ADDRESSES.len() - 1
    );
    let preprocessed_column_ids: Vec<String> = preprocessed_circuit
        .preprocessed_trace
        .ids()
        .into_iter()
        .map(|id| id.id)
        .collect();
    assert_eq!(
        preprocessed_column_ids.as_slice(),
        PRIVACY_CIRCUIT_PREPROCESSED_IDS
    );
    let actual_log_sizes: Vec<u32> = preprocessed_circuit
        .preprocessed_trace
        .log_sizes()
        .values()
        .copied()
        .collect();
    assert_eq!(
        actual_log_sizes.as_slice(),
        PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES,
        "Update PRIVACY_CIRCUIT_PREPROCESSED_LOG_SIZES in consts.rs"
    );

    // Check that the lifting log sizes are correct
    assert!(
        CAIRO_TRACE_LOG_SIZE + CAIRO_LOG_BLOWUP_FACTOR
            == CAIRO_PCS_CONFIG.lifting_log_size.unwrap()
    );
    assert!(
        CIRCUIT_TRACE_LOG_SIZE + CIRCUIT_LOG_BLOWUP_FACTOR
            == CIRCUIT_PCS_CONFIG.lifting_log_size.unwrap()
    );

    // Check that the circuit pcs config is secure enough
    assert!(
        CIRCUIT_PCS_CONFIG.pow_bits
            + CIRCUIT_PCS_CONFIG.fri_config.n_queries as u32
                * CIRCUIT_PCS_CONFIG.fri_config.log_blowup_factor
            >= CONJECTURED_SECURITY_BITS,
        "The recursive circuit pcs config is not secure enough."
    );

    assert!(
        CAIRO_PCS_CONFIG.pow_bits
            + CAIRO_PCS_CONFIG.fri_config.n_queries as u32
                * CAIRO_PCS_CONFIG.fri_config.log_blowup_factor
            >= CONJECTURED_SECURITY_BITS,
        "The cairo circuit pcs config is not secure enough."
    );
}

#[cfg(feature = "slow-tests")]
pub mod slow_tests {
    use std::path::PathBuf;

    use cairo_vm::vm::runners::cairo_pie::CairoPie;
    use privacy_prove::{prepare_recursive_prover_precomputes, privacy_recursive_prove};
    use tracing_subscriber::fmt;

    use crate::consts::{CAIRO_PROOF_UNCOMPRESSED_BYTES, RECURSIVE_PROOF_UNCOMPRESSED_BYTES};
    use crate::get_proof_config;

    #[test]
    fn check_recursive_circuit_proof_deserializes() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let pie_path = project_dir.join("../privacy_prove/test_data/privacy_tx_cairo_pie.zip");
        let pie = CairoPie::read_zip_file(&pie_path).unwrap();
        let precomputes = prepare_recursive_prover_precomputes().unwrap();
        let proof_output = privacy_recursive_prove(pie, precomputes).unwrap();

        let proof_config = get_proof_config();
        let proof_bytes = crate::decompress_proof(
            &proof_output.proof,
            crate::consts::MAX_RECURSIVE_PROOF_UNCOMPRESSED_BYTES,
        )
        .unwrap();
        let mut serialized_proof: &[u8] = &proof_bytes;
        circuit_serialize::deserialize::deserialize_proof_with_config(
            &mut serialized_proof,
            &proof_config,
        )
        .unwrap();
        assert!(serialized_proof.is_empty());
    }

    #[test]
    fn check_max_cairo_proof_uncompressed_size() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let pie_path = project_dir.join("../privacy_prove/test_data/privacy_tx_cairo_pie.zip");
        let pie = CairoPie::read_zip_file(&pie_path).unwrap();
        let proof_output = privacy_prove::privacy_prove(pie).unwrap();

        let proof_bytes = zstd::decode_all(proof_output.proof.as_slice()).unwrap();
        assert_eq!(
            proof_bytes.len(),
            CAIRO_PROOF_UNCOMPRESSED_BYTES,
            "Update CAIRO_PROOF_UNCOMPRESSED_BYTES in consts.rs to {}",
            proof_bytes.len()
        );
    }

    #[test]
    fn check_max_recursive_proof_uncompressed_size() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let pie_path = project_dir.join("../privacy_prove/test_data/privacy_tx_cairo_pie.zip");
        let pie = CairoPie::read_zip_file(&pie_path).unwrap();
        let precomputes = prepare_recursive_prover_precomputes().unwrap();
        let proof_output = privacy_recursive_prove(pie, precomputes).unwrap();

        let proof_bytes = zstd::decode_all(proof_output.proof.as_slice()).unwrap();
        assert_eq!(
            proof_bytes.len(),
            RECURSIVE_PROOF_UNCOMPRESSED_BYTES,
            "Update RECURSIVE_PROOF_UNCOMPRESSED_BYTES in consts.rs to {}",
            proof_bytes.len()
        );
    }
}
