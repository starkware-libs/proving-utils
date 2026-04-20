#[cfg(feature = "slow-tests")]
pub mod slow_tests {
    use std::path::PathBuf;

    use cairo_air::air::PublicData;
    use cairo_vm::vm::runners::cairo_pie::CairoPie;
    use circuit_cairo_air::verify::build_fixed_cairo_circuit;
    use circuit_common::finalize::{add_zk_blinding, finalize_context};
    use circuit_prover::prover::{SimdBackend, prove_circuit_with_precompute};
    use circuit_serialize::deserialize::deserialize_proof_with_config;
    use privacy_circuit_verify::{verify_cairo, verify_recursive_circuit};
    use stwo::{core::utils::MaybeOwned, prover::poly::circle::PolyOps};
    use stwo_cairo_prover::witness::prelude::CanonicCoset;
    use tracing_subscriber::EnvFilter;
    use tracing_subscriber::fmt;
    use tracing_subscriber::fmt::format::FmtSpan;

    use crate::{prepare_recursive_prover_precomputes, privacy_prove, privacy_recursive_prove};

    #[test]
    fn test_privacy_prove_and_verify() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let pie_path = project_dir.join("test_data/privacy_tx_cairo_pie.zip");
        let pie = CairoPie::read_zip_file(&pie_path).unwrap();

        // Prove and verify
        let proof_output = privacy_prove(pie).unwrap();
        verify_cairo(&proof_output).unwrap();
    }

    #[test]
    fn test_privacy_recursive_prove_and_verify() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let pie_path = project_dir.join("test_data/privacy_tx_cairo_pie.zip");
        let pie = CairoPie::read_zip_file(&pie_path).unwrap();

        let precomputes = prepare_recursive_prover_precomputes().unwrap();

        // Prove and verify
        let proof_output = privacy_recursive_prove(pie, precomputes).unwrap();
        verify_recursive_circuit(&proof_output).unwrap();
    }

    /// Run with:
    /// `RUST_LOG=stwo=info cargo test --release --features slow-tests test_prove_circuit_stir -- --nocapture`
    #[test]
    fn test_prove_circuit_stir() {
        const ADDITIONAL_BLOWUP: u32 = 3;
        let _ = fmt()
            .with_env_filter(EnvFilter::from_default_env())
            .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
            // .with_ansi(false) // Uncomment if you want to dump the logs to file.
            .try_init();

        let precomputes = prepare_recursive_prover_precomputes().unwrap();
        // Don't use the precomputed twiddles. Instead create new ones of the needed size.
        // Here 23 == CAIRO_PROVER_PARAMS.pcs_config.lifting_log_size ==
        // CIRCUIT_PROVER_PARAMS.lifting_log_size
        let large_twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(23 + ADDITIONAL_BLOWUP)
                .circle_domain()
                .half_coset,
        );

        // Read the test data.
        let test_data_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_data");
        let proof_bytes = std::fs::read(test_data_dir.join("proof.bin")).unwrap();
        let proof = deserialize_proof_with_config(
            &mut proof_bytes.as_slice(),
            &precomputes.cairo_verifier_config.proof_config,
        )
        .unwrap();
        let public_data_json =
            std::fs::read_to_string(test_data_dir.join("public_data.json")).unwrap();
        let public_data: PublicData = serde_json::from_str(&public_data_json).unwrap();
        let outputs_json = std::fs::read_to_string(test_data_dir.join("outputs.json")).unwrap();
        let outputs = serde_json::from_str(&outputs_json).unwrap();

        // Build the circuit.
        let (public_claim, _outputs, _program) = public_data.pack_into_u32s();
        let mut context = build_fixed_cairo_circuit(
            &precomputes.cairo_verifier_config,
            proof,
            public_claim,
            vec![outputs],
        );
        assert!(context.is_circuit_valid());

        // Hardcoded from the proof.
        let zk_blinding_seed = [
            91, 214, 217, 69, 114, 162, 16, 29, 202, 148, 192, 111, 115, 243, 51, 40, 5, 189, 154,
            83, 81, 64, 58, 31, 23, 164, 202, 25, 107, 12, 231, 31,
        ];
        add_zk_blinding(
            &mut context,
            zk_blinding_seed,
            precomputes.circuit_config.config.fri_config.n_queries,
        );
        finalize_context(&mut context);
        let context_values = context.values();

        // Prove the circuit.

        let start = std::time::Instant::now();
        let _circuit_proof = prove_circuit_with_precompute(
            &precomputes.base_column_pool,
            &large_twiddles,
            &precomputes.preprocessed_circuit,
            MaybeOwned::Borrowed(&precomputes.circuit_preprocessed_tree),
            context_values,
            precomputes.circuit_config.config,
        );
        let elapsed = start.elapsed();
        println!("prove_circuit_with_precompute took {:?}", elapsed);
    }
}
