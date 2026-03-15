#[cfg(feature = "slow-tests")]
pub mod slow_tests {
    use std::path::PathBuf;

    use cairo_vm::vm::runners::cairo_pie::CairoPie;
    use privacy_circuit_verify::{verify_cairo, verify_recursive_circuit};
    use tracing_subscriber::fmt;

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
}
