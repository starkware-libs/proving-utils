#[cfg(feature = "slow-tests")]
pub mod slow_tests {
    use std::path::PathBuf;

    use privacy_circuit_verify::verify;
    use tracing_subscriber::fmt;

    use crate::privacy_prove;

    #[test]
    fn test_privacy_prove_and_verify() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let program_path = project_dir.join("test_data/privacy_tx_cairo_pie.zip");

        // Prove and verify
        let (proof, output_preimage) = privacy_prove(program_path).unwrap();
        verify(&proof, &output_preimage).unwrap();
    }
}
