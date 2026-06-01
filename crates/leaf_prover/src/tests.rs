#[cfg(feature = "slow-tests")]
pub mod slow_tests {
    use std::fs::{self, read_to_string};
    use std::path::PathBuf;

    use cairo_program_runner_lib::utils::get_program;
    use tracing_subscriber::fmt::format::FmtSpan;

    use crate::{
        consts::{CIRCUIT_PCS_CONFIG, CIRCUIT_TRACE_LOG_SIZE},
        prove_leaf,
    };
    #[test]
    fn test_prove_leaf_small_program_canonical_small() {
        // Enable logging for the leaf prover and stwo
        let subscriber = tracing_subscriber::fmt()
            .with_ansi(false)
            .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
            .finish();
        tracing::subscriber::set_global_default(subscriber)
            .expect("Setting tracing default failed");

        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let program =
            get_program(&project_dir.join("test_data/use_all_opcodes_and_builtins_compiled.json"))
                .unwrap();
        let prover_parameters = sonic_rs::from_str(
            &read_to_string(project_dir.join("test_data/prover_params_canonical_small.json"))
                .unwrap(),
        )
        .unwrap();

        // Use a blowup factor of 1 to reduce memory consumption of this test
        let mut pcs_config = CIRCUIT_PCS_CONFIG;
        pcs_config.fri_config.log_blowup_factor = 1;
        pcs_config.lifting_log_size =
            Some(CIRCUIT_TRACE_LOG_SIZE + pcs_config.fri_config.log_blowup_factor);

        let output = prove_leaf(&program, None, prover_parameters, pcs_config);

        let expected_output_path = project_dir.join("test_data/expected_output.json");

        if std::env::var("FIX").is_ok() {
            fs::write(
                &expected_output_path,
                serde_json::to_string_pretty(&output).unwrap(),
            )
            .unwrap_or_else(|err| {
                panic!("Error writing to {}: {err}", expected_output_path.display())
            });
        } else {
            let expected_output = fs::read_to_string(&expected_output_path).unwrap_or_else(|err| {
                panic!("Cannot read {}: {err}", expected_output_path.display())
            });
            let expected_output = serde_json::from_str(&expected_output).unwrap();
            assert!(
                output == expected_output,
                "Leaf prover output != expected. Run with FIX=1 to fix expected output."
            );
        }
    }
}
