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

    // Configuration for the circuit prover.
    // Use a blowup factor of 1 to minimize memory consumption of the test.
    pub const CIRCUIT_LOG_BLOWUP_FACTOR: u32 = 1;
    pub const CIRCUIT_TRACE_LOG_SIZE: u32 = 21;

    pub const CIRCUIT_PROVER_FRI_CONFIG: FriConfig = FriConfig {
        log_blowup_factor: CIRCUIT_LOG_BLOWUP_FACTOR,
        log_last_layer_degree_bound: 0,
        n_queries: 35,
        fold_step: 4,
    };

    pub const CIRCUIT_PROVER_PCS_CONFIG: PcsConfig = PcsConfig {
        pow_bits: 26,
        fri_config: CIRCUIT_PROVER_FRI_CONFIG,
        lifting_log_size: Some(CIRCUIT_TRACE_LOG_SIZE + CIRCUIT_LOG_BLOWUP_FACTOR),
    };

    #[test]
    fn test_prove_leaf_small_program_canonical_small() {
        // Enable logging for the leaf prover and stwo
        let subscriber = tracing_subscriber::fmt()
            .with_ansi(false)
            .with_span_events(FmtSpan::ENTER | FmtSpan::CLOSE)
            .with_test_writer()
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

        let output = prove_leaf(&program, None, prover_parameters, CIRCUIT_PROVER_PCS_CONFIG);

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
