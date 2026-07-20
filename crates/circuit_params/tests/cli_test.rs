use std::process::Command;

/// Runs the `circuit-params` binary for a single trace log size and returns its stdout, asserting
/// success. With `registry`, passes `--registry` (JSON output); otherwise emits the human-readable
/// report.
fn run(registry: bool) -> String {
    let binary = env!("CARGO_BIN_EXE_circuit-params");
    let mut args = vec!["--min_trace_log_size", "25", "--max_trace_log_size", "25"];
    if registry {
        args.push("--registry");
    }
    let output = Command::new(binary).args(&args).output().expect("Cannot run circuit-params");

    assert!(
        output.status.success(),
        "binary exited with status {}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout).expect("stdout is not valid UTF-8")
}

#[test]
fn run_circuit_params_binary_info() {
    let stdout = run(false);
    assert!(
        stdout.contains("leaf:\n25: eq:(log:")
            && stdout.contains("multiverifier:\neq:(log:")
            && stdout.contains("blake_g_gate:(log:"),
        "unexpected output: {stdout}"
    );
}

// Slow: builds and Merkle-commits a ~2^24 preprocessed trace. Gated behind the `slow-tests`
// feature (run with `cargo test --features slow-tests`) so it runs under the coverage job but not
// the fast test job.
#[test]
#[cfg(feature = "slow-tests")]
fn run_circuit_params_binary_json() {
    let stdout = run(true);
    assert!(
        stdout.contains("\"circuit_configs\":")
            && stdout.contains("\"leaf_verifiers\":")
            && stdout.contains("\"multiverifiers\":")
            && stdout.contains("\"input_configs\":")
            && stdout.contains("\"trace_log_size\": 25")
            && stdout.contains("\"log_blowup_factor\":")
            && stdout.contains("\"preprocessed_root\":")
            && stdout.contains("\"0x"),
        "unexpected output: {stdout}"
    );
}
