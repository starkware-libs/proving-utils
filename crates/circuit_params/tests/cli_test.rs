use std::process::Command;

/// Runs the `circuit-params` binary for a single trace log size and checks it prints one info line.
#[test]
fn run_circuit_params_binary() {
    let binary = env!("CARGO_BIN_EXE_circuit-params");
    let output = Command::new(binary)
        .args(["--min-trace-log-size", "25", "--max-trace-log-size", "25"])
        .output()
        .expect("Cannot run circuit-params");

    assert!(
        output.status.success(),
        "binary exited with status {}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8(output.stdout).expect("stdout is not valid UTF-8");
    assert!(
        stdout.contains("leaf:\n25: eq:(log:")
            && stdout.contains("multiverifier:\neq:(log:")
            && stdout.contains("blake_g_gate:(log:"),
        "unexpected output: {stdout}"
    );
}
