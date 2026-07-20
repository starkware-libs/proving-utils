#[test]
fn test_privacy_bootloader_program_hash_snapshot() {
    use cairo_program_runner_lib::compute_program_hash_chain;
    use cairo_program_runner_lib::types::HashFunc;
    use expect_test::expect;
    use privacy_circuit_verify::get_privacy_bootloader_program;

    let bootloader_program = get_privacy_bootloader_program().unwrap();
    let stripped_program = bootloader_program.get_stripped_program().unwrap();
    let program_hash = compute_program_hash_chain(&stripped_program, 0, HashFunc::Blake)
        .expect("Failed to compute program hash.");

    // Source code for this compiled privacy bootloader can be found at:
    // repo: https://github.com/starkware-industries/starkware
    // branch: "dev"
    // commit: "7e08556cbf0bf75dc9651d297c3246be5871eeae"
    // Built (with debug info) via the standard BUILD target, then stripped of debug info to keep
    // the checked-in file small, from the starkware repo root:
    //   bazel build //src/starkware/cairo/bootloaders/simple_bootloader:privacy_simple_bootloader_program
    //   jq --indent 4 '.debug_info = null' \
    //     "$(bazel info bazel-bin)/src/starkware/cairo/bootloaders/simple_bootloader/privacy_simple_bootloader_compiled.json" \
    //     > privacy_simple_bootloader_compiled.json
    // (--indent 4 with no --sort-keys reproduces the compiler's json.dump(indent=4,
    //  sort_keys=True) output byte-for-byte, as the build output already has that key order.)
    let expected_hash_str =
        expect!["73747894710436589082477846004984361876990600795917652715762276452157777094"];
    expected_hash_str.assert_eq(&program_hash.to_string());
}

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
