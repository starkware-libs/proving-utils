//! Slow integration test: run the full chain end-to-end and execute the new Cairo
//! circuit verifier on the produced args file via `scarb execute`. Gated by the
//! `slow-tests` feature because proving + executing takes minutes.

#![cfg(feature = "slow-tests")]

use std::path::PathBuf;
use std::process::Command;

use cairo_vm::vm::runners::cairo_pie::CairoPie;
use circuit_verifier_e2e::recurse::{
    dump_cairo_verifier_args, prove_recursive_verification, write_arguments_file,
};
use privacy_prove::{prepare_recursive_prover_precomputes, privacy_recursive_prove};

const PIE_PATH: &str = "../privacy_prove/test_data/privacy_tx_cairo_pie.zip";

fn stwo_cairo_verifier_dir() -> PathBuf {
    // <repo-root>/proving-utils/crates/circuit_verifier_e2e → <workspace>/stwo-cairo/...
    // The integration test is invoked with CARGO_MANIFEST_DIR set to the e2e crate.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .join("../../../stwo-cairo/stwo_cairo_verifier")
        .canonicalize()
        .expect("stwo-cairo/stwo_cairo_verifier must exist as a sibling repo")
}

#[test]
fn end_to_end_privacy_to_cairo_circuit_verifier() {
    let _ = tracing_subscriber::fmt::try_init();

    // ---- Steps 1-7 ----
    let pie = CairoPie::read_zip_file(&PathBuf::from(PIE_PATH)).expect("read PIE fixture");
    let precomputes =
        prepare_recursive_prover_precomputes().expect("prepare_recursive_prover_precomputes");
    let privacy_proof_output =
        privacy_recursive_prove(pie, precomputes).expect("privacy_recursive_prove");
    let recursive =
        prove_recursive_verification(&privacy_proof_output).expect("prove_recursive_verification");

    // ---- Step 8: write args file ----
    let tmp = tempfile::tempdir().expect("tempdir");
    let args_file = tmp.path().join("circuit_verifier_args.json");
    let felts = dump_cairo_verifier_args(recursive).expect("dump_cairo_verifier_args");
    write_arguments_file(&felts, &args_file).expect("write args file");

    println!("wrote {} felts to {}", felts.len(), args_file.display());

    // ---- Step 8b: invoke `scarb execute` on the new Cairo circuit verifier ----
    let verifier_dir = stwo_cairo_verifier_dir();
    let status = Command::new("scarb")
        .arg("--profile")
        .arg("proving")
        .arg("execute")
        .arg("--package")
        .arg("stwo_circuit_verifier")
        .arg("--features")
        .arg("qm31_opcode")
        .arg("--print-resource-usage")
        .arg("--output")
        .arg("none")
        .arg("--arguments-file")
        .arg(&args_file)
        .current_dir(&verifier_dir)
        .status()
        .expect("invoke scarb");

    assert!(
        status.success(),
        "scarb execute failed (exit {:?}). args: {}, dir: {}",
        status.code(),
        args_file.display(),
        verifier_dir.display()
    );
}
