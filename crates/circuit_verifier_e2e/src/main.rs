//! `dump_circuit_verifier_args` — drives the privacy chain end-to-end and writes the
//! felt252 stream the new Cairo circuit verifier consumes via
//! `scarb execute --arguments-file`.
//!
//! Usage:
//!   dump_circuit_verifier_args --pie <PIE.zip> --out <args.json> [--consts-out <consts.txt>]
//!
//! The PIE is the output of running a Cairo program through the privacy bootloader
//! workflow (see `proving-utils/crates/cairo-program-runner`). For an existing fixture,
//! pass it directly.

use std::path::PathBuf;

use anyhow::{Context, Result};
use cairo_vm::vm::runners::cairo_pie::CairoPie;
use circuit_verifier_e2e::recurse::{
    dump_cairo_verifier_args, prove_recursive_verification, render_privacy_consts,
    write_arguments_file,
};
use clap::Parser;
use privacy_prove::{prepare_recursive_prover_precomputes, privacy_recursive_prove};
use tracing::info;
use tracing_subscriber::EnvFilter;

#[derive(Parser, Debug)]
#[command(about = "Dump Cairo circuit-verifier args from a PIE", long_about = None)]
struct Args {
    /// Path to the Cairo PIE produced by running a program through the privacy
    /// bootloader workflow.
    #[arg(long)]
    pie: PathBuf,

    /// Output path for the args JSON file (consumed by `scarb execute --arguments-file`).
    #[arg(long)]
    out: PathBuf,

    /// Optional output path for the structural constants the Cairo verifier hardcodes
    /// in `privacy_consts.cairo` (preprocessed root, column log sizes, ...).
    #[arg(long)]
    consts_out: Option<PathBuf>,
}

fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env().add_directive(tracing::Level::INFO.into()))
        .init();

    let args = Args::parse();

    info!("Load CairoPie from {}", args.pie.display());
    let pie = CairoPie::read_zip_file(&args.pie)
        .with_context(|| format!("reading PIE at {}", args.pie.display()))?;

    info!("Prepare recursive prover precomputes");
    let precomputes = prepare_recursive_prover_precomputes()
        .map_err(|e| anyhow::anyhow!("prepare_recursive_prover_precomputes: {e}"))?;

    info!("Steps 1-5: prove cairo, verify-in-circuit, prove circuit_proof_1");
    let privacy_proof_output = privacy_recursive_prove(pie, precomputes.clone())
        .map_err(|e| anyhow::anyhow!("privacy_recursive_prove: {e}"))?;

    info!("Steps 6-7: verify circuit_proof_1 IN circuit, prove circuit_proof_2");
    let recursive = prove_recursive_verification(&privacy_proof_output)
        .map_err(|e| anyhow::anyhow!("prove_recursive_verification: {e}"))?;
    info!(
        "circuit_proof_2 ready: n_outputs={}, lifting_log_size={}, {} preprocessed cols",
        recursive.n_outputs,
        recursive.lifting_log_size,
        recursive.preprocessed_column_log_sizes.len()
    );

    let consts = render_privacy_consts(&recursive);
    if let Some(consts_out) = &args.consts_out {
        std::fs::write(consts_out, &consts)
            .with_context(|| format!("writing {}", consts_out.display()))?;
        info!("Wrote privacy consts to {}", consts_out.display());
    } else {
        info!("privacy_consts.cairo values:\n{consts}");
    }

    info!("Step 8: serialize for the Cairo circuit verifier and write args file");
    let felts = dump_cairo_verifier_args(recursive)
        .map_err(|e| anyhow::anyhow!("dump_cairo_verifier_args: {e}"))?;

    write_arguments_file(&felts, &args.out)
        .with_context(|| format!("writing {}", args.out.display()))?;

    info!("Wrote {} felts to {}", felts.len(), args.out.display());
    eprintln!(
        "\nNext: re-run only the verifier with\n  \
         (cd /home/gali/workspace/stwo-cairo/stwo_cairo_verifier && \\\n   \
          scarb --profile proving execute --package stwo_circuit_verifier \\\n     \
            --features qm31_opcode --print-resource-usage --output none \\\n     \
            --arguments-file {})",
        args.out.display()
    );
    Ok(())
}
