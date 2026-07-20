//! Computes the leaf-prover verifier circuit's per-component sizes for the CANONICAL preprocessed
//! trace config, across a range of verified trace sizes, and writes them as text.

use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;

use cairo_air::verifier::INTERACTION_POW_BITS;
use circuit_cairo_verifier::all_components::all_components;
use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_cairo_verifier::statement::MEMORY_VALUES_LIMBS;
use circuit_cairo_verifier::verify::{CairoVerifierConfig, build_cairo_verifier_circuit};
use circuit_common::finalize::{ComponentSizes, compute_padded_sizes};
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::proof::ProofConfig;
use clap::Parser;
use indexmap::IndexMap;
use leaf_prover::consts::DISABLED_COMPONENTS_CANONICAL_PREPROCESSED;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTraceVariant;
use stwo_cairo_common::prover_types::cpu::M31;
use stwo_cairo_prover::witness::prelude::QM31;
use stwo_cairo_utils::binary_utils::run_binary;

#[derive(Parser)]
struct Args {
    /// Path to write the output to. If omitted, prints to stdout.
    #[clap(long)]
    output_path: Option<PathBuf>,
    /// Smallest verified trace log size to measure (inclusive). A canonical Cairo trace commits
    /// its preprocessed sequence columns at `MAX_SEQUENCE_LOG_SIZE = 25`, so a real canonical
    /// leaf proof has `log_trace_size >= 25`.
    #[clap(long)]
    min_trace_log_size: u32,
    /// Largest verified trace log size to measure (inclusive).
    #[clap(long)]
    max_trace_log_size: u32,
    /// Log blowup factor of the verified Cairo proof (1, 2, or 3), passed to `get_pcs_config`.
    #[clap(long = "log_blowup_factor", default_value_t = 1)]
    log_blowup_factor: u32,
}

fn log_size(size: usize) -> u32 {
    size.next_power_of_two().ilog2()
}

/// The fraction (as a percentage) of the padded (power-of-two) component that is actually used.
fn usage_percent(size: usize) -> f64 {
    100.0 * size as f64 / size.next_power_of_two() as f64
}

/// The raw (non-padded) row count of each AIR component.
struct RawSizes {
    eq: usize,
    qm31_ops: usize,
    m31_to_u32: usize,
    triple_xor: usize,
    blake_g_gate: usize,
}

/// One line with each component's padded log size and usage (fraction of the padded power-of-two
/// that the non-padded rows fill).
fn format_sizes(raw: &RawSizes, padded: &ComponentSizes) -> String {
    let component = |name: &str, raw_size: usize, padded_size: usize| {
        format!("{name}:(log: {}, usage = {:.0}%)", log_size(padded_size), usage_percent(raw_size),)
    };
    format!(
        "{} {} {} {} {}",
        component("eq", raw.eq, padded.eq),
        component("qm31_ops", raw.qm31_ops, padded.qm31_ops),
        component("m31_to_u32", raw.m31_to_u32, padded.m31_to_u32),
        component("triple_xor", raw.triple_xor, padded.triple_xor),
        component("blake_g_gate", raw.blake_g_gate, padded.blake_g_gate),
    )
}

/// Builds the leaf-prover verifier circuit topology (with the CANONICAL preprocessed trace and its
/// component set) for a verified Cairo proof whose trace has the given log size, and returns the
/// non-padded row counts and padded sizes of its AIR components.
fn leaf_verifier_component_sizes(
    trace_log_size: u32,
    log_blowup_factor: u32,
) -> (RawSizes, ComponentSizes) {
    let preprocessed_trace_variant = PreProcessedTraceVariant::Canonical;

    // The Cairo-proof PCS config the leaf prover uses (canonical preprocessed).
    let pcs_config = get_pcs_config(trace_log_size, log_blowup_factor);

    // Enabled bits and component set for the canonical preprocessed leaf config, mirroring
    // `prove_leaf`.
    let mut cairo_components: IndexMap<&'static str, Box<dyn CircuitEval<QM31>>> =
        IndexMap::default();
    let mut enabled_bits = vec![];
    for (name, component) in all_components::<QM31>() {
        if DISABLED_COMPONENTS_CANONICAL_PREPROCESSED.contains(&name) {
            enabled_bits.push(false);
        } else {
            cairo_components.insert(name, component);
            enabled_bits.push(true);
        }
    }

    let proof_config = ProofConfig::new(
        &cairo_components,
        preprocessed_trace_variant.n_columns(),
        &pcs_config,
        INTERACTION_POW_BITS,
    );

    // Program length and output count are held fixed for this measurement; only the trace size
    // varies. The preprocessed root value is irrelevant for the [NoValue] topology.
    let program: Arc<[[M31; MEMORY_VALUES_LIMBS]]> =
        std::iter::repeat_n([M31::from(0u32); MEMORY_VALUES_LIMBS], 128).collect();

    let verifier_config = CairoVerifierConfig {
        proof_config,
        enabled_bits,
        program,
        n_outputs: 1,
        preprocessed_root: [0u32; 8].into(),
        preprocessed_trace_variant,
    };

    let context = build_cairo_verifier_circuit(&verifier_config);
    let padded = compute_padded_sizes(&context);

    // Non-padded row counts, mirroring `compute_padded_sizes` before its power-of-two rounding.
    let circuit = context.circuit();
    let qm31_ops = circuit.add.len()
        + circuit.sub.len()
        + circuit.mul.len()
        + circuit.pointwise_mul.len()
        + circuit.permutation.iter().map(|p| p.inputs.len() + p.outputs.len()).sum::<usize>();
    let raw = RawSizes {
        eq: circuit.eq.len(),
        qm31_ops,
        m31_to_u32: circuit.m31_to_u32.len(),
        triple_xor: circuit.triple_xor.len(),
        blake_g_gate: circuit.blake_g_gate.len(),
    };

    (raw, padded)
}

fn main() -> ExitCode {
    run_binary(run, "circuit_params")
}

fn run() -> Result<(), String> {
    let args = Args::parse();

    let output = (args.min_trace_log_size..=args.max_trace_log_size)
        .map(|trace_log_size| {
            let (raw, padded) =
                leaf_verifier_component_sizes(trace_log_size, args.log_blowup_factor);
            format!("{}: {}", trace_log_size, format_sizes(&raw, &padded))
        })
        .collect::<Vec<_>>()
        .join("\n");

    match args.output_path {
        Some(path) => std::fs::write(&path, format!("{output}\n"))
            .map_err(|err| format!("Cannot write output to {}: {err}", path.display()))?,
        None => println!("{output}"),
    }
    Ok(())
}
