//! Computes per-component sizes for the CANONICAL preprocessed trace config, across a range of
//! verified trace sizes, and writes them as text (`info`) or JSON (`json`).
//!
//! - `info` reports two circuits per run: the leaf-prover verifier circuit (which verifies one
//!   Cairo proof), reported for every trace size, and the multiverifier circuit (which verifies two
//!   proofs of that leaf verifier circuit), reported once for the largest trace size. Each line
//!   gives every component's padded log size and usage.
//! - `json` computes shared target component sizes (the elementwise max of the leaf and
//!   multiverifier circuits at the largest trace size), then computes the preprocessed root of the
//!   leaf circuit for each trace size and of the multiverifier circuit once (for the largest trace
//!   size), all padded to those targets.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;

use cairo_air::verifier::INTERACTION_POW_BITS;
use circuit_cairo_verifier::all_components::all_components;
use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_cairo_verifier::statement::MEMORY_VALUES_LIMBS;
use circuit_cairo_verifier::verify::{CairoVerifierConfig, build_cairo_verifier_circuit};
use circuit_common::N_RESERVED;
use circuit_common::finalize::{ComponentSizes, compute_padded_sizes, pad_to_targets};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_verifier::statement::{
    INTERACTION_POW_BITS as CIRCUIT_INTERACTION_POW_BITS, all_circuit_components,
    circuit_component_log_sizes,
};
use circuits::blake::HashValue;
use circuits::context::FinalizedContext;
use circuits::ivalue::NoValue;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use clap::{Parser, ValueEnum};
use indexmap::IndexMap;
use leaf_prover::consts::DISABLED_COMPONENTS_CANONICAL_PREPROCESSED;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTraceVariant;
use stwo_cairo_common::prover_types::cpu::M31;
use stwo_cairo_prover::stwo::core::pcs::PcsConfig;
use stwo_cairo_prover::stwo::core::poly::circle::CanonicCoset;
use stwo_cairo_prover::stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo_cairo_prover::stwo::prover::CommitmentTreeProver;
use stwo_cairo_prover::stwo::prover::backend::simd::SimdBackend;
use stwo_cairo_prover::stwo::prover::mempool::BaseColumnPool;
use stwo_cairo_prover::stwo::prover::poly::circle::PolyOps;
use stwo_cairo_prover::witness::prelude::QM31;
use stwo_cairo_utils::binary_utils::run_binary;

#[cfg(test)]
mod tests;

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
    /// Output format.
    #[clap(long, value_enum, default_value = "info")]
    format: Format,
}

#[derive(Clone, ValueEnum)]
enum Format {
    /// Human-readable: per component, the padded log size and usage percentage.
    Info,
    /// JSON: a circuit-config registry, the leaf verifiers (one per trace size) and the
    /// multiverifier, each with its preprocessed root. All circuits are padded to the shared target
    /// component sizes (the max of the leaf and multiverifier circuits at the largest trace size).
    Json,
}

/// The padded log sizes of the verifier circuit's AIR components.
#[derive(Serialize, Deserialize)]
struct LogSizes {
    eq: u32,
    qm31_ops: u32,
    m31_to_u32: u32,
    triple_xor: u32,
    blake_g_gate: u32,
}

impl From<&ComponentSizes> for LogSizes {
    fn from(padded: &ComponentSizes) -> Self {
        LogSizes {
            eq: log_size(padded.eq),
            qm31_ops: log_size(padded.qm31_ops),
            m31_to_u32: log_size(padded.m31_to_u32),
            triple_xor: log_size(padded.triple_xor),
            blake_g_gate: log_size(padded.blake_g_gate),
        }
    }
}

/// A preprocessed-trace Merkle root: eight little-endian u32 words, serialized as an array of
/// `0x`-prefixed hex strings.
struct RootHex([u32; 8]);

impl Serialize for RootHex {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0
            .map(|word| format!("{word:#010x}"))
            .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for RootHex {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let words: [String; 8] = Deserialize::deserialize(deserializer)?;
        let mut root = [0u32; 8];
        for (out, word) in root.iter_mut().zip(words) {
            let hex = word.strip_prefix("0x").unwrap_or(&word);
            *out = u32::from_str_radix(hex, 16).map_err(serde::de::Error::custom)?;
        }
        Ok(RootHex(root))
    }
}

/// A circuit configuration: the (circuit-prover) log blowup factor and padded component log sizes a
/// circuit is proven with. Circuits sharing a config produce proofs a common AIR can verify.
#[derive(Serialize, Deserialize)]
struct CircuitConfig {
    log_blowup_factor: u32,
    component_log_sizes: LogSizes,
}

/// A leaf verifier circuit (verifying one Cairo proof of the given trace size and log blowup
/// factor), padded to its config's component sizes.
#[derive(Serialize, Deserialize)]
struct LeafVerifier {
    /// Key into `JsonOutput::circuit_configs`.
    config: String,
    trace_log_size: u32,
    /// Log blowup factor of the Cairo proof this leaf verifies.
    log_blowup_factor: u32,
    preprocessed_root: RootHex,
}

/// The multiverifier circuit, padded to its config's component sizes.
#[derive(Serialize, Deserialize)]
struct Multiverifier {
    /// Key into `JsonOutput::circuit_configs`: the multiverifier's own config.
    config: String,
    /// Configs of the two circuits whose proofs the multiverifier verifies.
    input_configs: [String; 2],
    preprocessed_root: RootHex,
}

/// The json output: a registry of circuit configs, the leaf verifiers (one per trace size), and the
/// multiverifiers. All circuits are padded to the shared target sizes and proven with the same
/// blowup, so they share a single config; the multiverifier verifies proofs of the leaf circuit and
/// is essentially the same across trace sizes, so a single multiverifier is reported.
#[derive(Serialize, Deserialize)]
struct JsonOutput {
    circuit_configs: BTreeMap<String, CircuitConfig>,
    leaf_verifiers: Vec<LeafVerifier>,
    multiverifiers: Vec<Multiverifier>,
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

/// The raw (non-padded) row counts of a circuit's AIR components, mirroring `compute_padded_sizes`
/// before its power-of-two rounding.
fn raw_sizes(context: &FinalizedContext<NoValue>) -> RawSizes {
    let circuit = context.circuit();
    let qm31_ops = circuit.add.len()
        + circuit.sub.len()
        + circuit.mul.len()
        + circuit.pointwise_mul.len()
        + circuit
            .permutation
            .iter()
            .map(|p| p.inputs.len() + p.outputs.len())
            .sum::<usize>();
    RawSizes {
        eq: circuit.eq.len(),
        qm31_ops,
        m31_to_u32: circuit.m31_to_u32.len(),
        triple_xor: circuit.triple_xor.len(),
        blake_g_gate: circuit.blake_g_gate.len(),
    }
}

/// Non-padded row counts and padded sizes of a circuit context's AIR components.
fn component_sizes(context: &FinalizedContext<NoValue>) -> (RawSizes, ComponentSizes) {
    (raw_sizes(context), compute_padded_sizes(context))
}

/// The elementwise maximum of two components' padded sizes.
fn max_component_sizes(a: &ComponentSizes, b: &ComponentSizes) -> ComponentSizes {
    ComponentSizes {
        eq: a.eq.max(b.eq),
        qm31_ops: a.qm31_ops.max(b.qm31_ops),
        m31_to_u32: a.m31_to_u32.max(b.m31_to_u32),
        triple_xor: a.triple_xor.max(b.triple_xor),
        blake_g_gate: a.blake_g_gate.max(b.blake_g_gate),
    }
}

/// One line with each component's padded log size and usage (fraction of the padded power-of-two
/// that the non-padded rows fill).
fn format_sizes(
    label: &str,
    trace_log_size: u32,
    raw: &RawSizes,
    padded: &ComponentSizes,
) -> String {
    let component = |name: &str, raw_size: usize, padded_size: usize| {
        format!(
            "{name}:(log: {}, usage = {:.0}%)",
            log_size(padded_size),
            usage_percent(raw_size),
        )
    };
    format!(
        "{label}{trace_log_size}: {} {} {} {} {}",
        component("eq", raw.eq, padded.eq),
        component("qm31_ops", raw.qm31_ops, padded.qm31_ops),
        component("m31_to_u32", raw.m31_to_u32, padded.m31_to_u32),
        component("triple_xor", raw.triple_xor, padded.triple_xor),
        component("blake_g_gate", raw.blake_g_gate, padded.blake_g_gate),
    )
}

/// Builds the leaf-prover verifier circuit topology (with the CANONICAL preprocessed trace and its
/// component set) for a verified Cairo proof whose trace has the given log size. The result is a
/// `NoValue` context (topology only; no witness values).
fn build_leaf_verifier_context(
    trace_log_size: u32,
    log_blowup_factor: u32,
) -> FinalizedContext<NoValue> {
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

    build_cairo_verifier_circuit(&verifier_config)
}

/// Builds the multiverifier circuit topology that verifies two proofs of `preprocessed_leaf`.
///
/// Mirrors `circuit_multiverifier`'s test-only `get_preprocessed_multiverifier_from_circuit`:
/// the multiverifier is fed two empty (zero-valued) proofs of the leaf circuit, which is enough to
/// build the `NoValue` topology and measure its component sizes. No target padding is applied so
/// the reported sizes are the raw ones. `pcs_config` must be the leaf proof's config; its
/// `min_lifting_log_size` must equal `preprocessed_leaf.trace_log_size + log_blowup_factor`.
fn build_multiverifier_context(
    preprocessed_leaf: &PreprocessedCircuit,
    pcs_config: PcsConfig,
) -> FinalizedContext<NoValue> {
    let preprocessed_column_log_sizes = preprocessed_leaf.preprocessed_trace.log_sizes();

    // `ProofConfig` expects the components in ascending log-size order.
    let mut components = all_circuit_components::<NoValue>();
    let log_sizes = circuit_component_log_sizes(&components, &preprocessed_column_log_sizes);
    components.sort_by(|a, _, b, _| log_sizes[*a].cmp(&log_sizes[*b]));

    let proof_config = ProofConfig::new(
        &components,
        preprocessed_leaf.preprocessed_trace.n_columns(),
        &pcs_config,
        CIRCUIT_INTERACTION_POW_BITS,
    );
    let shared_config = SharedConfig {
        pcs_config,
        preprocessed_column_log_sizes,
        proof_config: proof_config.clone(),
    };
    let empty_input = || MultiverifierInput {
        proof: empty_proof(&proof_config),
        preprocessed_root: HashValue::from([0u32; 8]),
        output_values: [0u32; N_RESERVED],
    };
    build_multiverifier_circuit::<NoValue>(empty_input(), empty_input(), &shared_config)
}

/// Builds the leaf verifier circuit for the given verified trace log size and returns its
/// component sizes.
fn leaf_component_sizes(trace_log_size: u32, log_blowup_factor: u32) -> (RawSizes, ComponentSizes) {
    let context = build_leaf_verifier_context(trace_log_size, log_blowup_factor);
    component_sizes(&context)
}

/// Builds the multiverifier circuit that verifies two proofs of the leaf verifier circuit for the
/// given verified trace log size.
fn build_multiverifier_context_for_trace(
    trace_log_size: u32,
    log_blowup_factor: u32,
) -> FinalizedContext<NoValue> {
    let mut leaf_context = build_leaf_verifier_context(trace_log_size, log_blowup_factor);

    // The multiverifier verifies proofs of the (preprocessed) leaf circuit, proven at the leaf
    // circuit's own trace log size.
    let preprocessed_leaf = PreprocessedCircuit::preprocess_circuit(&mut leaf_context);
    let multiverifier_pcs_config =
        get_pcs_config(preprocessed_leaf.trace_log_size, log_blowup_factor);
    build_multiverifier_context(&preprocessed_leaf, multiverifier_pcs_config)
}

/// The multiverifier circuit's component sizes for the given verified trace log size.
fn multiverifier_component_sizes(
    trace_log_size: u32,
    log_blowup_factor: u32,
) -> (RawSizes, ComponentSizes) {
    component_sizes(&build_multiverifier_context_for_trace(
        trace_log_size,
        log_blowup_factor,
    ))
}

/// Computes the Merkle root of a circuit's preprocessed trace, as eight little-endian Blake2s
/// words.
fn preprocessed_root(
    preprocessed_circuit: &PreprocessedCircuit,
    circuit_log_blowup_factor: u32,
) -> [u32; 8] {
    let min_lifting_log_size = preprocessed_circuit.trace_log_size + circuit_log_blowup_factor;
    let preprocessed_trace = preprocessed_circuit
        .preprocessed_trace
        .get_trace::<SimdBackend>();
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(min_lifting_log_size)
            .circle_domain()
            .half_coset,
    );
    let preprocessed_trace_polys = SimdBackend::interpolate_columns(preprocessed_trace, &twiddles);
    let preprocessed_tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        preprocessed_trace_polys,
        circuit_log_blowup_factor,
        &twiddles,
        true,
        min_lifting_log_size,
        &BaseColumnPool::<SimdBackend>::new(),
    );
    let root_hash = preprocessed_tree.commitment.root();
    std::array::from_fn(|i| u32::from_le_bytes(root_hash.0[i * 4..i * 4 + 4].try_into().unwrap()))
}

/// Pads `context` to the shared `target_sizes`, preprocesses it, and returns its preprocessed root.
fn padded_preprocessed_root(
    mut context: FinalizedContext<NoValue>,
    target_sizes: &ComponentSizes,
    circuit_log_blowup_factor: u32,
) -> [u32; 8] {
    pad_to_targets(&mut context, target_sizes.clone());
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut context);
    preprocessed_root(&preprocessed_circuit, circuit_log_blowup_factor)
}

fn main() -> ExitCode {
    run_binary(run, "circuit_params")
}

fn run() -> Result<(), String> {
    let args = Args::parse();

    let output = match args.format {
        Format::Info => {
            // The leaf verifier circuit's size grows with the verified trace size, so it's reported
            // for every trace log size in the range, under a `leaf:` header. The multiverifier
            // verifies proofs of the leaf circuit; we only report it for the largest leaf
            // (`max_trace_log_size`), which bounds the multiverifier size across the range.
            let leaf_lines: Vec<String> = (args.min_trace_log_size..=args.max_trace_log_size)
                .map(|trace_log_size| {
                    let (raw, padded) =
                        leaf_component_sizes(trace_log_size, args.log_blowup_factor);
                    format_sizes("", trace_log_size, &raw, &padded)
                })
                .collect();
            let leaf_section = format!("leaf:\n{}", leaf_lines.join("\n"));

            // We report a single multiverifier line, as the multiverifier is about the same for
            // all trace log sizes.
            let (mv_raw, mv_padded) =
                multiverifier_component_sizes(args.max_trace_log_size, args.log_blowup_factor);
            let multiverifier_line = format_sizes(
                "multiverifier:\n",
                args.max_trace_log_size,
                &mv_raw,
                &mv_padded,
            );

            format!("{leaf_section}\n\n{multiverifier_line}")
        }
        Format::Json => {
            // Currently a single log blowup factor is used across the system.
            let circuit_log_blowup_factor = args.log_blowup_factor;

            // Target sizes: the elementwise max of the leaf (cairo verifier) and multiverifier
            // component sizes at the largest trace size. Padding both circuits to this shared
            // target lets a single multiverifier AIR verify executions of the cairo
            // verifier and of itself (see `circuit_multiverifier`'s
            // `test_padding_is_correct`).
            let leaf_sizes = compute_padded_sizes(&build_leaf_verifier_context(
                args.max_trace_log_size,
                args.log_blowup_factor,
            ));
            let (_mv_raw, multiverifier_sizes) =
                multiverifier_component_sizes(args.max_trace_log_size, args.log_blowup_factor);
            let target_sizes = max_component_sizes(&leaf_sizes, &multiverifier_sizes);

            // All circuits are padded to `target_sizes` and proven with
            // `circuit_log_blowup_factor`, so they share a single config.
            const CONFIG_ID: &str = "default";
            let circuit_configs = BTreeMap::from([(
                CONFIG_ID.to_string(),
                CircuitConfig {
                    log_blowup_factor: circuit_log_blowup_factor,
                    component_log_sizes: (&target_sizes).into(),
                },
            )]);

            let leaf_verifiers = (args.min_trace_log_size..=args.max_trace_log_size)
                .map(|trace_log_size| {
                    let context =
                        build_leaf_verifier_context(trace_log_size, args.log_blowup_factor);
                    LeafVerifier {
                        config: CONFIG_ID.to_string(),
                        trace_log_size,
                        log_blowup_factor: args.log_blowup_factor,
                        preprocessed_root: RootHex(padded_preprocessed_root(
                            context,
                            &target_sizes,
                            circuit_log_blowup_factor,
                        )),
                    }
                })
                .collect::<Vec<_>>();

            // The multiverifier is essentially the same across trace sizes, so a single instance
            // (for the largest trace size) is reported. It verifies two proofs of the leaf circuit,
            // hence `input_configs = [CONFIG_ID, CONFIG_ID]`.
            let multiverifiers = vec![Multiverifier {
                config: CONFIG_ID.to_string(),
                input_configs: [CONFIG_ID.to_string(), CONFIG_ID.to_string()],
                preprocessed_root: RootHex(padded_preprocessed_root(
                    build_multiverifier_context_for_trace(
                        args.max_trace_log_size,
                        args.log_blowup_factor,
                    ),
                    &target_sizes,
                    circuit_log_blowup_factor,
                )),
            }];

            let json = JsonOutput {
                circuit_configs,
                leaf_verifiers,
                multiverifiers,
            };
            serde_json::to_string_pretty(&json).map_err(|err| err.to_string())?
        }
    };

    match args.output_path {
        Some(path) => std::fs::write(&path, format!("{output}\n"))
            .map_err(|err| format!("Cannot write output to {}: {err}", path.display()))?,
        None => println!("{output}"),
    }
    Ok(())
}
