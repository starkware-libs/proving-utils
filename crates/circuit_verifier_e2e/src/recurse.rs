//! Steps 6–8 of the e2e flow.
//!
//! Steps 1–5 (compile → run_and_adapt → cairo_prove → cairo-verifier-in-circuit →
//! circuit-prove) are done by `privacy_prove::privacy_recursive_prove`, which produces a
//! `PrivacyProofOutput` containing a (version-prefixed, compressed) circuit_proof_1.
//!
//! This module:
//! - Step 6: builds the recursive verification context via
//!   `circuit_verifier::verify::build_verification_circuit`.
//! - Step 7: preprocesses + proves it via `circuit_prover::prove_circuit_assignment_with_channel`,
//!   giving `circuit_proof_2`.
//! - Step 8: serializes `circuit_proof_2` into the felt252 stream the Cairo circuit verifier (in
//!   `stwo-cairo`) consumes. The verifier-config constants (preprocessed root, column log sizes,
//!   lifting log size, n_outputs) are NOT part of the stream — they are hardcoded in the Cairo
//!   binary (`privacy_consts.cairo`); this module surfaces them in [`RecursiveProveOutput`] so they
//!   can be (re)generated.

use std::error::Error;

use circuit_cairo_serialize::prepare_circuit_proof_for_cairo_verifier;
use circuit_common::finalize::add_zk_blinding;
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_prover::prover::{
    BaseColumnPool, CircuitProof as ProverCircuitProof, SimdBackend,
    prove_circuit_assignment_with_channel,
};
use circuit_serialize::deserialize::deserialize_proof_with_config;
use circuit_verifier::components::prelude::OrderedHashMap;
use circuit_verifier::statement::{all_circuit_components, circuit_component_log_sizes};
use circuit_verifier::verify::{CircuitPublicData, build_verification_circuit};
use circuits::ivalue::{IValue, NoValue};
use itertools::Itertools;
use privacy_circuit_verify::consts::{
    CIRCUIT_FRI_CONFIG, CIRCUIT_PCS_CONFIG, MAX_RECURSIVE_PROOF_UNCOMPRESSED_BYTES,
};
use privacy_circuit_verify::{
    PrivacyProofOutput, compute_privacy_bootloader_output, decompress_proof, get_proof_config,
    get_recursive_circuit_config, split_proof_version,
};
use starknet_ff::FieldElement;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs::blake2_hash::Blake2sHash;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};

/// Output of the recursive prove step: the prover's `CircuitProof` (`circuit_proof_2`)
/// PLUS the structural info about the OUTER circuit (the recursive verification circuit)
/// that the Cairo verifier hardcodes in its `privacy_consts.cairo`.
pub struct RecursiveProveOutput {
    /// Outer (`circuit_proof_2`) prover output. Uses the non-M31 `Blake2sMerkleHasher`
    /// because the Cairo circuit verifier's channel does not M31-reduce digests.
    pub prover_output: ProverCircuitProof<Blake2sMerkleHasher>,
    /// Per-component log sizes of the outer circuit, keyed by component name (in
    /// `all_circuit_components` order). Needed by the serializer to sort queried values the
    /// way the Cairo verifier reads them.
    pub component_log_sizes: OrderedHashMap<&'static str, u32>,
    /// Per-column (id, log size) of the outer circuit's preprocessed trace, in canonical
    /// (size-sorted) prover order — the order the Cairo verifier's
    /// `preprocessed_columns.cairo` indices assume.
    pub preprocessed_column_log_sizes: Vec<(String, u32)>,
    /// Preprocessed trace root (Merkle commitment, tree 0 of `stark_proof.commitments`).
    pub preprocessed_root: Blake2sHash,
    /// `trace_log_size + log_blowup_factor` — must equal the proof's
    /// `pcs_config.lifting_log_size` and the Cairo config's `lifting_log_size`.
    pub lifting_log_size: u32,
    /// Number of `Output` gates of the outer circuit.
    pub n_outputs: u32,
}

pub fn prove_recursive_verification(
    proof_output: &PrivacyProofOutput,
) -> Result<RecursiveProveOutput, Box<dyn Error>> {
    let proof_config = get_proof_config();

    // ---- Step 6a: deserialize circuit_proof_1 ----
    let (_version, compressed_proof) = split_proof_version(&proof_output.proof)?;
    let proof_bytes = decompress_proof(compressed_proof, MAX_RECURSIVE_PROOF_UNCOMPRESSED_BYTES)?;
    let mut slice: &[u8] = &proof_bytes;
    let proof_q = deserialize_proof_with_config(&mut slice, &proof_config)?;
    if !slice.is_empty() {
        return Err(format!(
            "circuit_proof_1 deserialization left {} trailing bytes (decompressed={}, used={})",
            slice.len(),
            proof_bytes.len(),
            proof_bytes.len() - slice.len()
        )
        .into());
    }

    // ---- Step 6b: assemble the public data the recursive verifier expects ----
    // Must mirror `privacy_circuit_verify::verify_recursive_circuit`: the output hash
    // (2 QM31s). The logup anchor `u` is appended internally by the verifier.
    let outputs = compute_privacy_bootloader_output(&proof_output.output_preimage);
    let output_qm31s =
        circuits_stark_verifier::proof_from_stark_proof::pack_into_qm31s(outputs.into_iter());
    let output_hash = QM31::blake(output_qm31s.as_slice(), output_qm31s.len() * 16);
    let output_values = vec![output_hash.0, output_hash.1];
    let public_data = CircuitPublicData { output_values };

    // ---- Step 6c: build the recursive verification context (witness) ----
    let mut context =
        build_verification_circuit::<QM31>(get_recursive_circuit_config(), proof_q, public_data)
            .map_err(|e| -> Box<dyn Error> { e.into() })?;

    if !context.is_circuit_valid() {
        return Err(
            "recursive verification context is invalid (the inner proof did not verify)".into(),
        );
    }

    // Use a deterministic seed for the test driver. In production a random seed should be used.
    let zk_blinding_seed = [0u8; 32];
    add_zk_blinding(&mut context, zk_blinding_seed, CIRCUIT_FRI_CONFIG.n_queries);

    // ---- Step 7: preprocess (pads the context in place) and prove the witness ----
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);

    let prover_output = prove_circuit_assignment_with_channel::<Blake2sMerkleChannel>(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
        CIRCUIT_PCS_CONFIG,
    )
    .map_err(|e| -> Box<dyn Error> { format!("prove_circuit_assignment: {e:?}").into() })?;

    // ---- Step 7b: extract the structural info the Cairo verifier hardcodes ----
    let preprocessed_log_sizes_map = preprocessed.preprocessed_trace.log_sizes();
    let components = all_circuit_components::<NoValue>();
    let component_log_sizes = circuit_component_log_sizes(&components, &preprocessed_log_sizes_map);
    let preprocessed_column_log_sizes: Vec<(String, u32)> = preprocessed_log_sizes_map
        .iter()
        .map(|(id, &log_size)| (id.id.clone(), log_size))
        .collect();

    // Preprocessed root = the first commitment in the StarkProof.
    let preprocessed_root: Blake2sHash = prover_output.stark_proof.proof.0.commitments.0[0];

    // The Cairo verifier asserts its hardcoded `lifting_log_size` equals the one in the
    // proof's `pcs_config`, so report the proof's value (not `trace_log_size + blowup`,
    // which can be smaller when the configured lifting over-lifts).
    let lifting_log_size = prover_output
        .pcs_config
        .lifting_log_size
        .ok_or("circuit proofs must carry an explicit lifting_log_size")?;
    let n_outputs = u32::try_from(preprocessed.n_outputs).expect("n_outputs must fit in u32");

    Ok(RecursiveProveOutput {
        prover_output,
        component_log_sizes,
        preprocessed_column_log_sizes,
        preprocessed_root,
        lifting_log_size,
        n_outputs,
    })
}

/// Step 8: serialize `circuit_proof_2` for the Cairo circuit verifier. Consumes the
/// prover output (the serializer takes ownership of the proof).
pub fn dump_cairo_verifier_args(
    recursive: RecursiveProveOutput,
) -> Result<Vec<FieldElement>, Box<dyn Error>> {
    let felts = prepare_circuit_proof_for_cairo_verifier(
        recursive.prover_output,
        &recursive.component_log_sizes,
    );
    Ok(felts)
}

/// Renders the body of `stwo-cairo`'s `privacy_consts.cairo` constants from a real
/// recursive prove run, so the Cairo verifier's hardcoded config can be regenerated.
pub fn render_privacy_consts(recursive: &RecursiveProveOutput) -> String {
    let root_words = recursive
        .preprocessed_root
        .0
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()).to_string())
        .join(", ");
    let log_sizes = recursive
        .preprocessed_column_log_sizes
        .iter()
        .map(|(id, log_size)| format!("    {log_size}, // {id}"))
        .join("\n");
    format!(
        "// Generated by proving-utils' `dump_circuit_verifier_args` (circuit_verifier_e2e).\n\
         LIFTING_LOG_SIZE: u32 = {};\n\
         N_OUTPUTS: u32 = {};\n\
         preprocessed_root (LE u32 words): [{}]\n\
         preprocessed_column_log_sizes ({} columns):\narray![\n{}\n]\n",
        recursive.lifting_log_size,
        recursive.n_outputs,
        root_words,
        recursive.preprocessed_column_log_sizes.len(),
        log_sizes,
    )
}

/// Helper: write a `Vec<FieldElement>` to a JSON arguments file in the format
/// `scarb execute --arguments-file` accepts (a JSON array of `0x`-prefixed hex strings).
pub fn write_arguments_file(felts: &[FieldElement], path: &std::path::Path) -> std::io::Result<()> {
    let strings: Vec<String> = felts.iter().map(|f| format!("0x{f:x}")).collect();
    let json = serde_json::to_string(&strings).expect("FieldElement strings should serialize");
    std::fs::write(path, json)
}
