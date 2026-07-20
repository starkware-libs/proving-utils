use std::sync::Arc;

use cairo_air::verifier::INTERACTION_POW_BITS;
use cairo_program_runner_lib::utils::get_cairo_run_config;
use cairo_program_runner_lib::{ProgramInput, cairo_run_program};
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use circuit_cairo_verifier::all_components::all_components;
use circuit_cairo_verifier::statement::MEMORY_VALUES_LIMBS;
use circuit_cairo_verifier::verify::{
    CairoVerifierConfig, build_and_fill_cairo_verifier_circuit,
    prepare_cairo_proof_for_circuit_verifier,
};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_prover::prover::{
    BaseColumnPool, prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
};
use circuit_serialize::serialize::CircuitSerialize;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::proof::ProofConfig;
use indexmap::IndexMap;
use itertools::Itertools;
use leaf_proof_format::SerializedLeafProof;
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTraceVariant;
use stwo_cairo_common::prover_types::cpu::M31;
use stwo_cairo_common::prover_types::felt::split_f252;
use stwo_cairo_prover::prover::{ProverParameters, prove_cairo};
use stwo_cairo_prover::stwo::core::pcs::PcsConfig;
use stwo_cairo_prover::stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo_cairo_prover::stwo::core::verifier::PREPROCESSED_TRACE_IDX;
use stwo_cairo_prover::witness::prelude::{Felt252, QM31};
use tracing::info;

use crate::consts::{
    DISABLED_COMPONENTS_CANONICAL_PREPROCESSED, DISABLED_COMPONENTS_SMALL_PREPROCESSED,
};

pub fn prove_leaf(
    program: &Program,
    program_input: Option<ProgramInput>,
    cairo_prover_parameters: ProverParameters,
    circuit_prover_pcs_config: PcsConfig,
) -> SerializedLeafProof {
    assert!(
        cairo_prover_parameters.include_all_preprocessed_columns,
        "The prover parameters must set include_all_preprocessed_columns=true because the \
         verifier circuit expects a constant number of preprocessed columns"
    );
    assert!(
        cairo_prover_parameters.raise_min_lifting_to_max_column,
        "The prover parameters must set raise_min_lifting_to_max_column=true because the \
         circuit-cairo-verifier only supports verifying proofs where the lifting size is >= the \
         preprocessed trace height"
    );

    // Execute & prove the input Cairo program.

    let cairo_run_config = get_cairo_run_config(
        // we don't use dynamic layout in stwo.
        &None,
        LayoutName::all_cairo_stwo,
        // proof_mode.
        true,
        // in stwo when proof_mode==true, trace padding is redundant work.
        true,
        // allow_missing_builtins - ignored when proof_mode == true.
        true,
        // we don't need to relocate memory in the VM because we later call the adapter that does
        // relocation.
        false,
    )
    .unwrap();
    let runner = cairo_run_program(program, program_input, cairo_run_config, None).unwrap();
    info!("Program execution done");

    let prover_input = adapt(&runner).unwrap();
    let output_addresses = prover_input.builtin_segments.output.unwrap();

    let program_output_u256s: Vec<[u32; 8]> = (output_addresses.begin_addr
        ..output_addresses.stop_ptr)
        .map(|addr| prover_input.memory.get(addr.try_into().unwrap()).as_u256())
        .collect();
    let n_outputs = program_output_u256s.len();
    info!("Adapter done. Program created {n_outputs} outputs.");

    let outputs_as_m31_slices =
        program_output_u256s.iter().map(|value| split_f252(*value)).collect_vec();
    let proof =
        prove_cairo::<Blake2sM31MerkleChannel>(prover_input, cairo_prover_parameters).unwrap();
    info!("Cairo proving done");

    let preprocessed_root = proof.extended_stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX];

    let disabled_components: &[&str] = match cairo_prover_parameters.preprocessed_trace {
        PreProcessedTraceVariant::Canonical => &DISABLED_COMPONENTS_CANONICAL_PREPROCESSED,
        PreProcessedTraceVariant::CanonicalSmall => &DISABLED_COMPONENTS_SMALL_PREPROCESSED,
        _ => panic!(
            "Unsupported preprocessed trace {:?}",
            cairo_prover_parameters.preprocessed_trace
        ),
    };
    let LeafVerifierComponents { components: cairo_components, enabled_bits } =
        leaf_verifier_components(disabled_components);

    // Set min_lifting_log_size from the cairo proof.
    let mut pcs_config = cairo_prover_parameters.pcs_config;
    pcs_config.min_lifting_log_size = proof.extended_stark_proof.proof.config.min_lifting_log_size;

    let proof_config = ProofConfig::new(
        &cairo_components,
        cairo_prover_parameters.preprocessed_trace.n_columns(),
        &pcs_config,
        INTERACTION_POW_BITS,
    );

    // Verify that the Cairo proof has the expected trace width (if not - this is an
    // indication that the program doesn't use all components).
    for (trace_idx, trace_name) in ["preprocessed", "base", "interaction"].iter().enumerate() {
        let expected_columns = proof_config.n_columns_per_trace()[trace_idx];
        let columns_in_proof = proof.extended_stark_proof.proof.queried_values[trace_idx].len();
        assert!(
            columns_in_proof == expected_columns,
            "Expected {expected_columns} columns in {trace_name} trace, but proof has \
             {columns_in_proof}"
        );
    }

    let (proof_for_circuit, serialized_aux_data) =
        prepare_cairo_proof_for_circuit_verifier(&proof, &enabled_bits);

    // Build the verifier circuit.

    let verifier_config = CairoVerifierConfig {
        program: Arc::from(program_felts(program)),
        enabled_bits,
        proof_config,
        n_outputs,
        preprocessed_trace_variant: cairo_prover_parameters.preprocessed_trace,
        preprocessed_root: preprocessed_root.into(),
    };

    let mut context = build_and_fill_cairo_verifier_circuit(
        &verifier_config,
        proof_for_circuit,
        serialized_aux_data,
        outputs_as_m31_slices,
    );

    // TODO: Pad to multiverifier size.

    info!(
        "Verifier config:
    program: ({} felts)
    n_outputs: {}
    Cairo preprocessed trace: {:?}
    Cairo preprocessed trace root: {:?}
    Proof pow bits: {}
    Proof FRI config: {:?}",
        verifier_config.program.len(),
        verifier_config.n_outputs,
        verifier_config.preprocessed_trace_variant,
        verifier_config.preprocessed_root,
        verifier_config.proof_config.n_pow_bits,
        verifier_config.proof_config.fri,
    );
    assert!(context.is_circuit_valid(), "The verifier circuit rejected the proof!");
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut context);

    // Prove the execution of the verifier circuit.

    let base_column_pool = BaseColumnPool::new();
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed_circuit,
        &base_column_pool,
        circuit_prover_pcs_config,
    )
    .unwrap();
    info!("Circuit proving done");
    let circuit_preprocessed_root =
        circuit_proof.stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX].0;
    info!("Circuit preprocessed root: {:?}", circuit_preprocessed_root);

    // Convert the proof to our output format.

    let (proof_qm31s, _public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let mut proof_bytes: Vec<u8> = vec![];
    proof_qm31s.serialize(&mut proof_bytes);

    SerializedLeafProof { circuit_preprocessed_root, proof: proof_bytes }
}

/// The components of the circuit that verifies the Cairo proof.
pub struct LeafVerifierComponents {
    /// Map from component name to the circuit evaluator that verifies it.
    pub components: IndexMap<&'static str, Box<dyn CircuitEval<QM31>>>,
    /// One bit per possible component: `true` if the component is enabled (present).
    pub enabled_bits: Vec<bool>,
}

/// Creates the component list and enabled bits for the circuit that verifies the Cairo proof.
/// The set of components is constant (all possible components for the given preprocessed trace,
/// minus `disabled_components`) to keep the verifier circuit stable. The trace is expected to
/// contain all the components in this set.
pub fn leaf_verifier_components(disabled_components: &[&str]) -> LeafVerifierComponents {
    let mut components: IndexMap<&'static str, Box<dyn CircuitEval<QM31>>> = IndexMap::default();
    let mut enabled_bits = vec![];
    for (name, component) in all_components::<QM31>() {
        if disabled_components.contains(&name) {
            enabled_bits.push(false);
        } else {
            components.insert(name, component);
            enabled_bits.push(true);
        }
    }
    LeafVerifierComponents { components, enabled_bits }
}

fn program_felts(program: &Program) -> Vec<[M31; MEMORY_VALUES_LIMBS]> {
    let mut program_felts = vec![];
    for value in program.iter_data() {
        let value = value.get_int().unwrap();
        program_felts.push(Felt252::from(value).get_limbs());
    }
    program_felts
}
