pub mod consts;

#[cfg(test)]
pub mod tests;

use std::sync::Arc;

use cairo_air::verifier::INTERACTION_POW_BITS;
use cairo_program_runner_lib::utils::get_cairo_run_config;
use cairo_program_runner_lib::{ProgramInput, cairo_run_program};
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use circuit_cairo_verifier::all_components::all_components;
use circuit_cairo_verifier::statement::MEMORY_VALUES_LIMBS;
use circuit_cairo_verifier::verify::{
    CairoVerifierConfig, build_fixed_cairo_circuit, prepare_cairo_proof_for_circuit_verifier,
};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_prover::prover::{
    BaseColumnPool, prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
};
use circuit_serialize::serialize::CircuitSerialize;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::proof::ProofConfig;
use indexmap::IndexMap;
use leaf_proof_format::SerializedLeafProof;
use num_bigint::BigUint;
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

use crate::consts::{DISABLED_COMPONENTS, DISABLED_COMPONENTS_SMALL_PREPROCESSED};

pub fn prove_leaf(
    program: &Program,
    program_input: Option<ProgramInput>,
    prover_parameters: ProverParameters,
    circuit_pcs_config: PcsConfig,
) -> SerializedLeafProof {
    assert!(
        prover_parameters.include_all_preprocessed_columns,
        "The prover parameters must set include_all_preprocessed_columns=true because the verifier circuit expects a constant number of preprocessed columns"
    );

    let cairo_run_config = get_cairo_run_config(
        // we don't use dynamic layout in stwo
        &None,
        LayoutName::all_cairo_stwo,
        true,
        // in stwo when proof_mode==true, trace padding is redundant work
        true,
        // we allow missing builtins because all_cairo_stwo doesn't include all builtins, and
        // the bootloader will simulate the missing builtins.
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

    let outputs_as_m31_slices = program_output_u256s
        .iter()
        .map(|value| split_f252(*value))
        .collect::<Vec<_>>();
    let proof = prove_cairo::<Blake2sM31MerkleChannel>(prover_input, prover_parameters).unwrap();
    info!("Cairo proving done");

    let preprocessed_root = proof.extended_stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX];

    let mut cairo_components: IndexMap<&'static str, Box<dyn CircuitEval<_>>> = IndexMap::default();
    let mut enabled_bits = vec![];

    let disabled_components: &[&str] = match prover_parameters.preprocessed_trace {
        PreProcessedTraceVariant::Canonical => &DISABLED_COMPONENTS,
        PreProcessedTraceVariant::CanonicalSmall => &DISABLED_COMPONENTS_SMALL_PREPROCESSED,
        _ => panic!(
            "Unsupported preprocessed trace {:?}",
            prover_parameters.preprocessed_trace
        ),
    };
    for (name, component) in all_components::<QM31>() {
        if disabled_components.contains(&name) {
            enabled_bits.push(false);
        } else {
            cairo_components.insert(name, component);
            enabled_bits.push(true);
        }
    }

    let proof_config = ProofConfig::new(
        &cairo_components,
        prover_parameters.preprocessed_trace.n_columns(),
        &prover_parameters.pcs_config,
        INTERACTION_POW_BITS,
    );

    for (trace_idx, trace_name) in ["preprocessed", "base", "interaction"].iter().enumerate() {
        let expected_columns = proof_config.n_columns_per_trace()[trace_idx];
        let columns_in_proof = proof.extended_stark_proof.proof.queried_values[trace_idx].len();
        assert!(
            columns_in_proof == expected_columns,
            "Expected {expected_columns} columns in {trace_name} trace, but proof has {columns_in_proof}"
        );
    }
    let (proof_for_circuit, serialized_aux_data) =
        prepare_cairo_proof_for_circuit_verifier(&proof, &enabled_bits);

    let verifier_config = CairoVerifierConfig {
        program: Arc::from(program_felts(program)),
        enabled_bits,
        proof_config,
        n_outputs,
        preprocessed_trace_variant: prover_parameters.preprocessed_trace,
        preprocessed_root: preprocessed_root.into(),
    };

    let mut context = build_fixed_cairo_circuit(
        &verifier_config,
        proof_for_circuit,
        serialized_aux_data,
        outputs_as_m31_slices,
    );

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
    assert!(
        context.is_circuit_valid(),
        "The verifier circuit rejected the proof!"
    );
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut context);
    let base_column_pool = BaseColumnPool::new();
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed_circuit,
        &base_column_pool,
        circuit_pcs_config,
    )
    .unwrap();
    info!("Circuit proving done");
    let circuit_preprocessed_root =
        circuit_proof.stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX].0;
    info!("Circuit preprocessed root: {:?}", circuit_preprocessed_root);

    let (proof_qm31s, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
    let circuit_output = public_data
        .output_values
        .iter()
        .map(|qm31| qm31.to_m31_array().map(|m31| m31.0))
        .collect();

    let mut proof_bytes: Vec<u8> = vec![];
    proof_qm31s.serialize(&mut proof_bytes);

    let program_output = program_output_u256s
        .iter()
        .map(|u256| BigUint::from_slice(u256).to_string())
        .collect::<Vec<_>>();
    SerializedLeafProof {
        program_output,
        circuit_output,
        circuit_preprocessed_root,
        proof: proof_bytes,
    }
}

fn program_felts(program: &Program) -> Vec<[M31; MEMORY_VALUES_LIMBS]> {
    let mut program_felts = vec![];
    for value in program.iter_data() {
        let value = value.get_int().unwrap();
        program_felts.push(Felt252::from(value).get_limbs());
    }
    program_felts
}
