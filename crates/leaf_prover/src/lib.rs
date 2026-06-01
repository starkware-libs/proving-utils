pub mod consts;

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use cairo_air::verifier::INTERACTION_POW_BITS;
use cairo_program_runner_lib::utils::{get_cairo_run_config, write_output_to_file};
use cairo_program_runner_lib::{ProgramInput, cairo_run_program};
use cairo_vm::types::builtin_name::BuiltinName;
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
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTraceVariant;
use stwo_cairo_common::prover_types::cpu::M31;
use stwo_cairo_common::prover_types::felt::split_f252;
use stwo_cairo_prover::prover::{ProverParameters, prove_cairo};
use stwo_cairo_prover::stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo_cairo_prover::stwo::core::verifier::PREPROCESSED_TRACE_IDX;
use stwo_cairo_prover::witness::prelude::{Felt252, QM31};
use tracing::info;

use crate::consts::{CIRCUIT_PCS_CONFIG, DISABLED_COMPONENTS};

// The root of the commitment on the canonical preprocessed trace with a lifting
// size of 26 and log-blowup-factor of 1 using the Blake2sM31 hash.
const CANONICAL_PREPROCESSED_TRACE_ROOT: [u8; 32] = [
    0x5b, 0x49, 0x00, 0x29, 0x97, 0xff, 0xac, 0x06, 0xc6, 0x3a, 0x96, 0x16, 0xf7, 0x01, 0x68, 0x7e,
    0x8c, 0xc3, 0xeb, 0x55, 0x72, 0x6b, 0x0c, 0x08, 0xa4, 0x94, 0x31, 0x28, 0x26, 0xd5, 0x4c, 0x0a,
];

pub fn prove_leaf(
    program: &Program,
    program_input: Option<ProgramInput>,
    prover_parameters: ProverParameters,
    proof_path: PathBuf,
    output_path: Option<PathBuf>,
) {
    assert_eq!(
        prover_parameters.preprocessed_trace,
        PreProcessedTraceVariant::Canonical,
        "Must always use the same preprocesed trace variant to keep the verifier circuit stable"
    );
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
    let mut runner = cairo_run_program(&program, program_input, cairo_run_config, None).unwrap();

    let n_outputs = *runner
        .get_execution_resources()
        .unwrap()
        .builtin_instance_counter
        .get(&BuiltinName::output)
        .unwrap_or(&0);
    info!("Program execution done. Created {n_outputs} outputs.");
    if let Some(output_path) = output_path {
        info!("Writing outputs to {}", output_path.display());
        write_output_to_file(&mut runner, output_path).unwrap();
    }

    let prover_input = adapt(&runner).unwrap();
    let output_addresses = prover_input.builtin_segments.output.unwrap();
    let outputs_as_m31_slices = (output_addresses.begin_addr..output_addresses.stop_ptr)
        .map(|addr| split_f252(prover_input.memory.get(addr.try_into().unwrap()).as_u256()))
        .collect::<Vec<_>>();
    let proof = prove_cairo::<Blake2sM31MerkleChannel>(prover_input, prover_parameters).unwrap();
    info!("Cairo proving done");

    let preprocessed_root = proof.extended_stark_proof.proof.commitments[PREPROCESSED_TRACE_IDX];
    assert_eq!(
        preprocessed_root,
        CANONICAL_PREPROCESSED_TRACE_ROOT.as_slice().into()
    );

    let mut cairo_components: IndexMap<&'static str, Box<dyn CircuitEval<_>>> = IndexMap::default();
    let mut enabled_bits = vec![];
    for (name, component) in all_components::<QM31>() {
        if DISABLED_COMPONENTS.contains(&name) {
            enabled_bits.push(false);
        } else {
            cairo_components.insert(name, component);
            enabled_bits.push(true);
        }
    }

    let preprocessed_columns = prover_parameters
        .preprocessed_trace
        .to_preprocessed_trace()
        .columns;

    let proof_config = ProofConfig::new(
        &cairo_components,
        preprocessed_columns.len(),
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
        preprocessed_trace_variant: PreProcessedTraceVariant::Canonical,
        preprocessed_root: preprocessed_root.into(),
    };

    let mut context = build_fixed_cairo_circuit(
        &verifier_config,
        proof_for_circuit,
        serialized_aux_data,
        outputs_as_m31_slices,
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
        CIRCUIT_PCS_CONFIG,
    )
    .unwrap();
    info!("Circuit proving done");

    let (proof_qm31s, _public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let mut proof_bytes: Vec<u8> = vec![];
    proof_qm31s.serialize(&mut proof_bytes);

    fs::write(&proof_path, proof_bytes).unwrap_or_else(|err| {
        panic!(
            "Cannot write proof to {}. Error: {err}",
            proof_path.display()
        )
    })
}

fn program_felts(program: &Program) -> Vec<[M31; MEMORY_VALUES_LIMBS]> {
    let mut program_felts = vec![];
    for value in program.iter_data() {
        let value = value.get_int().unwrap();
        program_felts.push(Felt252::from(value).get_limbs());
    }
    program_felts
}
