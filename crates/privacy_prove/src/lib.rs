pub mod consts;
#[cfg(test)]
mod tests;

use std::cmp::max;
use std::error::Error;
use std::fs::read_to_string;
use std::rc::Rc;
use std::sync::Arc;

use anyhow::Result;
use cairo_program_runner_lib::types::HashFunc;
use cairo_program_runner_lib::types::{PrivacySimpleBootloaderInput, SimpleBootloaderInput};
use cairo_program_runner_lib::{ProgramInput, Task, TaskSpec, cairo_run_program};
use cairo_vm::vm::runners::cairo_pie::CairoPie;
use circuit_air::verify::CircuitConfig;
use circuit_cairo_air::verify::CairoVerifierConfig;
use circuit_cairo_air::verify::build_fixed_cairo_circuit;
use circuit_cairo_air::verify::prepare_cairo_proof_for_circuit_verifier;
use circuit_common::finalize::{add_zk_blinding, finalize_context};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_prover::prover::{
    preprare_circuit_proof_for_circuit_verifier, prove_circuit_with_precompute,
};
use circuit_serialize::serialize::CircuitSerialize;
use circuits_stark_verifier::proof::ProofConfig;
use itertools::chain;
use privacy_circuit_verify::consts::{CAIRO_PCS_CONFIG, CIRCUIT_FRI_CONFIG, CIRCUIT_PCS_CONFIG};
use privacy_circuit_verify::{
    PrivacyProofOutput, compute_privacy_bootloader_output, get_cairo_proof_config,
    get_cairo_verifier_config, get_preprocessed_cairo_circuit, get_privacy_bootloader_program,
    get_proof_config, get_recursive_circuit_config,
};
use serde_json::from_str;
use starknet_types_core::felt::Felt;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTrace;
use stwo_cairo_prover::prover::{prove_cairo, prove_cairo_with_precompute};
use stwo_cairo_prover::witness::preprocessed_trace::gen_trace;
use tempfile::NamedTempFile;
use tracing::{Level, info, span};

use crate::consts::{
    CAIRO_PROVER_PARAMS, CAIRO_RUN_CONFIG, CIRCUIT_STORE_POLYNOMIALS_COEFFICIENTS,
};

pub struct RecursiveProverPrecomputes {
    pub base_column_pool: BaseColumnPool<SimdBackend>,
    pub twiddles: TwiddleTree<SimdBackend>,
    pub cairo_preprocessed_trace: Arc<PreProcessedTrace>,
    pub cairo_preprocessed_tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>,
    pub cairo_verifier_config: CairoVerifierConfig,
    pub circuit_preprocessed_tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>,
    pub preprocessed_circuit: PreprocessedCircuit,
    pub circuit_config: CircuitConfig,
    pub proof_config: ProofConfig,
}

/// Runs the program and generates a proof for it with params, bootloader and output format suitable
/// for the privacy circuit verifier.
pub fn privacy_prove(pie: CairoPie) -> Result<PrivacyProofOutput, Box<dyn Error>> {
    let _span = span!(Level::INFO, "privacy_prove").entered();

    info!("Run privacy bootloader and get the prover input and output preimage");
    let (prover_input, output_preimage) = run_privacy_bootloader(pie)?;

    info!("Generate the cairo proof");
    let cairo_proof = prove_cairo::<Blake2sM31MerkleChannel>(prover_input, CAIRO_PROVER_PARAMS)?;

    info!("Prepare the proof for the circuit verifier");
    let proof_config = get_cairo_proof_config();
    let (proof, public_data) =
        prepare_cairo_proof_for_circuit_verifier(&cairo_proof, &proof_config);

    info!("Serialize the proof and public data");
    let (public_claim, _outputs, _program) = public_data.pack_into_u32s();
    let mut proof_u32s = vec![];
    proof.serialize(&mut proof_u32s);

    Ok(PrivacyProofOutput {
        proof: chain!(public_claim, proof_u32s).collect(),
        output_preimage,
    })
}

pub fn prepare_recursive_prover_precomputes()
-> Result<Arc<RecursiveProverPrecomputes>, Box<dyn Error>> {
    let _span = span!(Level::INFO, "prepare_privacy_recursiveprover_precomputes").entered();

    let cairo_verifier_config = get_cairo_verifier_config()?;
    let preprocessed_circuit = get_preprocessed_cairo_circuit(&cairo_verifier_config);
    let circuit_config = get_recursive_circuit_config();
    let proof_config = get_proof_config();

    info!("Prepare the twiddles");
    let base_column_pool = BaseColumnPool::<SimdBackend>::new();
    let cairo_lifting_log_size = CAIRO_PROVER_PARAMS
        .pcs_config
        .lifting_log_size
        .ok_or("Lifting log size is not set in Cairo's PcsConfig")?;
    let circuit_lifting_log_size = CIRCUIT_PCS_CONFIG
        .lifting_log_size
        .ok_or("Lifting log size is not set in Circuit's PcsConfig")?;

    // Precompute twiddles.
    let max_domain_size = max(cairo_lifting_log_size, circuit_lifting_log_size);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_domain_size)
            .circle_domain()
            .half_coset,
    );

    info!("Prepare the cairo prover preprocessed trace and tree");
    let cairo_preprocessed_trace = Arc::new(
        CAIRO_PROVER_PARAMS
            .preprocessed_trace
            .to_preprocessed_trace(),
    );
    let cairo_preprocessed_trace_polys =
        SimdBackend::interpolate_columns(gen_trace(cairo_preprocessed_trace.clone()), &twiddles);
    let cairo_preprocessed_tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        cairo_preprocessed_trace_polys,
        CAIRO_PCS_CONFIG.fri_config.log_blowup_factor,
        &twiddles,
        CAIRO_PROVER_PARAMS.store_polynomials_coefficients,
        Some(cairo_lifting_log_size),
        &base_column_pool,
    );

    info!("Prepare the circuit prover preprocessed trace and tree");
    let circuit_preprocessed_trace = preprocessed_circuit
        .preprocessed_trace
        .get_trace::<SimdBackend>();
    let circuit_preprocessed_trace_polys =
        SimdBackend::interpolate_columns(circuit_preprocessed_trace, &twiddles);
    let circuit_preprocessed_tree =
        CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
            circuit_preprocessed_trace_polys,
            CIRCUIT_FRI_CONFIG.log_blowup_factor,
            &twiddles,
            CIRCUIT_STORE_POLYNOMIALS_COEFFICIENTS,
            circuit_config.config.lifting_log_size,
            &base_column_pool,
        );

    Ok(Arc::new(RecursiveProverPrecomputes {
        base_column_pool,
        twiddles,
        cairo_preprocessed_trace,
        cairo_preprocessed_tree,
        cairo_verifier_config,
        circuit_preprocessed_tree,
        preprocessed_circuit,
        circuit_config,
        proof_config,
    }))
}

pub fn privacy_recursive_prove(
    pie: CairoPie,
    precomputes: Arc<RecursiveProverPrecomputes>,
) -> Result<PrivacyProofOutput, Box<dyn Error>> {
    let _span = span!(Level::INFO, "privacy_recursive_prove").entered();

    info!("Run privacy bootloader and get the prover input and output preimage");
    let (prover_input, output_preimage) = run_privacy_bootloader(pie)?;

    info!("Generate the cairo proof");
    let cairo_proof = prove_cairo_with_precompute(
        &precomputes.base_column_pool,
        &precomputes.twiddles,
        precomputes.cairo_preprocessed_trace.clone(),
        MaybeOwned::Borrowed(&precomputes.cairo_preprocessed_tree),
        prover_input,
        CAIRO_PROVER_PARAMS,
    )?;

    info!("Prepare the cairo proof for the cairo-circuit verifier");
    let (proof, public_data) = prepare_cairo_proof_for_circuit_verifier(
        &cairo_proof,
        &precomputes.cairo_verifier_config.proof_config,
    );

    info!("Build the cairo-circuit verifier context");
    let (public_claim, _outputs, _program) = public_data.pack_into_u32s();
    let outputs = compute_privacy_bootloader_output(&output_preimage);
    let mut context = build_fixed_cairo_circuit(
        &precomputes.cairo_verifier_config,
        proof,
        public_claim,
        vec![outputs],
    );
    if !context.is_circuit_valid() {
        return Err("Circuit is not valid".into());
    };
    let zk_blinding_seed = cairo_proof.extended_stark_proof.proof.commitments.0[1].0;
    add_zk_blinding(
        &mut context,
        zk_blinding_seed,
        precomputes.circuit_config.config.fri_config.n_queries,
    );
    finalize_context(&mut context);
    let context_values = context.values();

    info!("Prove the cairo-circuit verifier");
    let circuit_proof = prove_circuit_with_precompute(
        &precomputes.base_column_pool,
        &precomputes.twiddles,
        &precomputes.preprocessed_circuit,
        MaybeOwned::Borrowed(&precomputes.circuit_preprocessed_tree),
        context_values,
        precomputes.circuit_config.config,
    );

    info!("Prepare the circuit proof for the circuit verifier");
    let (proof_qm31s, _public_data) =
        preprare_circuit_proof_for_circuit_verifier(circuit_proof, &precomputes.proof_config);

    info!("Serializing the proof");
    let mut proof = vec![];
    proof_qm31s.serialize(&mut proof);

    Ok(PrivacyProofOutput {
        proof,
        output_preimage,
    })
}

fn run_privacy_bootloader(pie: CairoPie) -> Result<(ProverInput, Vec<Felt>), Box<dyn Error>> {
    let _span = span!(Level::INFO, "get_prover_input").entered();

    let output_preimage_file = NamedTempFile::new()?;
    let output_preimage_path = output_preimage_file.path().to_path_buf();
    let pie_task_spec = TaskSpec {
        task: Rc::new(Task::Pie(pie)),
        program_hash_function: HashFunc::Blake,
    };
    let bootloader_input = PrivacySimpleBootloaderInput {
        simple_bootloader_input: SimpleBootloaderInput {
            fact_topologies_path: None,
            single_page: true,
            tasks: vec![pie_task_spec],
        },
        output_preimage_dump_path: output_preimage_path.clone(),
    };
    let bootloader_program = get_privacy_bootloader_program()?;

    info!("Running the program");
    let runner = cairo_run_program(
        &bootloader_program,
        Some(ProgramInput::Value(Box::new(bootloader_input))),
        CAIRO_RUN_CONFIG,
        None,
    )?;

    info!("Reading the bootloader output preimage");
    let output_preimage_content = read_to_string(&output_preimage_path)?;
    let output_preimage: Vec<Felt> = from_str(&output_preimage_content)?;

    info!("Adapting the runner output for the prover");
    let prover_input = adapt(&runner)?;

    Ok((prover_input, output_preimage))
}
