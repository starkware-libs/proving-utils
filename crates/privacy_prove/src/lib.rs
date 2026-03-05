pub mod consts;
#[cfg(test)]
mod tests;

use std::error::Error;
use std::fs::read_to_string;
use std::rc::Rc;

use anyhow::Result;
use cairo_program_runner_lib::types::HashFunc;
use cairo_program_runner_lib::types::{PrivacySimpleBootloaderInput, SimpleBootloaderInput};
use cairo_program_runner_lib::{ProgramInput, Task, TaskSpec, cairo_run_program};
use cairo_vm::vm::runners::cairo_pie::CairoPie;
use circuit_cairo_air::verify::prepare_cairo_proof_for_circuit_verifier;
use circuit_serialize::serialize::CircuitSerialize;
use itertools::chain;
use privacy_circuit_verify::{
    PrivacyProofOutput, get_privacy_bootloader_program, get_proof_config,
};
use serde_json::from_str;
use starknet_types_core::felt::Felt;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_prover::prover::prove_cairo;
use tempfile::NamedTempFile;
use tracing::{Level, info, span};

use crate::consts::{CAIRO_RUN_CONFIG, PROVER_PARAMS};

/// Runs the program and generates a proof for it with params, bootloader and output format suitable
/// for the privacy circuit verifier.
pub fn privacy_prove(pie: CairoPie) -> Result<PrivacyProofOutput, Box<dyn Error>> {
    let _span = span!(Level::INFO, "privacy_prove").entered();

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

    info!("Generating the cairo proof");
    let cairo_proof = prove_cairo::<Blake2sM31MerkleChannel>(prover_input, PROVER_PARAMS)?;

    info!("Preparing the proof for the circuit verifier");
    let proof_config = get_proof_config();
    let (proof, public_data) =
        prepare_cairo_proof_for_circuit_verifier(&cairo_proof, &proof_config);

    info!("Serializing the proof and public data");
    let (public_claim, _outputs, _program) = public_data.pack_into_u32s();
    let mut proof_u32s = vec![];
    proof.serialize(&mut proof_u32s);

    Ok(PrivacyProofOutput {
        proof: chain!(public_claim, proof_u32s).collect(),
        output_preimage,
    })
}
