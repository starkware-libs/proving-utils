pub mod consts;
#[cfg(test)]
mod tests;

use std::error::Error;
use std::fs::read_to_string;
use std::path::PathBuf;

use anyhow::Result;
use cairo_program_runner_lib::{ProgramInput, cairo_run_program};
use circuit_cairo_air::verify::prepare_cairo_proof_for_circuit_verifier;
use circuit_serialize::serialize::CircuitSerialize;
use itertools::chain;
use privacy_circuit_verify::{get_bootloader_program, get_proof_config};
use serde_json::from_str;
use starknet_types_core::felt::Felt;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_prover::prover::prove_cairo;
use tempfile::NamedTempFile;
use tracing::{Level, info, span};

use crate::consts::{CAIRO_RUN_CONFIG, PROVER_PARAMS};

/// Runs the program and generates a proof for it.
pub fn privacy_prove(program_path: PathBuf) -> Result<(Vec<u32>, Vec<Felt>), Box<dyn Error>> {
    let _span = span!(Level::INFO, "privacy_prove").entered();

    let output_preimage_file = NamedTempFile::new()?;
    let output_preimage_path = output_preimage_file.path().to_path_buf();
    let program_input_contents = format!(
        r#"{{
            "tasks": [
              {{
                "path": "{}",
                "program_hash_function": "blake",
                "type": "CairoPiePath"
              }}
            ],
            "single_page": true,
            "output_preimage_dump_path": "{}"
        }}"#,
        program_path.display(),
        output_preimage_path.display(),
    );
    let bootloader_program = get_bootloader_program()?;

    info!("Running the program");
    let runner = cairo_run_program(
        &bootloader_program,
        Some(ProgramInput::Json(program_input_contents)),
        CAIRO_RUN_CONFIG,
        None,
    )?;

    info!("Reading the bootloader output preimage");
    let output_preimage_content = read_to_string(&output_preimage_path)?;
    let output_preimage_felts: Vec<Felt> = from_str(&output_preimage_content)?;

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

    Ok((
        chain!(public_claim, proof_u32s).collect(),
        output_preimage_felts,
    ))
}
