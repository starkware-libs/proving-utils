use cairo_air::utils::ProofFormat;

use std::{fs::read_to_string, path::PathBuf};
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_prover::prover::prove_cairo;
use stwo_cairo_prover::stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;

use stwo_circuits::{cairo_air::verify::verify_cairo, circuit_prover::prover::prove_circuit};
pub use stwo_run_and_prove::{
    stwo_run_and_prove, ProveConfig, ProverTrait, RunConfig, StwoProverEntryPoint,
    StwoRunAndProveError,
};

pub struct ProvingServiceEntryPoint;

impl ProverTrait for ProvingServiceEntryPoint {
    fn create_and_serialize_proof(
        &self,
        prover_input: ProverInput,
        _verify: bool,
        _proof_path: PathBuf,
        _proof_format: ProofFormat,
        proof_params_json: Option<PathBuf>,
    ) -> Result<(), StwoRunAndProveError> {
        let proof_params = if let Some(proof_params_json) = proof_params_json {
            let s = read_to_string(&proof_params_json)
                .map_err(|e| StwoRunAndProveError::PathIO(e, proof_params_json.clone()))?;
            serde_json::from_str(&s)
                .map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?
        } else {
            panic!("Proof parameters JSON file is required");
        };

        let cairo_proof = prove_cairo::<Blake2sM31MerkleChannel>(prover_input, proof_params)
            .map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?;

        let mut context = verify_cairo(&cairo_proof);
        let _proof = prove_circuit(&mut context);

        // TODO: Serialize the proof to a file.

        Ok(())
    }
}
