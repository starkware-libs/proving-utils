use cairo_air::utils::ProofFormat;
use circuit_cairo_air::statement::MEMORY_VALUES_LIMBS;
use circuit_cairo_air::verify::{
    prepare_cairo_proof_for_circuit_verifier, verify_fixed_cairo_circuit, CairoVerifierConfig,
};
use circuit_prover::finalize::finalize_context;
use circuit_prover::prover::prove_circuit_assignment;
use circuit_prover::witness::preprocessed::PreprocessedCircuit;
use itertools::Itertools;
use stwo_cairo_prover::prover::prove_cairo;
use stwo_cairo_prover::witness::prelude::SimdBackend;
use std::array;
use std::{fs::read_to_string, path::PathBuf};
use stwo::core::fields::m31::M31;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_prover::stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use circuit_prover::prover::BaseColumnPool;

use tracing::{Level, span};

pub use stwo_run_and_prove::{
    ProveConfig, ProverTrait, RunConfig, StwoProverEntryPoint, StwoRunAndProveError,
    stwo_run_and_prove,
};


pub struct ProvingServiceEntryPoint {
    pub base_column_pool: BaseColumnPool<SimdBackend>,
    pub preprocessed_circuit: PreprocessedCircuit,
    pub privacy_verifier_config: CairoVerifierConfig,
}

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

        let span = span!(Level::INFO, "proving cairo").entered();
        let cairo_proof = prove_cairo::<Blake2sM31MerkleChannel>(prover_input, proof_params)
            .map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?;
        span.exit();

        let (proof, public_data) = prepare_cairo_proof_for_circuit_verifier(&cairo_proof, &self.privacy_verifier_config.proof_config);

        let (public_claim, outputs, _program) = public_data.pack_into_u32s();
        let outputs: Vec<[M31; 28]> = outputs
            .chunks_exact(MEMORY_VALUES_LIMBS)
            .map(|chunk| array::from_fn(|i| M31::from_u32_unchecked(chunk[i])))
            .collect_vec();
       

        let span = span!(Level::INFO, "building verification context").entered();
       
        let mut context = verify_fixed_cairo_circuit(&self.privacy_verifier_config, proof, public_claim, outputs).unwrap();
        span.exit();


        finalize_context(&mut context);
        let context_values = context.values();
    
        let span = span!(Level::INFO, "proving verification circuit").entered();

        
        let _proof = prove_circuit_assignment(context_values, &self.preprocessed_circuit, &self.base_column_pool);

    
        span.exit();

        // TODO: Serialize the proof to a file.

        Ok(())
    }
}
