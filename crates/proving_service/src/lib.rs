use cairo_air::utils::ProofFormat;
use circuit_cairo_air::statement::MEMORY_VALUES_LIMBS;
use circuit_cairo_air::verify::{
    prepare_cairo_proof_for_circuit_verifier, verify_fixed_cairo_circuit, CairoVerifierConfig,
};
use circuit_prover::finalize::finalize_context;
use circuit_prover::prover::{SimdBackend, prove_circuit_with_precompute};
use circuit_prover::witness::preprocessed::PreprocessedCircuit;
use circuit_air::statement::all_circuit_components;
use circuit_prover::prover::preprare_circuit_proof_for_circuit_verifier;
use circuits_stark_verifier::proof::ProofConfig;
use itertools::Itertools;
use stwo::core::pcs::PcsConfig;
use stwo::core::utils::MaybeOwned;
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::CommitmentTreeProver;
use stwo_cairo_prover::prover::{ProverParameters, prove_cairo_precompute};
use std::array;
use std::{fs::read_to_string, path::PathBuf};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
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
    pub twiddles: TwiddleTree<SimdBackend>,
    pub cairo_preprocessed_tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>,
    pub circuit_preprocessed_tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>
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
        let proof_params: ProverParameters = if let Some(proof_params_json) = proof_params_json {
            let s = read_to_string(&proof_params_json)
                .map_err(|e| StwoRunAndProveError::PathIO(e, proof_params_json.clone()))?;
            serde_json::from_str(&s)
                .map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?
        } else {
            panic!("Proof parameters JSON file is required");
        };

        let span = span!(Level::INFO, "proving cairo").entered();
        let cairo_proof = prove_cairo_precompute::<Blake2sM31MerkleChannel>(&self.base_column_pool, &self.twiddles, MaybeOwned::Borrowed(&self.cairo_preprocessed_tree), prover_input, proof_params,)
            .map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?;
        span.exit();

        let (proof, public_data) = prepare_cairo_proof_for_circuit_verifier(&cairo_proof, &self.privacy_verifier_config.proof_config);

        let (public_claim, outputs, _program) = public_data.pack_into_u32s();
        let outputs: Vec<[M31; 28]> = outputs
            .chunks_exact(MEMORY_VALUES_LIMBS)
            .map(|chunk| array::from_fn(|i| M31::from_u32_unchecked(chunk[i])))
            .collect_vec();
       

        let span = span!(Level::INFO, "building verification context").entered();
       
        let mut context = verify_fixed_cairo_circuit(&self.privacy_verifier_config, proof, public_claim, outputs, false).unwrap();
        span.exit();


        finalize_context(&mut context);
        let context_values = context.values();
    
        let span = span!(Level::INFO, "proving verification circuit").entered();

        let mut pcs_config = PcsConfig::default();
        let lifting_log_size = self.preprocessed_circuit.params.trace_log_size + pcs_config.fri_config.log_blowup_factor;
        pcs_config.lifting_log_size = Some(lifting_log_size);
        
        let circuit_proof = prove_circuit_with_precompute(&self.preprocessed_circuit, MaybeOwned::Borrowed(&self.circuit_preprocessed_tree), &self.base_column_pool, &self.twiddles, pcs_config, context_values);
        span.exit();

        let preprocessed_column_ids = self.preprocessed_circuit.preprocessed_trace.ids();
        let proof_config = ProofConfig::from_components(
            &all_circuit_components::<QM31>(),
            preprocessed_column_ids.len(),
            &circuit_proof.pcs_config,
            circuit_air::statement::INTERACTION_POW_BITS,
        );
        let (_proof, _public_data) = preprare_circuit_proof_for_circuit_verifier(circuit_proof, proof_config);
    
        // Sleep for 1 second to create a seperation between the proving and clean up.
        std::thread::sleep(std::time::Duration::from_secs(1));
       

        // TODO: Serialize the proof to a file.

        Ok(())
    }
}

