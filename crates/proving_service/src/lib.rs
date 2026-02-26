use cairo_air::flat_claims::FlatClaim;
use cairo_air::utils::ProofFormat;
use cairo_air::CairoProof;
use circuit_cairo_air::all_components::all_components;
use circuit_cairo_air::preprocessed_columns::PREPROCESSED_COLUMNS_ORDER;
use circuit_cairo_air::statement::MEMORY_VALUES_LIMBS;
use circuit_cairo_air::verify::{
    prepare_cairo_proof_for_circuit_verifier, verify_fixed_cairo_circuit, CairoVerifierConfig,
    INTERACTION_POW_BITS,
};
use circuit_prover::finalize::finalize_context;
use circuit_prover::prover::{preprocess_circuit, prove_circuit_assignment};
use circuits::context::Context;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::empty_component::EmptyComponent;
use circuits_stark_verifier::proof::ProofConfig;
use itertools::{zip_eq, Itertools};
use std::array;
use std::collections::HashSet;
use std::io::Read;
use std::{fs::read_to_string, path::PathBuf};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleHasher;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_prover::stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo_cairo_prover::{prover::prove_cairo_with_memory_pool, stwo::prover::mempool::BaseColumnPool};
use tracing::{Level, span};

pub use stwo_run_and_prove::{
    ProveConfig, ProverTrait, RunConfig, StwoProverEntryPoint, StwoRunAndProveError,
    stwo_run_and_prove,
};

/// Circuit Verifies a [CairoProof].
fn verify_cairo(proof: &CairoProof<Blake2sM31MerkleHasher>) -> Result<Context<QM31>, String> {
    let FlatClaim { component_enable_bits, component_log_sizes: _, public_data: _ } =
        proof.claim.flatten_claim();

    let components = HashSet::from_iter(
        zip_eq(all_components::<QM31>().into_keys(), &component_enable_bits)
            .filter(|(_, enable_bit)| **enable_bit)
            .map(|(component_name, _)| component_name),
    );

    verify_cairo_with_component_set(proof, components)
}

/// Verifies a [CairoProof] with a given set of components.
fn verify_cairo_with_component_set(
    cairo_proof: &CairoProof<Blake2sM31MerkleHasher>,
    component_set: HashSet<&str>,
) -> Result<Context<QM31>, String> {
    let FlatClaim { component_enable_bits, component_log_sizes: _, public_data: _ } =
        cairo_proof.claim.flatten_claim();
    let components: Vec<Box<dyn CircuitEval<QM31>>> =
        zip_eq(all_components::<QM31>().into_iter(), &component_enable_bits)
            .map(|((component_name, component), &enable_bit)| {
                let component_in_set = component_set.contains(component_name);
                if component_in_set != enable_bit {
                    return Err(format!(
                        "Proof was produced with the wrong components set: expected the component '{}' to be {} according to the component set, but it is {} in the proof.",
                        component_name,
                        if component_in_set { "enabled" } else { "disabled" },
                        if enable_bit { "enabled" } else { "disabled" }
                    ));
                }
                Ok(if enable_bit { component } else { Box::new(EmptyComponent {}) })
            })
            .try_collect()?;

    let proof_config = ProofConfig::from_components(
        &components,
        PREPROCESSED_COLUMNS_ORDER.len(),
        &cairo_proof.extended_stark_proof.proof.config,
        INTERACTION_POW_BITS,
    );

    let (proof, public_data) = prepare_cairo_proof_for_circuit_verifier(cairo_proof, &proof_config);
    let (public_claim, outputs, program) = public_data.pack_into_u32s();
    let outputs = outputs
        .chunks_exact(MEMORY_VALUES_LIMBS)
        .map(|chunk| array::from_fn(|i| M31::from_u32_unchecked(chunk[i])))
        .collect_vec();
    let program = program
        .chunks_exact(MEMORY_VALUES_LIMBS)
        .map(|chunk| array::from_fn(|i| M31::from_u32_unchecked(chunk[i])))
        .collect_vec();

    let verifier_config = CairoVerifierConfig {
        proof_config,
        program,
        n_outputs: cairo_proof.claim.public_data.public_memory.output.len(),
    };

    verify_fixed_cairo_circuit(verifier_config, proof, public_claim, outputs)
}

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
        let mut base_column_pool = BaseColumnPool::new();
        let proof_params = if let Some(proof_params_json) = proof_params_json {
            let s = read_to_string(&proof_params_json)
                .map_err(|e| StwoRunAndProveError::PathIO(e, proof_params_json.clone()))?;
            serde_json::from_str(&s)
                .map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?
        } else {
            panic!("Proof parameters JSON file is required");
        };

        let span = span!(Level::INFO, "proving cairo").entered();
        let cairo_proof = prove_cairo_with_memory_pool::<Blake2sM31MerkleChannel>(&mut base_column_pool, prover_input.clone(), proof_params)
            .map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?;
        span.exit();

        println!("finished proving");

        let span = span!(Level::INFO, "building verification context").entered();
        let mut context = verify_cairo(&cairo_proof).unwrap();
        span.exit();


       
        let preprocessed_circuit = preprocess_circuit(&mut context);
        let context_values = context.values();
    
        let span = span!(Level::INFO, "proving verification circuit").entered();

        // Create a named pipe and wait till the user writes to it.
        let pid = format!("{}", std::process::id());
        let pipe_path = format!("/tmp/proving_service_{pid}.pipe");
        std::process::Command::new("mkfifo")
            .arg(&pipe_path)
            .status()
            .expect("failed to create named pipe");
        println!("Waiting for signal on named pipe: {pipe_path}");
        println!("Run: samply record --pid {pid} & echo go > {pipe_path}");
        let mut pipe = std::fs::File::open(&pipe_path).expect("failed to open named pipe");
        let mut buf = String::new();
        pipe.read_to_string(&mut buf).expect("failed to read from named pipe");
        std::fs::remove_file(&pipe_path).ok();

        let cairo_proof = prove_cairo_with_memory_pool::<Blake2sM31MerkleChannel>(&mut base_column_pool, prover_input, proof_params).map_err(|e| StwoRunAndProveError::Anyhow(anyhow::Error::from(e)))?;
        let mut context = verify_cairo(&cairo_proof).unwrap();
        finalize_context(&mut context);
        
        let _proof = prove_circuit_assignment(context_values, preprocessed_circuit, &mut base_column_pool);

    
        span.exit();

        // TODO: Serialize the proof to a file.

        Ok(())
    }
}
