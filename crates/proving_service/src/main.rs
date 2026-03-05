use cairo_air::{PreProcessedTraceVariant, utils::ProofFormat};
use cairo_program_runner_lib::utils::get_program_input_from_path;
use circuit_cairo_air::privacy::privacy_cairo_verifier_config;
use circuit_cairo_air::verify::build_cairo_verifier_circuit;
use circuit_prover::prover::BaseColumnPool;
use circuit_prover::witness::preprocessed::PreprocessedCircuit;
use stwo::{core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel, prover::{CommitmentTreeProver, poly::circle::PolyOps}};
use stwo_cairo_prover::witness::{prelude::{CanonicCoset, SimdBackend}, preprocessed_trace::gen_trace};
use clap::Parser;
use proving_service::ProvingServiceEntryPoint;
use std::{cmp::max, path::PathBuf, sync::Arc};
use std::process::ExitCode;
use stwo_cairo_utils::binary_utils::run_binary;
use stwo_run_and_prove::{ProveConfig, RunConfig, StwoRunAndProveError, stwo_run_and_prove};
use tracing::{Level, span};

/// This binary runs a cairo program and generates a Stwo proof for it.
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "program", help = "Absolute path to the compiled program.")]
    program: PathBuf,
    #[clap(
        long = "program_input",
        help = "Absolute path to the program input file."
    )]
    program_input: Option<PathBuf>,
    #[clap(
        long = "prover_params_json",
        help = "Absolute path to the JSON file containing the prover parameters."
    )]
    prover_params_json: Option<PathBuf>,
    #[clap(
        long = "proof_path",
        help = "Absolute path where the generated proof will be saved."
    )]
    proof_path: PathBuf,
    #[clap(long, value_enum, default_value_t = ProofFormat::CairoSerde, help = "Json or cairo-serde.")]
    proof_format: ProofFormat,
    #[clap(long = "verify", help = "Should verify the generated proof.")]
    verify: bool,
    #[clap(
        long = "program_output",
        help = "Optional absolute path where the program's output will be saved."
    )]
    program_output: Option<PathBuf>,
    #[clap(
        long = "save_debug_data",
        help = "Should save the ProverInput to a file in `debug_data_dir` for both success and failure."
    )]
    save_debug_data: bool,
    #[clap(
        long = "debug_data_dir",
        help = "Absolute path to the output directory where the ProverInput will be saved in the
        case of a proving error, or when the save_debug_data flag is enabled."
    )]
    debug_data_dir: Option<PathBuf>,
}

fn main() -> ExitCode {
    run_binary(run, "proving_service")
}

fn run() -> Result<(), StwoRunAndProveError> {
    let _span = span!(Level::INFO, "run").entered();
    let args = Args::parse();
    let prove_config = ProveConfig {
        verify: args.verify,
        proof_path: args.proof_path,
        proof_format: args.proof_format,
        prover_params_json: args.prover_params_json,
    };

    let privacy_verifier_config = privacy_cairo_verifier_config();
    let proof_config = &privacy_verifier_config.proof_config;
    let mut novalue_context = build_cairo_verifier_circuit(&privacy_verifier_config);
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut novalue_context);
    
    

    let cairo_evaluation_domain_log_size = proof_config.log_evaluation_domain_size().try_into().unwrap();


    let circuit_proof_log_blowup_factor = 1;
    let max_domain_size = max(preprocessed_circuit.params.trace_log_size + circuit_proof_log_blowup_factor, cairo_evaluation_domain_log_size);

    // Precompute twiddles.
    // Account for blowup factor and for composition polynomial calculation (taking the max since
    // the composition polynomial is split prior to LDE).
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            max_domain_size,
        )
        .circle_domain()
        .half_coset,
    );


    let preprocessed_trace = Arc::new(PreProcessedTraceVariant::CanonicalSmall.to_preprocessed_trace());
    let preprocessed_trace_polys =
        SimdBackend::interpolate_columns(gen_trace(preprocessed_trace.clone()), &twiddles);


    let store_polynomials_coefficients = true;

    let base_column_pool = BaseColumnPool::<SimdBackend>::new();
    let cairo_preprocessed_tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        preprocessed_trace_polys,
        proof_config.fri.log_blowup_factor.try_into().unwrap(),
        &twiddles,
        store_polynomials_coefficients,
        Some(cairo_evaluation_domain_log_size),
        &base_column_pool,
    );

    let circuit_preprocessed_trace = preprocessed_circuit.preprocessed_trace.get_trace::<SimdBackend>();
    let circuit_preprocessed_trace_polys = SimdBackend::interpolate_columns(circuit_preprocessed_trace, &twiddles);

    let circuit_preprocessed_tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        circuit_preprocessed_trace_polys,
        circuit_proof_log_blowup_factor,
        &twiddles,
        store_polynomials_coefficients,
        None,
        &base_column_pool,
    );



 
    let prover = Box::new(ProvingServiceEntryPoint { base_column_pool, preprocessed_circuit, privacy_verifier_config, twiddles, cairo_preprocessed_tree, circuit_preprocessed_tree });
    let run_config = RunConfig {
        program_path: args.program,
        program_input: get_program_input_from_path(&args.program_input)?,
        program_output: args.program_output,
        debug_data_dir: args.debug_data_dir,
        save_debug_data: args.save_debug_data,
        extra_hint_processor: None,
    };
    // Sleep for 1 second to create a seperation between the preproccessing and the proving.
    std::thread::sleep(std::time::Duration::from_secs(1));
    stwo_run_and_prove(run_config, prove_config, prover)?;
    Ok(())
}
