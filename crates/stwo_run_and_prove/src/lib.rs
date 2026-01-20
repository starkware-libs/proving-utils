use anyhow::Result;
use cairo_air::utils::ProofFormat;
use cairo_program_runner_lib::ProgramInput;
use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_cairo_run_config, get_program, write_output_to_file};
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use cairo_vm::vm::errors::vm_errors::VirtualMachineError;
#[cfg(test)]
use mockall::automock;
use std::fs;
use std::path::PathBuf;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_prover::prover::create_and_serialize_proof;
use thiserror::Error;
use tracing::{Level, error, info, span};

static PROVER_INPUT_FILE_NAME: &str = "prover_input.json";

#[derive(Debug, Error)]
pub enum StwoRunAndProveError {
    #[error(transparent)]
    Cli(#[from] clap::Error),
    #[error("IO error on file '{1:?}': {0}")]
    PathIO(std::io::Error, PathBuf),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    CairoRun(Box<CairoRunError>),
    #[error("Program error on file '{1:?}': {0}")]
    Program(ProgramError, PathBuf),
    #[error(transparent)]
    Runner(#[from] RunnerError),
    #[error(transparent)]
    Serializing(#[from] sonic_rs::error::Error),
    #[error(transparent)]
    VM(#[from] VirtualMachineError),
    #[error(transparent)]
    Anyhow(#[from] anyhow::Error),
}

// Implement From<Box<CairoRunError>> manually.
impl From<CairoRunError> for StwoRunAndProveError {
    fn from(err: CairoRunError) -> Self {
        StwoRunAndProveError::CairoRun(Box::new(err))
    }
}

pub struct ProveConfig {
    pub proof_path: PathBuf,
    pub proof_format: ProofFormat,
    pub verify: bool,
    pub prover_params_json: Option<PathBuf>,
}

/// Runs the program and generates a proof for it, then saves the proof to the given path.
/// If `debug_data_dir` is provided, and there is a proving error or the `save_debug_data` flag is
/// enabled, saves the debug data to that path.
/// If `program_output` is provided, the program output to that path.
pub fn stwo_run_and_prove(
    program_path: PathBuf,
    program_input: Option<ProgramInput>,
    program_output: Option<PathBuf>,
    prove_config: ProveConfig,
    prover: Box<dyn ProverTrait>,
    debug_data_dir: Option<PathBuf>,
    save_debug_data: bool,
) -> Result<(), StwoRunAndProveError> {
    let _span = span!(Level::INFO, "stwo_run_and_prove").entered();
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
    )?;

    let program = get_program(program_path.as_path())
        .map_err(|e| StwoRunAndProveError::Program(e, program_path))?;
    let mut runner = cairo_run_program(&program, program_input, cairo_run_config)?;
    let prover_input = adapt(&runner)?;
    let result = prove(prover_input.clone(), prove_config, prover);

    if let Some(data_dir) = debug_data_dir
        && (result.is_err() || save_debug_data)
    {
        // create the directory if it doesn't exist.
        std::fs::create_dir_all(&data_dir)?;
        let prover_input_path = data_dir.join(PROVER_INPUT_FILE_NAME);
        std::fs::write(
            &prover_input_path,
            sonic_rs::to_string_pretty(&prover_input)?,
        )
        .map_err(|e| StwoRunAndProveError::PathIO(e, data_dir))?
    }

    if let Some(output_path) = program_output
        && result.is_ok()
    {
        info!("Saving program output to: {:?}", output_path);
        write_output_to_file(&mut runner, output_path)?;
    }

    result
}

/// Prepares the prover parameters and generates a proof given the prover input and parameters.
/// Verifies the proof in case the respective flag is set.
fn prove(
    prover_input: ProverInput,
    prove_config: ProveConfig,
    prover: Box<dyn ProverTrait>,
) -> Result<(), StwoRunAndProveError> {
    let _span = span!(Level::INFO, "prove").entered();

    match prover.create_and_serialize_proof(
        prover_input.clone(),
        prove_config.verify,
        prove_config.proof_path.clone(),
        prove_config.proof_format.clone(),
        prove_config.prover_params_json.clone(),
    ) {
        Ok(()) => {
            info!("Proof generated and verified successfully.");
            Ok(())
        }

        Err(e) => {
            if file_missing_or_empty(&prove_config.proof_path)? {
                error!("Proving failed with error {e}");
            } else {
                error!(
                    "Proof was generated successfully, but its verification failed with error {e}. The failed proof was written to the proof file."
                );
            }
            Err(e)
        }
    }
}

#[cfg_attr(test, automock)]
pub trait ProverTrait {
    fn create_and_serialize_proof(
        &self,
        input: ProverInput,
        verify: bool,
        proof_path: PathBuf,
        proof_format: ProofFormat,
        proof_params_json: Option<PathBuf>,
    ) -> Result<(), StwoRunAndProveError>;
}

pub struct StwoProverEntryPoint;

impl ProverTrait for StwoProverEntryPoint {
    fn create_and_serialize_proof(
        &self,
        prover_input: ProverInput,
        verify: bool,
        proof_path: PathBuf,
        proof_format: ProofFormat,
        proof_params_json: Option<PathBuf>,
    ) -> Result<(), StwoRunAndProveError> {
        create_and_serialize_proof(
            prover_input,
            verify,
            proof_path,
            proof_format,
            proof_params_json,
        )?;

        Ok(())
    }
}

fn file_empty(path: &PathBuf) -> std::io::Result<bool> {
    let metadata = fs::metadata(path)?;
    Ok(metadata.len() == 0)
}

fn file_exists(path: &PathBuf) -> bool {
    std::fs::metadata(path).is_ok()
}

fn file_missing_or_empty(path: &PathBuf) -> std::io::Result<bool> {
    if !file_exists(path) {
        return Ok(true);
    }
    file_empty(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cairo_vm::Felt252;
    use ctor::ctor;
    use serde_json::Value;
    use std::env;
    use stwo_cairo_utils::logging_utils::init_logging;
    use tempfile::{NamedTempFile, TempDir, TempPath};

    const ARRAY_SUM_EXPECTED_OUTPUT: [Felt252; 1] = [Felt252::from_hex_unchecked("0x32")];
    const RESOURCES_PATH: &str = "resources";
    const PROGRAM_FILE_NAME: &str = "array_sum.json";
    const PROVER_PARAMS_FILE_NAME: &str = "prover_params.json";
    const EXPECTED_PROOF_FILE_NAME: &str = "expected_array_sum_proof";
    const EXPECTED_PROVER_INPUT_FILE_NAME: &str = "expected_prover_input.json";

    #[ctor]
    fn init_logging_once() {
        init_logging(log::LevelFilter::Info);
    }

    fn get_path(file_name: &str) -> PathBuf {
        let current_path = env::current_dir().expect("failed to get current directory");
        current_path.join(RESOURCES_PATH).join(file_name)
    }

    struct TestArgs {
        program: PathBuf,
        program_input: Option<ProgramInput>,
        program_output: Option<PathBuf>,
        prover_params_json: Option<PathBuf>,
        proof_path: PathBuf,
        proof_format: ProofFormat,
        save_debug_data: bool,
        debug_data_dir: Option<PathBuf>,
        verify: bool,
    }

    fn prepare_args() -> (TestArgs, TempPath, TempPath, TempDir) {
        let program_output_tempfile = NamedTempFile::new()
            .expect("Failed to create temp file for program output")
            .into_temp_path();
        let proof_tempfile = NamedTempFile::new()
            .expect("Failed to create temp file for proof")
            .into_temp_path();
        let debug_data_tempdir =
            TempDir::new().expect("Failed to create temp directory for debug data");
        let args = TestArgs {
            program: get_path(PROGRAM_FILE_NAME),
            program_input: None,
            program_output: Some(program_output_tempfile.to_path_buf()),
            prover_params_json: Some(get_path(PROVER_PARAMS_FILE_NAME)),
            proof_path: proof_tempfile.to_path_buf(),
            proof_format: ProofFormat::CairoSerde,
            save_debug_data: false,
            debug_data_dir: Some(debug_data_tempdir.path().to_path_buf()),
            verify: true,
        };

        (
            args,
            program_output_tempfile,
            proof_tempfile,
            debug_data_tempdir,
        )
    }

    fn run_stwo_run_and_prove(
        args: TestArgs,
        prover: Box<dyn ProverTrait>,
    ) -> Result<(), StwoRunAndProveError> {
        let prove_config = ProveConfig {
            verify: args.verify,
            proof_path: args.proof_path,
            proof_format: args.proof_format,
            prover_params_json: args.prover_params_json,
        };

        stwo_run_and_prove(
            args.program,
            args.program_input,
            args.program_output,
            prove_config,
            prover,
            args.debug_data_dir,
            args.save_debug_data,
        )
    }

    fn run_with_successful_mock_prover() -> (TempPath, TempPath) {
        let (args, program_output_tempfile, proof_tempfile, _) = prepare_args();

        let mut mock_prover = Box::new(MockProverTrait::new());
        mock_prover
            .expect_create_and_serialize_proof()
            .times(1)
            .returning(move |_, _, proof_file, _, _| {
                let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
                fs::copy(&expected_proof_file, &proof_file).expect("Failed to copy proof file.");
                Ok(())
            });

        run_stwo_run_and_prove(args, mock_prover).expect("failed to run stwo_run_and_prove");

        (program_output_tempfile, proof_tempfile)
    }

    fn run_with_failed_mock_prover() -> (TempPath, TempPath, TempDir) {
        let (args, program_output_tempfile, proof_tempfile, debug_data_tempdir) = prepare_args();

        let mut mock_prover = Box::new(MockProverTrait::new());
        mock_prover
            .expect_create_and_serialize_proof()
            .times(1)
            .returning(move |_, _, _, _, _| {
                Err(StwoRunAndProveError::Anyhow(anyhow::anyhow!(
                    "mocked anyhow error"
                )))
            });

        let result = run_stwo_run_and_prove(args, mock_prover);
        assert!(
            matches!(result, Err(StwoRunAndProveError::Anyhow(_))),
            "run and prove should return Err(StwoRunAndProveError::Anyhow), but got: {result:?}",
        );

        (program_output_tempfile, proof_tempfile, debug_data_tempdir)
    }

    /// Sort the public_memory_addresses array in the Json, since its order is not deterministic.
    fn normalize_public_memory_addresses(value: &mut Value) {
        if let Value::Object(map) = value
            && let Some(Value::Array(arr)) = map.get_mut("public_memory_addresses")
        {
            assert!(arr.iter().all(|v| v.is_number()));
            arr.sort_by_key(|v| v.as_u64().unwrap());
        }
    }

    /// Reads the JSON content from the given file path and normalizes it.
    fn get_json_normalized_content(file_path: &PathBuf, file_name: &str) -> serde_json::Value {
        let content = std::fs::read(file_path)
            .unwrap_or_else(|e| panic!("Failed to read {file_name:?} file: {e}"));
        let mut json: serde_json::Value =
            serde_json::from_slice(&content).expect("Failed to parse prover input JSON");
        normalize_public_memory_addresses(&mut json);
        json
    }

    #[test]
    fn test_stwo_run_and_prove() {
        let (output_tempfile, proof_tempfile) = run_with_successful_mock_prover();

        // Verifying the proof content.
        let proof_content =
            std::fs::read_to_string(proof_tempfile).expect("Failed to read proof file");
        let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
        let expected_proof_content = std::fs::read_to_string(expected_proof_file)
            .expect("Failed to read expected proof file");
        assert_eq!(
            proof_content, expected_proof_content,
            "Proof content does not match expected proof content"
        );

        // Verifying the proof output.
        let output_content =
            std::fs::read_to_string(output_tempfile).expect("Failed to read output file");
        let output: Vec<Felt252> =
            sonic_rs::from_str(&output_content).expect("Failed to parse output");
        assert_eq!(
            output, ARRAY_SUM_EXPECTED_OUTPUT,
            "Expected output to be {ARRAY_SUM_EXPECTED_OUTPUT:?}",
        );
    }

    #[test]
    fn test_stwo_run_and_prove_proving_failure() {
        let (output_tempfile, proof_tempfile, debug_data_tempdir) = run_with_failed_mock_prover();

        assert!(
            file_empty(&proof_tempfile.to_path_buf()).unwrap(),
            "proof file should be empty after running with proving failure",
        );
        assert!(
            file_empty(&output_tempfile.to_path_buf()).unwrap(),
            "Output file should be empty after running with proving failure",
        );
        assert!(
            file_exists(&debug_data_tempdir.path().join(PROVER_INPUT_FILE_NAME)),
            "Prover input file was not created in the debug data directory, or was created with an
            incorrect name, after running with a proving failure. NOTE: Changing the file name may
            break external dependencies.",
        );

        // Verifying the prover input content.
        let prover_input_json = get_json_normalized_content(
            &debug_data_tempdir.path().join(PROVER_INPUT_FILE_NAME),
            PROVER_INPUT_FILE_NAME,
        );
        let expected_prover_input_json = get_json_normalized_content(
            &get_path(EXPECTED_PROVER_INPUT_FILE_NAME),
            EXPECTED_PROVER_INPUT_FILE_NAME,
        );

        assert_eq!(
            prover_input_json, expected_prover_input_json,
            "Prover input JSON does not match expected prover input JSON."
        );
    }
}
