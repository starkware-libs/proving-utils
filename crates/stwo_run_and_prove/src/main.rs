use anyhow::Result;
use cairo_air::utils::ProofFormat;
use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::utils::{get_cairo_run_config, get_program, get_program_input};
use cairo_vm::Felt252;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use cairo_vm::vm::errors::vm_errors::VirtualMachineError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;
use clap::Parser;
#[cfg(test)]
use mockall::automock;
#[cfg(test)]
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_prover::prover::create_and_serialize_proof;
use stwo_cairo_prover::stwo::prover::ProvingError;
use stwo_cairo_utils::binary_utils::run_binary;
use stwo_cairo_utils::file_utils::IoErrorWithPath;
use thiserror::Error;
use tracing::{Level, error, info, span};

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
        help = "Optional absolute path for the program output."
    )]
    program_output: Option<PathBuf>,
}

#[derive(Debug, Error)]
enum StwoRunAndProveError {
    #[error(transparent)]
    Cli(#[from] clap::Error),
    #[error("IO error on file '{path:?}': {source}")]
    PathIO {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    CairoRun(Box<CairoRunError>),
    #[error("Program error on file '{path:?}': {source}")]
    Program { path: PathBuf, source: ProgramError },
    #[error(transparent)]
    Runner(#[from] RunnerError),
    #[error("File error on file '{path:?}': {source}")]
    File {
        path: PathBuf,
        source: IoErrorWithPath,
    },
    #[error(transparent)]
    Serializing(#[from] sonic_rs::error::Error),
    #[error(transparent)]
    Proving(#[from] ProvingError),
    #[error(transparent)]
    VM(#[from] VirtualMachineError),
    #[error("Failed to parse output line as Felt decimal.")]
    OutputParsing,
    #[error(transparent)]
    Anyhow(#[from] anyhow::Error),
}

// Implement From<Box<CairoRunError>> manually
impl From<CairoRunError> for StwoRunAndProveError {
    fn from(err: CairoRunError) -> Self {
        StwoRunAndProveError::CairoRun(Box::new(err))
    }
}

impl From<(std::io::Error, PathBuf)> for StwoRunAndProveError {
    fn from((source, path): (std::io::Error, PathBuf)) -> Self {
        StwoRunAndProveError::PathIO { path, source }
    }
}

impl From<(ProgramError, PathBuf)> for StwoRunAndProveError {
    fn from((source, path): (ProgramError, PathBuf)) -> Self {
        StwoRunAndProveError::Program { path, source }
    }
}

impl From<(IoErrorWithPath, PathBuf)> for StwoRunAndProveError {
    fn from((source, path): (IoErrorWithPath, PathBuf)) -> Self {
        StwoRunAndProveError::File { path, source }
    }
}

struct ProveConfig {
    proof_path: PathBuf,
    proof_format: ProofFormat,
    verify: bool,
    prover_params_json: Option<PathBuf>,
}

fn main() -> ExitCode {
    run_binary(run, "stwo_run_and_prove")
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

    let stwo_prover = Box::new(StwoProverEntryPoint);
    stwo_run_and_prove(
        args.program,
        args.program_input,
        args.program_output,
        prove_config,
        stwo_prover,
    )?;
    Ok(())
}

/// Runs the program and generates a proof for it, then saves the proof to the given path.
/// If `program_output` is provided, saves the program output to that path.
fn stwo_run_and_prove(
    program_path: PathBuf,
    program_input: Option<PathBuf>,
    program_output: Option<PathBuf>,
    prove_config: ProveConfig,
    prover: Box<dyn ProverTrait>,
) -> Result<(), StwoRunAndProveError> {
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
        .map_err(|e| StwoRunAndProveError::from((e, program_path)))?;
    let program_input = get_program_input(&program_input)
        .map_err(|e| StwoRunAndProveError::from((e, program_input.unwrap_or_default())))?;
    let runner = cairo_run_program(&program, program_input, cairo_run_config)?;
    let prover_input = adapt(&runner)?;
    prove(prover_input, prove_config, prover)?;
    if let Some(output_path) = program_output {
        write_output_to_file(runner, output_path)?;
    }

    Ok(())
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
            if is_file_missing_or_empty(&prove_config.proof_path)? {
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
trait ProverTrait {
    fn create_and_serialize_proof(
        &self,
        input: ProverInput,
        verify: bool,
        proof_path: PathBuf,
        proof_format: ProofFormat,
        proof_params_json: Option<PathBuf>,
    ) -> Result<(), StwoRunAndProveError>;
}

struct StwoProverEntryPoint;

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

/// Write the program output to the specified output path as Felt252 values.
fn write_output_to_file(
    mut runner: CairoRunner,
    output_path: PathBuf,
) -> Result<(), StwoRunAndProveError> {
    info!("Saving program output to: {:?}", output_path);
    // TODO(Nitsan): move this function to cairo_program_runner_lib or a new utils lib,
    // and call it from here and from cairo_program_runner.

    let mut output_buffer = String::new();
    runner.vm.write_output(&mut output_buffer)?;
    let output_lines = output_buffer
        .lines()
        .map(|line: &str| {
            Felt252::from_dec_str(line).map_err(|_| StwoRunAndProveError::OutputParsing)
        })
        .collect::<Result<Vec<Felt252>, _>>()?;
    std::fs::write(&output_path, sonic_rs::to_string_pretty(&output_lines)?)
        .map_err(|e| StwoRunAndProveError::from((e, output_path)))?;
    Ok(())
}

fn is_file_empty(path: &PathBuf) -> std::io::Result<bool> {
    let metadata = fs::metadata(path)?;
    Ok(metadata.len() == 0)
}

fn is_file_missing_or_empty(path: &PathBuf) -> std::io::Result<bool> {
    match std::fs::metadata(path) {
        Ok(_) => is_file_empty(path),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(true),
        Err(e) => Err(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ctor::ctor;
    use stwo_cairo_utils::logging_utils::init_logging;
    use tempfile::{NamedTempFile, TempPath};

    const ARRAY_SUM_EXPECTED_OUTPUT: [Felt252; 1] = [Felt252::from_hex_unchecked("0x32")];
    const RESOURCES_PATH: &str = "resources";
    const PROGRAM_FILE_NAME: &str = "array_sum.json";
    const PROVER_PARAMS_FILE_NAME: &str = "prover_params.json";
    const EXPECTED_PROOF_FILE_NAME: &str = "array_sum_proof";

    #[ctor]
    fn init_logging_once() {
        init_logging(log::LevelFilter::Info);
    }

    fn get_path(file_name: &str) -> PathBuf {
        let current_path = env::current_dir().expect("failed to get current directory");
        current_path.join(RESOURCES_PATH).join(file_name)
    }

    fn prepare_args() -> (Args, TempPath, TempPath) {
        let program_output_tempfile = NamedTempFile::new()
            .expect("Failed to create temp file for program output")
            .into_temp_path();
        let proof_tempfile = NamedTempFile::new()
            .expect("Failed to create temp file for proof")
            .into_temp_path();
        let args = Args {
            program: get_path(PROGRAM_FILE_NAME),
            program_input: None,
            program_output: Some(program_output_tempfile.to_path_buf()),
            prover_params_json: Some(get_path(PROVER_PARAMS_FILE_NAME)),
            proof_path: proof_tempfile.to_path_buf(),
            proof_format: ProofFormat::CairoSerde,
            verify: true,
        };

        (args, program_output_tempfile, proof_tempfile)
    }

    fn run_stwo_run_and_prove(
        args: Args,
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
        )
    }

    fn run_with_successful_mock_prover() -> (TempPath, TempPath) {
        let (args, program_output_tempfile, proof_tempfile) = prepare_args();

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

    fn run_with_failed_mock_prover() -> (TempPath, TempPath) {
        let (args, program_output_tempfile, proof_tempfile) = prepare_args();

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

        (program_output_tempfile, proof_tempfile)
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
        let (output_tempfile, proof_tempfile) = run_with_failed_mock_prover();

        assert!(
            is_file_empty(&proof_tempfile.to_path_buf()).unwrap(),
            "proof file should be empty after running with proving failure",
        );
        assert!(
            is_file_empty(&output_tempfile.to_path_buf()).unwrap(),
            "Output file should be empty after running with proving failure",
        );
    }
}
