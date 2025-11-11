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
use tracing::{Level, error, info, span, warn};

static PROOF_PREFIX: &str = "proof_";
static SUCCESS_SUFFIX: &str = "_success";
static FAILURE_SUFFIX: &str = "_failure";

fn parse_usize_ge1(s: &str) -> Result<usize, String> {
    let v: usize = s.parse().map_err(|_| "must be a number".to_string())?;
    if v >= 1 {
        Ok(v)
    } else {
        Err("must be >= 1".into())
    }
}

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
        long = "proofs_dir",
        help = "Absolute path to the output directory where the generated proofs will be saved (may include
    multiple proofs from repeated attempts)."
    )]
    proofs_dir: PathBuf,
    #[clap(long, value_enum, default_value_t = ProofFormat::CairoSerde, help = "Json or cairo-serde.")]
    proof_format: ProofFormat,
    #[clap(
        long = "n_proof_attempts",
        help = "Number of attempts for proving, in case the proof verification fails.",
        default_value_t = 1usize,
        requires = "verify",
        value_parser = parse_usize_ge1
    )]
    n_proof_attempts: usize,
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
    proofs_dir: PathBuf,
    proof_format: ProofFormat,
    verify: bool,
    n_proof_attempts: usize,
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
        proofs_dir: args.proofs_dir,
        proof_format: args.proof_format,
        n_proof_attempts: args.n_proof_attempts,
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

/// Runs the program and generates a proof for it.
/// Saves the proof to the specified output dir (may include multiple proofs from repeated
/// attempts). If `program_output` is provided, saves the program output to that path.
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
    prove_with_retries(prover_input, prove_config, prover)?;
    if let Some(output_path) = program_output {
        write_output_to_file(runner, output_path)?;
    }

    Ok(())
}

/// Prepares the prover parameters and generates proof given the prover input and parameters.
/// Verifies the proof in case the respective flag is set.
/// In case the proving fails or the proof verification fails, it retries up to `n_proof_attempts`
/// times.
/// Returns the program output.
fn prove_with_retries(
    prover_input: ProverInput,
    prove_config: ProveConfig,
    prover: Box<dyn ProverTrait>,
) -> Result<(), StwoRunAndProveError> {
    let _span = span!(Level::INFO, "prove_with_retries").entered();
    // create the directory if it doesn't exist, attach the proofs_dir path on error.
    std::fs::create_dir_all(&prove_config.proofs_dir)
        .map_err(|e| StwoRunAndProveError::from((e, prove_config.proofs_dir.clone())))?;
    let proof_format = prove_config.proof_format;

    for i in 1..=prove_config.n_proof_attempts {
        let _attempt_span = span!(
            Level::INFO,
            "prove_attempt",
            attempt = i,
            out_of = prove_config.n_proof_attempts
        )
        .entered();
        let proof_file_path = prove_config.proofs_dir.join(format!("{PROOF_PREFIX}{i}"));
        let proof_file_name = proof_file_path
            .file_name()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidInput, "no file name"))?;

        match prover.create_and_serialize_proof(
            prover_input.clone(),
            prove_config.verify,
            proof_file_path.clone(),
            proof_format.clone(),
            prove_config.prover_params_json.clone(),
        ) {
            Ok(()) => {
                info!(
                    "Proof generated and verified successfully on attempt {}/{}",
                    i, prove_config.n_proof_attempts
                );
                let success_path = proof_file_path.with_file_name(format!(
                    "{}{}",
                    proof_file_name.to_string_lossy(),
                    SUCCESS_SUFFIX
                ));
                fs::rename(proof_file_path, &success_path)?;
                return Ok(());
            }

            Err(e) => {
                if proof_file_path.exists() {
                    let failure_path = proof_file_path.with_file_name(format!(
                        "{}{}",
                        proof_file_name.to_string_lossy(),
                        FAILURE_SUFFIX
                    ));
                    fs::rename(proof_file_path, &failure_path)?;
                }
                if i < prove_config.n_proof_attempts {
                    warn!(
                        "Proving failed on attempt {}/{}. Retrying.",
                        i, prove_config.n_proof_attempts
                    );
                    continue;
                }
                error!(
                    "Proving failed on last attempt - {}/{}.",
                    i, prove_config.n_proof_attempts
                );
                return Err(e);
            }
        }
    }

    panic!("Should not reach here, n_proof_attempts should be at least 1.");
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

#[cfg(test)]
mod tests {
    use super::*;
    use ctor::ctor;
    use rstest::rstest;
    use std::fs;
    use stwo_cairo_utils::logging_utils::init_logging;
    use tempfile::{NamedTempFile, TempDir, TempPath};

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

    fn is_file_empty(path: &PathBuf) -> std::io::Result<bool> {
        let metadata = fs::metadata(path)?;
        Ok(metadata.len() == 0)
    }

    fn prepare_args(n_proof_attempts: usize) -> (Args, TempPath, TempDir) {
        let program_output_tempfile = NamedTempFile::new()
            .expect("Failed to create temp file for program output")
            .into_temp_path();
        let proofs_tempdir = TempDir::new().expect("Failed to create temp directory for proofs");
        let args = Args {
            program: get_path(PROGRAM_FILE_NAME),
            program_input: None,
            program_output: Some(program_output_tempfile.to_path_buf()),
            prover_params_json: Some(get_path(PROVER_PARAMS_FILE_NAME)),
            proofs_dir: proofs_tempdir.path().to_path_buf(),
            proof_format: ProofFormat::CairoSerde,
            n_proof_attempts,
            verify: true,
        };

        (args, program_output_tempfile, proofs_tempdir)
    }

    fn run_stwo_run_and_prove(
        args: Args,
        prover: Box<dyn ProverTrait>,
    ) -> Result<(), StwoRunAndProveError> {
        let prove_config = ProveConfig {
            verify: args.verify,
            proofs_dir: args.proofs_dir,
            proof_format: args.proof_format,
            n_proof_attempts: args.n_proof_attempts,
            prover_params_json: args.prover_params_json,
        };

        stwo_run_and_prove(
            args.program,
            args.program_input,
            args.program_output.clone(),
            prove_config,
            prover,
        )
    }

    fn run_with_successful_mock_prover(n_proof_attempts: usize) -> (TempPath, TempDir) {
        let (args, program_output_tempfile, proofs_tempdir) = prepare_args(n_proof_attempts);

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

        (program_output_tempfile, proofs_tempdir)
    }

    fn run_with_failed_mock_prover(
        n_proof_attempts: usize,
        is_verification_failure: bool,
    ) -> (TempPath, TempDir) {
        let (args, program_output_tempfile, proofs_tempdir) = prepare_args(n_proof_attempts);

        let mut mock_prover = Box::new(MockProverTrait::new());
        mock_prover
            .expect_create_and_serialize_proof()
            .times(n_proof_attempts)
            .returning(move |_, _, proof_file, _, _| {
                if is_verification_failure {
                    let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
                    fs::copy(&expected_proof_file, &proof_file)
                        .expect("Failed to copy proof file.");
                }
                Err(StwoRunAndProveError::Anyhow(anyhow::anyhow!(
                    "mocked anyhow error"
                )))
            });

        let result = run_stwo_run_and_prove(args, mock_prover);
        assert!(
            matches!(result, Err(StwoRunAndProveError::Anyhow(_))),
            "run and prove should return Err(StwoRunAndProveError::Anyhow), but got: {:?}",
            result,
        );

        (program_output_tempfile, proofs_tempdir)
    }

    fn run_with_mock_prover_succeeds_on_retry(
        n_proof_attempts: usize,
        is_verification_failure: bool,
    ) -> (TempPath, TempDir) {
        let (args, program_output_tempfile, proofs_tempdir) = prepare_args(n_proof_attempts);
        let mut mock_prover = Box::new(MockProverTrait::new());

        // Create iterator that return errors for the first n-1 attempts, and a successful result
        // for the last attempt.
        let mut results = (0..n_proof_attempts.saturating_sub(1))
            .map(|_| {
                Err(StwoRunAndProveError::Anyhow(anyhow::anyhow!(
                    "mocked anyhow error"
                )))
            })
            .chain(std::iter::once(Ok(())));

        mock_prover
            .expect_create_and_serialize_proof()
            .times(n_proof_attempts)
            .returning(move |_, _, proof_file, _, _| {
                let res: Result<(), StwoRunAndProveError> =
                    results.next().expect("results exhausted");
                if matches!(res, Ok(()))
                    || (matches!(res, Err(StwoRunAndProveError::Anyhow(_)))
                        && is_verification_failure)
                {
                    let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
                    fs::copy(&expected_proof_file, &proof_file)
                        .expect("Failed to copy proof file.");
                }
                res
            });

        run_stwo_run_and_prove(args, mock_prover).expect("failed to run stwo_run_and_prove");
        (program_output_tempfile, proofs_tempdir)
    }

    #[test]
    fn test_stwo_run_and_prove() {
        let (output_temp_file, proofs_temp_dir) = run_with_successful_mock_prover(1);

        // Verifying the proof content.
        let proof_file = proofs_temp_dir
            .path()
            .to_path_buf()
            .join(format!("{}1{}", PROOF_PREFIX, SUCCESS_SUFFIX));
        let proof_content = std::fs::read_to_string(proof_file).expect("Failed to read proof file");
        let expected_proof_file = get_path(EXPECTED_PROOF_FILE_NAME);
        let expected_proof_content = std::fs::read_to_string(expected_proof_file)
            .expect("Failed to read expected proof file");
        assert_eq!(
            proof_content, expected_proof_content,
            "Proof content does not match expected proof content"
        );

        // Verifying the proof output.
        let output_content =
            std::fs::read_to_string(output_temp_file).expect("Failed to read output file");
        let output: Vec<Felt252> =
            sonic_rs::from_str(&output_content).expect("Failed to parse output");
        assert_eq!(
            output, ARRAY_SUM_EXPECTED_OUTPUT,
            "Expected output to be {:?}",
            ARRAY_SUM_EXPECTED_OUTPUT
        );
    }

    #[test]
    fn test_stwo_run_and_prove_all_retries_fail_on_verification() {
        let n_proof_attempts = 3;
        let (output_temp_file, proofs_temp_dir) =
            run_with_failed_mock_prover(n_proof_attempts, true);
        let proofs_dir = proofs_temp_dir.path().to_path_buf();

        (1..=n_proof_attempts).for_each(|i| {
            let proof_file = proofs_dir.join(format!("{PROOF_PREFIX}{i}{FAILURE_SUFFIX}"));
            assert!(
                proof_file.exists(),
                "Proof file {:?} should exist after running with verifier failures",
                proof_file,
            );
        });

        assert!(
            is_file_empty(&output_temp_file.to_path_buf()).unwrap(),
            "Output file should be empty after running with verifier failures",
        );
    }

    #[test]
    fn test_stwo_run_and_prove_all_retries_fail_on_proving() {
        let n_proof_attempts = 3;
        let (output_temp_file, proofs_temp_dir) =
            run_with_failed_mock_prover(n_proof_attempts, false);
        let proofs_dir = proofs_temp_dir.path().to_path_buf();

        (1..=n_proof_attempts).for_each(|i| {
            let proof_file = proofs_dir.join(format!("{PROOF_PREFIX}{i}{FAILURE_SUFFIX}"));
            assert!(
                !proof_file.exists(),
                "Proof file {:?} should not exist after running with proving failures",
                proof_file,
            );
        });

        assert!(
            is_file_empty(&output_temp_file.to_path_buf()).unwrap(),
            "Output file should be empty after running with proving failures",
        );
    }

    #[rstest]
    #[case::two_tries(2)]
    #[case::three_tries(3)]
    fn test_stwo_run_and_prove_succeeds_on_retry_after_verification_failures(
        #[case] n_proof_attempts: usize,
    ) {
        let (output_temp_file, proofs_temp_dir) =
            run_with_mock_prover_succeeds_on_retry(n_proof_attempts, true);
        let proofs_dir = proofs_temp_dir.path().to_path_buf();

        (1..=n_proof_attempts).for_each(|i| {
            let suffix = if i < n_proof_attempts { FAILURE_SUFFIX } else { SUCCESS_SUFFIX };
            let proof_file = proofs_dir.join(format!("{PROOF_PREFIX}{i}{suffix}"));
            assert!(
                proof_file.exists(),
                "Proof file {:?} should exist after a run that succeeds on attempt {:?} of proof and verify",
                proof_file, n_proof_attempts,
            );
        });

        assert!(
            !is_file_empty(&output_temp_file.to_path_buf()).unwrap(),
            "Output file should not be empty after a run that succeeds on attempt {:?} of proof and verify",
            n_proof_attempts,
        );
    }

    #[rstest]
    #[case::two_tries(2)]
    #[case::three_tries(3)]
    fn test_stwo_run_and_prove_succeeds_on_retry_after_proving_failures(
        #[case] n_proof_attempts: usize,
    ) {
        let (output_temp_file, proofs_temp_dir) =
            run_with_mock_prover_succeeds_on_retry(n_proof_attempts, false);
        let proofs_dir = proofs_temp_dir.path().to_path_buf();

        (1..=n_proof_attempts - 1).for_each(|i| {
            let failed_proof_file = proofs_dir.join(format!("{PROOF_PREFIX}{i}{FAILURE_SUFFIX}"));
            assert!(
                !failed_proof_file.exists(),
                "Proof file {:?} should exist after a run that got proving errors, and succeeded on attempt {:?} of proof and verify",
                failed_proof_file, n_proof_attempts,
            );
        });

        let success_proof_file =
            proofs_dir.join(format!("{PROOF_PREFIX}{n_proof_attempts}{SUCCESS_SUFFIX}"));
        assert!(
            success_proof_file.exists(),
            "Proof file {:?} should exist after a run that succeeds on attempt {:?} of proof and verify",
            success_proof_file,
            n_proof_attempts,
        );

        assert!(
            !is_file_empty(&output_temp_file.to_path_buf()).unwrap(),
            "Output file should not be empty after a run that succeeds on attempt {:?} of proof and verify",
            n_proof_attempts,
        );
    }

    #[test]
    fn test_proof_files_suffixes() {
        // DO NOT CHANGE THESE VALUES UNLESS THEY WERE CHANGED IN ALL THE PLACES THAT CALL THIS
        // BINARY
        let expected_success_suffix: &str = "_success";
        let expected_failure_suffix: &str = "_failure";

        assert_eq!(
            SUCCESS_SUFFIX, expected_success_suffix,
            "The SUCCESS_SUFFIX constant value has changed. This change will break all the places
            that call this binary. Such a change should not happen often, so please make sure it's
            absolutely necessary, and update all the places that call this binary accordingly."
        );
        assert_eq!(
            FAILURE_SUFFIX, expected_failure_suffix,
            "The FAILURE_SUFFIX constant value has changed. This change will break all the places
            that call this binary. Such a change should not happen often, so please make sure it's
            absolutely necessary, and update all the places that call this binary accordingly."
        );
    }
}
