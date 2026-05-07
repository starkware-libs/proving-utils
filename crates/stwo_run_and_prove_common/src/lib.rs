//! Shared abstractions for the `stwo_run_and_prove*` crates. Today this is just the prover
//! trait — an abstraction over the STWO prove call so consumers can mock the slow real prove
//! step in tests. Enable the `mock` feature in `[dev-dependencies]` to get `MockProverTrait`.

use std::path::PathBuf;

use anyhow::Result;
use cairo_air::utils::ProofFormat;
#[cfg(feature = "mock")]
use mockall::automock;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_prover::prover::create_and_serialize_proof;

#[cfg_attr(feature = "mock", automock)]
pub trait ProverTrait {
    fn create_and_serialize_proof(
        &self,
        input: ProverInput,
        verify: bool,
        proof_path: PathBuf,
        proof_format: ProofFormat,
        prover_params_json: Option<PathBuf>,
    ) -> Result<()>;
}

/// Production impl: delegates to `stwo_cairo_prover::prover::create_and_serialize_proof`.
pub struct StwoProverEntryPoint;

impl ProverTrait for StwoProverEntryPoint {
    fn create_and_serialize_proof(
        &self,
        prover_input: ProverInput,
        verify: bool,
        proof_path: PathBuf,
        proof_format: ProofFormat,
        prover_params_json: Option<PathBuf>,
    ) -> Result<()> {
        create_and_serialize_proof(
            prover_input,
            verify,
            proof_path,
            proof_format,
            prover_params_json,
        )
    }
}
