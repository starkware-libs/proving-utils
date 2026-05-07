//! In-binary recursive proof tree builder.
//!
//! Given an ordered list of `N` leaf STWO proofs and metadata about each leaf, folds the entire
//! recursive proof tree above the leaves in a single binary invocation by repeatedly running the
//! no-builtin-simulation simple bootloader on pairs of children. The output is the single root
//! proof, its program output, its layer fact topology, and a nested CompositePackedOutput JSON
//! structure mirrored from Python's `starkware.cairo.bootloaders.bootloader.objects.PackedOutput`
//! that the on-chain unpacker bootloader needs to split the root proof's flat output back into
//! per-leaf pieces.
//!
//! The constructed tree is balanced: every layer pairs adjacent entries two-to-one, so the tree
//! has depth `ceil(log2(N))` — as opposed to a degenerate chain that folds one leaf at a time
//! (depth `N - 1`). It is not necessarily *complete* in the strict sense: an odd entry at any
//! layer is carried through unchanged to the next layer, attaching one level higher (e.g. for
//! `N = 3` the root verifies the pair-proof of leaves 0,1 alongside leaf 2 itself).
//!
//! The layered reduction is purely sequential: each layer's two-to-one bootloader call consumes
//! the previous layer's proofs as Cairo1Executable user_args.
//!
//! Used by `services.gps.prover_utils.core.stwo_prover.StwoProver` when the parent CairoJob's
//! spec is `StwoInBinaryRecursiveTree` (gated by the `enable_in_binary_recursive_tree` feature
//! flag).

use std::fs;
use std::path::{Path, PathBuf};

use cairo_air::utils::ProofFormat;
use cairo_program_runner_lib::cairo_run_program;
use cairo_program_runner_lib::hints::fact_topologies::{
    FactTopology, write_to_fact_topologies_file,
};
use cairo_program_runner_lib::hints::types::{
    CompositePackedOutput, PackedOutput, felt_decimal_vec,
};
use cairo_program_runner_lib::utils::{
    ProgramInput, get_cairo_run_config, get_program, write_output_to_file,
};
use cairo_vm::Felt252;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use cairo_vm::vm::errors::vm_errors::VirtualMachineError;
use serde::{Deserialize, Serialize};
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_adapter::adapter::adapt;
pub use stwo_run_and_prove_common::{ProverTrait, StwoProverEntryPoint};
use tempfile::TempDir;
use thiserror::Error;
use tracing::{Level, info, span};

#[derive(Debug, Error)]
pub enum RecursiveTreeError {
    #[error("Empty leaves list; expected at least one leaf entry.")]
    EmptyLeaves,
    #[error("IO error on file '{1:?}': {0}")]
    PathIO(std::io::Error, PathBuf),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error("Failed to (de)serialize JSON: {0}")]
    Serde(#[from] serde_json::Error),
    #[error(transparent)]
    SonicSerialize(#[from] sonic_rs::error::Error),
    #[error("Cairo program error on file '{1:?}': {0}")]
    Program(ProgramError, PathBuf),
    #[error(transparent)]
    CairoRun(Box<CairoRunError>),
    #[error(transparent)]
    Runner(#[from] RunnerError),
    #[error(transparent)]
    VM(#[from] VirtualMachineError),
    #[error(transparent)]
    Anyhow(#[from] anyhow::Error),
}

impl From<CairoRunError> for RecursiveTreeError {
    fn from(err: CairoRunError) -> Self {
        RecursiveTreeError::CairoRun(Box::new(err))
    }
}

/// One leaf entry as written by Python (`StwoProver._create_files_dict_for_recursive_tree`).
/// Fields mirror the per-leaf data the per-pair flow would have looked up from storage
/// (TrainProved.proof, TrainProved.flatten_task_outputs, the leaf's recursive_data).
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct LeafInput {
    /// Leaf train id; carried for logs so the binary's output can be cross-referenced against
    /// the Python pipeline when something fails mid-reduction.
    pub train_id: u64,
    /// Path to the leaf's decompressed STWO proof JSON (the cairo-serde format the verifier
    /// expects as `user_args_file`).
    pub proof_path: PathBuf,
    /// Hash function the simple bootloader should use when hashing the verified program.
    /// One of "pedersen", "poseidon", "blake". (Currently `verifier_task_for_child` hardcodes
    /// `"blake"` matching Python's `get_recursive_program_hash_function()`; this field is
    /// reserved for the day that contract is parameterized.)
    pub program_hash_function: String,
    /// The leaf's PackedOutput structure as computed by Python via
    /// `packed_output_from_data(create_recursive_data(leaf_train_info))`. For non-recursive
    /// leaves this is a `Composite { outputs, [Plain], [fact_topology] }` — the single-task
    /// simple-bootloader wrap representing the leaf's own proof. For recursive leaves it's
    /// the full nested Composite tree describing the leaf's own aggregation. The Rust binary
    /// propagates this verbatim as the LayerEntry's `packed_output` so that the resulting
    /// root `PackedOutput` matches what the per-pair flow would have produced.
    /// Also the sole source for this leaf's `outputs` and per-task `fact_topologies` at the
    /// initial `LayerEntry` — they're read from `composite.outputs` and
    /// `composite.fact_topologies`.
    pub packed_output: PackedOutput,
    /// Per-leaf stats pre-computed by Python.
    /// For non-recursive leaves these equal the raw fact-topology values; for recursive leaves
    /// Python reads the cumulative totals from `CairoJobReceived` (which already aggregated the
    /// entire sub-tree).
    #[serde(flatten)]
    pub counters: RecursiveJobCounters,
}

/// Aggregate counters carried per tree node during the reduction. Used both as the per-leaf
/// input stats (in `LeafInput`) and as the aggregated state on each `LayerEntry` /
/// `RecursiveJobData`. Same shape, two contexts — pre-aggregation vs running totals. Flattened
/// into the JSON wire format on both sides so Python sees the same flat keys it always did.
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
pub struct RecursiveJobCounters {
    pub n_non_recursive_jobs: u64,
    pub total_non_recursive_output_size: u64,
    pub total_n_pages: u64,
    pub total_fact_tree_structures_len: u64,
}

/// Aggregated counters mirrored from Python's
/// `services.gps.objects.recursive_job.RecursiveJobData`. Kept in sync as we walk up the tree so
/// that the root entry's `RecursiveJobData` is the correct sum across all leaves underneath it.
#[derive(Debug, Clone, Default, Serialize)]
pub struct RecursiveJobData {
    /// Bootloader output of the layer this `RecursiveJobData` is attached to (per Python's
    /// invariant). Populated with the leaf's outputs at layer 0 and with each pair-bootloader's
    /// output at higher layers.
    #[serde(serialize_with = "felt_decimal_vec::serialize")]
    pub outputs: Vec<Felt252>,
    #[serde(flatten)]
    pub counters: RecursiveJobCounters,
}

impl RecursiveJobData {
    /// Per-leaf seed using the stats pre-computed by Python and embedded in `LeafInput`.
    /// `outputs` are passed separately because they live on the leaf's `packed_output` rather
    /// than on `LeafInput` directly (single source of truth — see `LeafInput.packed_output`).
    fn from_leaf(leaf: &LeafInput, outputs: Vec<Felt252>) -> Self {
        Self {
            outputs,
            counters: leaf.counters.clone(),
        }
    }

    /// Aggregates two children's counters when reducing them under a new parent layer node.
    fn combine(left: &Self, right: &Self, new_outputs: Vec<Felt252>) -> Self {
        Self {
            outputs: new_outputs,
            counters: RecursiveJobCounters {
                n_non_recursive_jobs: left.counters.n_non_recursive_jobs
                    + right.counters.n_non_recursive_jobs,
                total_non_recursive_output_size: left.counters.total_non_recursive_output_size
                    + right.counters.total_non_recursive_output_size,
                total_n_pages: left.counters.total_n_pages + right.counters.total_n_pages,
                total_fact_tree_structures_len: left.counters.total_fact_tree_structures_len
                    + right.counters.total_fact_tree_structures_len,
            },
        }
    }
}

/// In-memory representation of a single tree node during reduction. At layer 0 these wrap the
/// leaves; at higher layers each entry is the result of folding two children.
struct LayerEntry {
    proof_path: PathBuf,
    /// The fact_topologies that would be written to disk for Python's
    /// `TrainProved.fact_topologies` if this entry ends up as the root — i.e. exactly what
    /// `stwo_run_and_prove` (single-shot) would have produced for this proof. For an internal
    /// node these are the per-task entries the bootloader wrote during this layer's
    /// `reduce_pair` (one per verifier task; 2 for our 2-task pair). For a leaf they're a
    /// single-element vector with the leaf's own fact_topology, handling the single-leaf-input
    /// edge case where no `reduce_pair` ever runs.
    fact_topologies: Vec<FactTopology>,
    outputs: Vec<Felt252>,
    recursive_job_data: RecursiveJobData,
    packed_output: PackedOutput,
}

/// CLI/file-level configuration for one invocation of the recursive-tree binary.
pub struct RecursiveTreeConfig {
    /// Ordered list of leaves to fold; consumed in this order by the layer-0 entry list.
    pub leaves: Vec<LeafInput>,
    /// Path to the verifier program (e.g. stwo_full_cairo_verifier_with_blake_packing) that
    /// each pair-bootloader's two Cairo1Executable tasks invoke.
    pub verifier_program: PathBuf,
    /// Path to the simple-bootloader program used at every layer. Python passes
    /// `NO_BUILTIN_SIMULATION_SIMPLE_BOOTLOADER_COMPILED_PATH` here for the offchain
    /// recursive-tree job.
    pub bootloader_program: PathBuf,
    pub prover_params_json: Option<PathBuf>,
    pub proof_format: ProofFormat,
    /// If true, verify each layer's proof immediately after generation (matches
    /// `stwo_run_and_prove`'s `--verify` flag).
    pub verify: bool,
    /// Output paths for the root layer:
    pub proof_path: PathBuf,
    pub program_output: PathBuf,
    /// JSON file in `FactTopologyFile` format containing the single root-layer fact topology.
    /// Read by Python (`StwoProver._cairo_prove_recursive_tree`) as
    /// `train_proved.fact_topologies`.
    pub fact_topologies_path: PathBuf,
    /// JSON file containing the nested `PackedOutput` for the on-chain unpacker.
    pub packed_output_path: PathBuf,
    /// Accepted for CLI compatibility with the Python caller (`get_stwo_prover_command` passes
    /// `--debug_data_dir` always and `--save_debug_data` on retry attempts), but currently
    /// inert: per-pair prover-input dumping was dropped to keep peak memory down. Reintroduce
    /// behind these knobs if per-layer debug artifacts become necessary.
    pub save_debug_data: bool,
    pub debug_data_dir: Option<PathBuf>,
}

/// Entry point: folds the entire recursive tree above the configured leaves and writes the four
/// root-layer output files. Returns the aggregated `RecursiveJobData` for the root, useful for
/// logging.
pub fn stwo_run_and_prove_recursive_tree(
    config: RecursiveTreeConfig,
    prover: &dyn ProverTrait,
) -> Result<RecursiveJobData, RecursiveTreeError> {
    let _span = span!(Level::INFO, "stwo_run_and_prove_recursive_tree").entered();
    let RecursiveTreeConfig {
        leaves,
        verifier_program,
        bootloader_program,
        prover_params_json,
        proof_format,
        verify,
        proof_path,
        program_output,
        fact_topologies_path,
        packed_output_path,
        save_debug_data: _,
        debug_data_dir: _,
    } = config;

    if leaves.is_empty() {
        return Err(RecursiveTreeError::EmptyLeaves);
    }
    info!(
        n_leaves = leaves.len(),
        leaf_train_ids = ?leaves.iter().map(|leaf| leaf.train_id).collect::<Vec<_>>(),
        "Folding leaves into recursive tree.",
    );

    // Per-invocation scratch space for intermediate proofs and bootloader fact-topology dumps.
    // Dropped (and removed from disk) when this function returns; the only files that outlive
    // the invocation are the four root-layer outputs the caller asked for.
    let scratch = TempDir::new()?;

    let verifier_program_arc = std::sync::Arc::new(verifier_program);
    let bootloader_program_arc = std::sync::Arc::new(bootloader_program);

    let mut current_layer: Vec<LayerEntry> = leaves
        .into_iter()
        .map(|leaf| {
            // The leaf's `outputs` and `fact_topologies` live on `leaf.packed_output` (the
            // Composite Python builds via `packed_output_from_data`). Pull them from there to
            // keep a single source of truth — the alternative would be Python-side fields that
            // duplicate the same values.
            let (leaf_outputs, leaf_fact_topologies) = match &leaf.packed_output {
                PackedOutput::Composite(c) => (c.outputs.clone(), c.fact_topologies.clone()),
                PackedOutput::Plain => {
                    return Err(RecursiveTreeError::Anyhow(anyhow::anyhow!(
                        "Expected Composite packed_output for leaf train_id={}; got Plain. \
                         Python should always pass a Composite wrap via \
                         packed_output_from_data(create_recursive_data(...)).",
                        leaf.train_id
                    )));
                }
            };
            Ok(LayerEntry {
                proof_path: leaf.proof_path.clone(),
                fact_topologies: leaf_fact_topologies,
                recursive_job_data: RecursiveJobData::from_leaf(&leaf, leaf_outputs.clone()),
                outputs: leaf_outputs,
                packed_output: leaf.packed_output.clone(),
            })
        })
        .collect::<Result<Vec<_>, RecursiveTreeError>>()?;

    let mut layer_idx: usize = 0;
    while current_layer.len() > 1 {
        info!(
            layer_idx,
            n_entries = current_layer.len(),
            "Reducing recursive-tree layer."
        );
        let mut next_layer: Vec<LayerEntry> = Vec::with_capacity(current_layer.len().div_ceil(2));
        let mut pairs = current_layer.into_iter();
        let mut pair_idx: usize = 0;
        while let Some(left) = pairs.next() {
            match pairs.next() {
                Some(right) => {
                    let entry = reduce_pair(
                        &left,
                        &right,
                        layer_idx + 1,
                        pair_idx,
                        scratch.path(),
                        verifier_program_arc.as_ref(),
                        bootloader_program_arc.as_ref(),
                        prover_params_json.as_ref(),
                        proof_format.clone(),
                        verify,
                        prover,
                    )?;
                    next_layer.push(entry);
                }
                None => {
                    // Odd carry: pass the unpaired entry through to the next layer unchanged.
                    info!(
                        layer_idx,
                        pair_idx, "Carrying unpaired entry to next layer."
                    );
                    next_layer.push(left);
                }
            }
            pair_idx += 1;
        }
        current_layer = next_layer;
        layer_idx += 1;
    }

    let root = current_layer.pop().expect(
        "reduction loop terminates only when current_layer.len() == 1, so the final layer must \
         contain exactly one root entry",
    );
    write_root_outputs(
        &root,
        &proof_path,
        &program_output,
        &fact_topologies_path,
        &packed_output_path,
    )?;
    Ok(root.recursive_job_data)
}

/// Folds two children into a new parent entry by running the simple bootloader on a 2-task
/// `SimpleBootloaderInput` (each task verifies one child's proof).
#[allow(clippy::too_many_arguments)]
fn reduce_pair(
    left: &LayerEntry,
    right: &LayerEntry,
    layer_idx: usize,
    pair_idx: usize,
    scratch_dir: &std::path::Path,
    verifier_program: &PathBuf,
    bootloader_program: &Path,
    prover_params_json: Option<&PathBuf>,
    proof_format: ProofFormat,
    verify: bool,
    prover: &dyn ProverTrait,
) -> Result<LayerEntry, RecursiveTreeError> {
    let _span = span!(Level::INFO, "reduce_pair", layer_idx, pair_idx).entered();

    let pair_dir = scratch_dir.join(format!("layer_{layer_idx:03}_pair_{pair_idx:03}"));
    fs::create_dir_all(&pair_dir)?;
    let bootloader_input_path = pair_dir.join("simple_bootloader_input.json");
    let fact_topologies_dump_path = pair_dir.join("fact_topologies.json");
    let proof_output_path = pair_dir.join("proof");
    let program_output_path = pair_dir.join("program_output");

    // SimpleBootloaderInput written here is shape-compatible with what
    // `services.gps.utils.cairo_run_bootloader_utils.get_bootloader_input` produces for an inner
    // recursive train (single_page=true; two Cairo1Executable verifier tasks).
    let bootloader_input_json = serde_json::json!({
        "fact_topologies_path": fact_topologies_dump_path,
        "single_page": true,
        "tasks": [
            verifier_task_for_child(verifier_program, &left.proof_path, layer_idx, pair_idx, "left"),
            verifier_task_for_child(verifier_program, &right.proof_path, layer_idx, pair_idx, "right"),
        ],
    });
    fs::write(
        &bootloader_input_path,
        serde_json::to_string(&bootloader_input_json)?,
    )?;

    let cairo_run_config = get_cairo_run_config(
        // We don't use dynamic layout in stwo.
        &None,
        LayoutName::all_cairo_stwo,
        true,
        // In stwo, when proof_mode==true, trace padding is redundant work.
        true,
        // We allow missing builtins because all_cairo_stwo doesn't include all builtins, and
        // the bootloader will simulate the missing builtins.
        true,
        // We don't need to relocate memory in the VM because we later call the adapter that does
        // relocation.
        false,
    )?;
    let program = get_program(bootloader_program)
        .map_err(|e| RecursiveTreeError::Program(e, bootloader_program.to_path_buf()))?;
    let mut runner = cairo_run_program(
        &program,
        Some(ProgramInput::Path(bootloader_input_path)),
        cairo_run_config,
        None,
    )?;

    write_output_to_file(&mut runner, program_output_path.clone())?;
    let outputs = read_outputs_file(&program_output_path)?;

    let prover_input: ProverInput = adapt(&runner)?;
    // The runner holds the full VM memory + execution trace; everything we still need has been
    // extracted into `prover_input`, so release it before proving to keep peak memory to a
    // single copy of the execution data.
    drop(runner);

    prover.create_and_serialize_proof(
        prover_input,
        verify,
        proof_output_path.clone(),
        proof_format,
        prover_params_json.cloned(),
    )?;

    // The simple-bootloader hint writes one fact_topology per task it ran — here, one per
    // verifier task. These are the authoritative recording of each child's verifier-task output
    // layout (whatever the verifier produced, including any pages it declared via
    // `gps_fact_topology`), and we feed them straight into `CompositePackedOutput.fact_topologies`
    // below. The 2-task contract is asserted as a sanity check on the bootloader run.
    let task_fact_topologies = read_fact_topologies_file(&fact_topologies_dump_path)?;
    if task_fact_topologies.len() != 2 {
        return Err(RecursiveTreeError::Anyhow(anyhow::anyhow!(
            "Expected exactly two fact topologies from a 2-task simple bootloader run \
             (one per child verifier task), got {}.",
            task_fact_topologies.len()
        )));
    }

    let recursive_job_data = RecursiveJobData::combine(
        &left.recursive_job_data,
        &right.recursive_job_data,
        outputs.clone(),
    );
    let packed_output = PackedOutput::Composite(CompositePackedOutput {
        outputs: outputs.clone(),
        subtasks: vec![left.packed_output.clone(), right.packed_output.clone()],
        fact_topologies: task_fact_topologies.clone(),
    });
    Ok(LayerEntry {
        proof_path: proof_output_path,
        fact_topologies: task_fact_topologies,
        outputs,
        recursive_job_data,
        packed_output,
    })
}

/// Builds the per-child Cairo1Executable JSON entry consumed by `TaskSpec`'s deserializer.
fn verifier_task_for_child(
    verifier_program: &PathBuf,
    proof_path: &PathBuf,
    layer_idx: usize,
    pair_idx: usize,
    side_label: &str,
) -> serde_json::Value {
    let _span = span!(
        Level::DEBUG,
        "verifier_task_for_child",
        layer_idx,
        pair_idx,
        side_label
    )
    .entered();
    serde_json::json!({
        "type": "Cairo1Executable",
        "path": verifier_program,
        "user_args_file": proof_path,
        // Recursive jobs always use blake for the program hash; matches Python's
        // `get_recursive_program_hash_function()`.
        "program_hash_function": "blake",
    })
}

/// Reads a `program_output` JSON file (a flat array of hex-encoded `Felt252` strings, exactly
/// the shape `write_output_to_file` produces) and parses each entry back into a `Felt252`.
fn read_outputs_file(path: &PathBuf) -> Result<Vec<Felt252>, RecursiveTreeError> {
    let content = fs::read_to_string(path)?;
    let hex_strings: Vec<String> = serde_json::from_str(&content)?;
    hex_strings
        .into_iter()
        .map(|hex_str| {
            // The bootloader writer (`write_output_to_file`) uses cairo-vm's default Felt252
            // serialization, which already emits a hex-prefixed (or unprefixed hex) string.
            Felt252::from_hex(&hex_str).map_err(|_| {
                RecursiveTreeError::Anyhow(anyhow::anyhow!(
                    "Failed to parse program-output entry as a Felt252 hex string: {hex_str:?}",
                ))
            })
        })
        .collect()
}

/// Reads the `fact_topologies.json` dump produced by the simple bootloader (shape:
/// `{"fact_topologies": [FactTopology, ...]}`, one entry per executed task) and returns the
/// inner list.
fn read_fact_topologies_file(path: &PathBuf) -> Result<Vec<FactTopology>, RecursiveTreeError> {
    #[derive(Deserialize)]
    struct FactTopologiesFile {
        fact_topologies: Vec<FactTopology>,
    }
    let content = fs::read_to_string(path)?;
    let file: FactTopologiesFile = serde_json::from_str(&content)?;
    Ok(file.fact_topologies)
}

/// Writes the four root-layer output files to the caller-configured paths: copies the root
/// proof out of the scratch dir, dumps the root `outputs` as a JSON array of hex strings (mirrors
/// `stwo_run_and_prove --program_output`), persists the root `fact_topologies` via the standard
/// `FactTopologiesFile` writer, and serializes the nested `PackedOutput` tree as JSON. This is
/// the binary's only side-effect on disk outside the scratch dir.
fn write_root_outputs(
    root: &LayerEntry,
    proof_path: &PathBuf,
    program_output: &PathBuf,
    fact_topologies_path: &Path,
    packed_output_path: &PathBuf,
) -> Result<(), RecursiveTreeError> {
    fs::copy(&root.proof_path, proof_path)
        .map_err(|e| RecursiveTreeError::PathIO(e, proof_path.clone()))?;
    let outputs_hex: Vec<String> = root.outputs.iter().map(|f| f.to_hex_string()).collect();
    fs::write(program_output, sonic_rs::to_string(&outputs_hex)?)
        .map_err(|e| RecursiveTreeError::PathIO(e, program_output.clone()))?;
    write_to_fact_topologies_file(fact_topologies_path, &root.fact_topologies)
        .map_err(|e| RecursiveTreeError::Anyhow(anyhow::anyhow!("{e}")))?;
    fs::write(
        packed_output_path,
        serde_json::to_string(&root.packed_output)?,
    )
    .map_err(|e| RecursiveTreeError::PathIO(e, packed_output_path.clone()))?;
    Ok(())
}

#[cfg(test)]
mod tests;
