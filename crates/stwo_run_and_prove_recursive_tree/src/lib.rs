//! In-binary recursive **circuit**-proof tree builder.
//!
//! Given an ordered list of `N` leaf circuit proofs (produced by the `leaf_prover` crate — each one
//! is a circuit proof that a Cairo proof was verified by the cairo-verifier circuit), this folds
//! the entire recursive proof tree above the leaves in a single binary invocation by repeatedly
//! pairing adjacent children with the `circuit_multiverifier`: for each pair it builds a
//! multiverifier circuit that verifies both children, proves that circuit, and the resulting
//! circuit proof becomes the parent node for the next layer. There is no Cairo bootloader and no
//! wrapping step anymore.
//!
//! The constructed tree is balanced: every layer pairs adjacent entries two-to-one, so the tree has
//! depth `ceil(log2(N))`. An odd entry at any layer is carried through unchanged to the next layer
//! (attaching one level higher). Carrying works because, thanks to the common padding target, every
//! proof in the tree — leaf or internal — has the exact same circuit shape and is therefore
//! verifiable by the same multiverifier circuit (see [`canonical`]).
//!
//! Outputs written for the root layer: the serialized root circuit proof, a flat JSON file with the
//! root node's circuit output values, and a nested `packed_output` JSON tree mirroring the fold —
//! `Composite` verifier nodes carrying their circuit outputs + subtasks down to per-leaf `Plain`
//! nodes carrying each leaf's Cairo program output — for a future unpacker.

use std::path::PathBuf;

use thiserror::Error;
use tracing::{Level, info, span};

pub mod canonical;
pub mod fold;
pub mod leaf_io;
pub mod output;

pub use leaf_io::{LeafInput, load_leaves};

use canonical::CanonicalCircuit;
use fold::{LayerEntry, reduce_pair};

#[derive(Debug, Error)]
pub enum RecursiveTreeError {
    #[error("Empty leaves list; expected at least one leaf entry.")]
    EmptyLeaves,
    #[error("IO error on file '{1:?}': {0}")]
    PathIO(std::io::Error, PathBuf),
    #[error("Failed to (de)serialize JSON: {0}")]
    Serde(#[from] serde_json::Error),
    #[error(transparent)]
    SonicSerialize(#[from] sonic_rs::error::Error),
    #[error("Failed to deserialize a circuit proof: {0}")]
    Deserialize(String),
    #[error("Circuit proving failed: {0}")]
    Proving(String),
    #[error("Expected {expected} output values from a circuit proof, got {got}.")]
    BadOutputArity { expected: usize, got: usize },
    #[error(
        "Padding parity broken: the leaf and multiverifier circuits do not share the same \
         preprocessed-trace layout (column log sizes / trace_log_size). TARGET_PADDING_SIZES is \
         likely inconsistent with the circuit configuration."
    )]
    PaddingParity,
    #[error("Could not parse leaf circuit output values: {reason}")]
    BadLeafOutputs { reason: String },
}

/// File-level configuration for one invocation of the recursive-tree binary.
pub struct RecursiveTreeConfig {
    /// Ordered list of leaves to fold; consumed in this order by the layer-0 entry list.
    pub leaves: Vec<LeafInput>,
    /// Output path for the serialized root circuit proof.
    pub proof_path: PathBuf,
    /// Output path for the root node's output values (flat JSON array of `[u32; 4]` QM31 limbs).
    pub program_output: PathBuf,
    /// Output path for the nested `PackedNode` JSON tree.
    pub packed_output_path: PathBuf,
}

/// Aggregate statistics for the completed reduction, returned for logging.
#[derive(Debug, Clone, Default)]
pub struct RecursiveTreeStats {
    pub n_leaves: usize,
    pub n_layers: usize,
    pub n_pair_reductions: usize,
}

/// Entry point: folds the entire recursive tree above the configured leaves and writes the three
/// root-layer output files.
pub fn stwo_run_and_prove_recursive_tree(
    config: RecursiveTreeConfig,
) -> Result<RecursiveTreeStats, RecursiveTreeError> {
    let _span = span!(Level::INFO, "stwo_run_and_prove_recursive_tree").entered();
    let RecursiveTreeConfig {
        leaves,
        proof_path,
        program_output,
        packed_output_path,
    } = config;

    if leaves.is_empty() {
        return Err(RecursiveTreeError::EmptyLeaves);
    }
    let n_leaves = leaves.len();
    info!(
        n_leaves,
        "Folding leaf circuit proofs into a recursive tree."
    );

    let canonical = CanonicalCircuit::build()?;

    // Intermediate proofs live in memory (on each `LayerEntry`) for the duration of the fold; the
    // only files this invocation writes are the root outputs.
    let mut current_layer: Vec<LayerEntry> = leaves
        .iter()
        .map(LayerEntry::from_leaf)
        .collect::<Result<Vec<_>, _>>()?;

    let mut stats = RecursiveTreeStats {
        n_leaves,
        n_layers: 0,
        n_pair_reductions: 0,
    };

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
                    let entry = reduce_pair(left, right, layer_idx + 1, pair_idx, &canonical)?;
                    next_layer.push(entry);
                    stats.n_pair_reductions += 1;
                }
                None => {
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
    stats.n_layers = layer_idx;

    let root = current_layer.pop().expect(
        "reduction loop terminates only when current_layer.len() == 1, so the final layer must \
         contain exactly one root entry",
    );
    output::write_root_outputs(&root, &proof_path, &program_output, &packed_output_path)?;
    info!(
        n_layers = stats.n_layers,
        n_pair_reductions = stats.n_pair_reductions,
        "Recursive tree reduction complete."
    );
    Ok(stats)
}

/// Pure mirror of the fold loop's shape: given `n_leaves`, returns `(n_layers, n_pair_reductions)`.
/// A balanced two-to-one tree with an odd entry carried up has depth `ceil(log2(n))` and exactly
/// `n - 1` pair reductions. Kept in sync with the loop in [`stwo_run_and_prove_recursive_tree`] and
/// exercised by the unit tests.
pub fn fold_plan(n_leaves: usize) -> (usize, usize) {
    let mut count = n_leaves;
    let mut layers = 0;
    let mut pair_reductions = 0;
    while count > 1 {
        pair_reductions += count / 2;
        count = count.div_ceil(2);
        layers += 1;
    }
    (layers, pair_reductions)
}

#[cfg(test)]
mod tests;
