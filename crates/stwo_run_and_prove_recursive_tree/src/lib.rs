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
//! The tree's final reduction is special: its proof is consumed by the Cairo circuit verifier (as
//! the applicative root task), not by another fold, so it is proven with the standard Blake2s
//! Merkle channel and written as the verifier's felt252 arguments stream (internal folds use the
//! M31 channel the multiverifier circuit verifies). A single-leaf tree performs no reduction, so
//! its root proof is the untouched leaf proof.
//!
//! Outputs written for the root layer: the root proof (see above), a flat JSON file with the
//! root node's circuit output values, and a nested `packed_output` JSON tree mirroring the fold —
//! `Composite` verifier nodes carrying their circuit outputs + subtasks down to each leaf's
//! `BootloaderOutput` (its bootloader's hashed output) over a `Plain` node carrying the raw
//! hashed-output preimage — one node per hash layer, for a future unpacker.

use std::path::{Path, PathBuf};

use thiserror::Error;
use tracing::{Level, info, span};

pub mod canonical;
pub mod fold;
pub mod leaf_io;
pub mod output;

pub use leaf_io::{LeafInput, LeafProofExt, load_leaves};
pub use leaf_proof_format::SerializedLeafProof;

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

/// Aggregate statistics for the completed reduction, returned for logging.
#[derive(Debug, Clone, Default)]
pub struct RecursiveTreeStats {
    pub n_leaves: usize,
    pub n_layers: usize,
    pub n_pair_reductions: usize,
}

/// Entry point: folds the entire recursive tree above `leaves` (consumed in order by the layer-0
/// entry list) and writes the three root-layer output files:
/// - `proof_path`: the root proof — the Cairo circuit verifier's felt252 arguments stream for a
///   multi-leaf tree, or the leaf's serialized proof unchanged for a single-leaf tree.
/// - `program_output`: the root node's output values (flat JSON array of `[u32; 4]` QM31 limbs).
/// - `packed_output_path`: the nested `PackedNode` JSON tree.
pub fn stwo_run_and_prove_recursive_tree(
    leaves: Vec<LeafInput>,
    proof_path: &Path,
    program_output: &Path,
    packed_output_path: &Path,
) -> Result<RecursiveTreeStats, RecursiveTreeError> {
    let _span = span!(Level::INFO, "stwo_run_and_prove_recursive_tree").entered();

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
        // A two-entry layer folds into the tree's single root: that final reduction produces the
        // proof the Cairo circuit verifier consumes (see `reduce_pair`).
        let is_root = current_layer.len() == 2;
        let mut next_layer: Vec<LayerEntry> = Vec::with_capacity(current_layer.len().div_ceil(2));
        let mut pairs = current_layer.into_iter();
        let mut pair_idx: usize = 0;
        while let Some(left) = pairs.next() {
            match pairs.next() {
                Some(right) => {
                    let entry =
                        reduce_pair(left, right, layer_idx + 1, pair_idx, &canonical, is_root)?;
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
    output::write_root_outputs(&root, proof_path, program_output, packed_output_path)?;
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
