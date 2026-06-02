//! Circuit-DSL unpacker for a perfect-binary-tree recursion of stwo-circuits proofs.
//!
//! # What this crate does
//!
//! It is the circuits-DSL analogue of the Cairo unpacker bootloader
//! (`starkware/.../bootloader/run_bootloader.cairo`, `BLAKE_UNPACKING` mode). Where the Cairo
//! bootloader walks task outputs at runtime via `[size, program_hash, ...]` headers, this
//! crate's [`run_unpacker`] walks a *statically-shaped* tree of [`circuit_verifier`] proofs and
//! emits each real leaf's outputs to the caller (typically an aggregator circuit).
//!
//! # Tree shape
//!
//! The tree is a **complete perfect binary tree** of `N_total = next_power_of_2(N)` slots, where
//! `N` is the number of *real* leaves the caller provides via [`UnpackerHints::leaf_outputs`]. The
//! last `N_total - N` slots are *dummy* leaves with a canonical empty output (see
//! [`DUMMY_LEAF_OUTPUT`]). Tree height is `log2(N_total)`. Every internal node has exactly two
//! children.
//!
//! Because the shape is fully determined by `N`, this crate does *not* embed `n_subtasks` / `size`
//! headers in the preimage of each node (which the Cairo unpacker requires for runtime walking).
//! Every preimage is the minimal data needed for the Blake binding:
//!
//! ```text
//!   internal node preimage:  [ h_L.0, h_L.1, h_R.0, h_R.1 ]      (4 QM31s)
//!   leaf preimage:           [ ...leaf_output ]                  (k_i QM31s)
//! ```
//!
//! # Hash binding
//!
//! At every node, the unpacker emits a Blake binding that matches the construction in
//! [`circuit_verifier::verify`] exactly:
//!
//! ```text
//!   computed = blake( pp_root.0 || pp_root.1 || ...preimage )
//!   assert computed == node_hash
//! ```
//!
//! The `node_hash` for the root is supplied by the caller (it is the verifier output emitted by
//! the top-level [`circuit_verifier`] proof). The `node_hash` for an internal node is itself a
//! pair of `Var`s extracted from its parent's preimage at the recursion's known offsets. The
//! `node_hash` for a real leaf is computed in the same way (its hash is what the parent's
//! preimage embeds).
//!
//! # Dummy leaves
//!
//! Dummies are pinned to known constants throughout: [`DUMMY_LEAF_OUTPUT`] is a 1-QM31 marker
//! `0xDEAD`. The hash of each "all-dummy subtree at depth d" is precomputed off-circuit and
//! pinned in-circuit with `Eq` gates — there is no recursion into
//! dummy subtrees and no Blake gate spent on them. Mixed subtrees (one real child, one dummy)
//! recurse only on the real side.
//!
//! Dummy leaves are *not* emitted in the unpacker's output: the returned `Vec<Vec<Var>>` has
//! exactly `N` entries (one per real leaf, in tree position order).
//!
//! # Inputs the unpacker does *not* take
//!
//! - It does **not** take the leaf STWO proofs or compose `build_verification_circuit` itself. The
//!   caller is responsible for already having verified each leaf and producing its `output_hash` (2
//!   QM31 wires). For the top-level [`run_unpacker`] call only the root's hash is passed in;
//!   intermediate leaf hashes are extracted from preimages during recursion.
//! - It does **not** take a per-task `program_hash`: the verifier's `output_hash` already commits
//!   to the inner circuit's `preprocessed_root` (via the verifier's hash construction).
//!
//! # Relation to the Cairo unpacker
//!
//! Both serve the same role — turn an opaque verifier output hash + a prover-supplied preimage
//! hint into the actual outputs, via a Blake hash binding. Differences:
//!
//! | Aspect                          | Cairo unpacker (`bootloader.cairo`) | This crate                                  |
//! |---------------------------------|--------------------------------------|---------------------------------------------|
//! | Value type                      | `felt252`                            | `QM31`                                      |
//! | Tree shape                      | Free (per-call, runtime-walked)      | Complete perfect binary, fixed by `N`       |
//! | Layout headers in preimage      | `[n_subtasks, size, program_hash]`   | None (positions are compile-time-known)     |
//! | Walking                         | Dynamic (size headers in preimage)   | Static (offsets known from `N` and `k_i`)   |
//! | Dummies                         | Not applicable                       | Right-aligned, precomputed-constant hashes  |

#[cfg(test)]
mod tests;

use circuits::blake::HashValue;
use circuits::context::{Context, Var};
use circuits::ivalue::{IValue, qm31_from_u32s};
use stwo::core::fields::qm31::QM31;

/// Marker value for an unused (dummy) leaf slot.
///
/// Padding required to round `N` up to `next_power_of_2(N)`. A dummy leaf's output is a single
/// QM31 holding `0xDEAD` in the first M31 limb. The exact value is soundness-irrelevant — it just
/// has to be a deterministic constant that the unpacker can pin via [`Eq`](circuits::ops::eq).
///
/// Reading `0xDEAD` in a debug dump of a recursive proof's leaves identifies a padded slot.
pub const DUMMY_LEAF_MARKER: u32 = 0xDEAD;

/// The full dummy leaf output: a single-QM31 sequence carrying the marker.
pub fn dummy_leaf_output() -> Vec<QM31> {
    vec![qm31_from_u32s(DUMMY_LEAF_MARKER, 0, 0, 0)]
}

/// Prover-supplied hints required to unpack the recursion.
///
/// Carries one entry per **real** leaf, in tree position order. The unpacker derives every other
/// piece of structural information (tree height, dummy positions, internal-node preimages,
/// per-level dummy hash constants) from `leaf_outputs.len()` alone.
///
/// Each `leaf_outputs[i]` is the i-th leaf's output as the inner STWO-proven circuit emitted it
/// (i.e., `output_values` minus the trailing `u` value the verifier convention drops). Length
/// `k_i` is allowed to vary across leaves.
#[derive(Debug, Clone)]
pub struct UnpackerHints {
    /// Per-leaf output values. Length = number of real leaves.
    pub leaf_outputs: Vec<Vec<QM31>>,
}

impl UnpackerHints {
    /// Returns the number of real leaves, `N`.
    pub fn n_real_leaves(&self) -> usize {
        self.leaf_outputs.len()
    }

    /// Returns the number of slots in the perfect binary tree, `N_total = next_power_of_2(N)`.
    pub fn n_total_leaves(&self) -> usize {
        self.n_real_leaves().next_power_of_two().max(1)
    }

    /// Returns the tree height (depth of the root above the leaves). 0 for a single-leaf tree.
    pub fn tree_height(&self) -> u32 {
        self.n_total_leaves().trailing_zeros()
    }

    /// Returns the number of dummy leaves padding the tree to a power of two.
    pub fn n_dummy_leaves(&self) -> usize {
        self.n_total_leaves() - self.n_real_leaves()
    }
}

/// Top-level unpacker entry point.
///
/// # Arguments
///
/// * `ctx` — circuits-DSL build context. `Value` is typically `QM31` (witness-carrying build, the
///   resulting context can validate via `is_circuit_valid()`) or `NoValue` (topology-only).
/// * `root_hash` — the 2-QM31 hash digest emitted by the top-level [`circuit_verifier`] proof.
///   Bound to the rest of the recursion via the Blake construction above.
/// * `preprocessed_root` — `preprocessed_root` of the underlying AIR. Identical at every internal
///   node (recursive-tree case: same verifier AIR at every layer).
/// * `hints` — prover-supplied preimage hints. See [`UnpackerHints`].
///
/// # Returns
///
/// One inner `Vec<Var>` per real leaf, in tree position order. Inner length is the leaf's `k_i`.
/// Dummy leaves are not represented in the output.
///
/// # Soundness contract
///
/// On `ctx.is_circuit_valid()` returning `Ok`, the returned `Vec<Vec<Var>>` is guaranteed to
/// equal the actual outputs the STWO-proven leaf circuits emitted, chained back to `root_hash`
/// via a continuous Blake hash binding. The prover cannot supply differing
/// `hints.leaf_outputs` without falsifying one of the Blake assertions.
///
/// Dummy positions are pinned to precomputed constants via `Eq` gates and cannot be
/// substituted by the prover for real (potentially-malicious) subtrees.
pub fn run_unpacker<Value: IValue>(
    _ctx: &mut Context<Value>,
    _root_hash: HashValue<Var>,
    _preprocessed_root: HashValue<Var>,
    _hints: &UnpackerHints,
) -> Vec<Vec<Var>> {
    // TODO: implement the Blake-binding tree walk. Returns one `Vec<Var>` per real leaf, in tree
    // position order.
    Vec::new()
}
