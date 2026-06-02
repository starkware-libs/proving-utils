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
//! [`dummy_leaf_output`]). Tree height is `log2(N_total)`. Every internal node has exactly two
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
//! When `N` is not a power of two, slots `N..N_total` are *dummies* with the canonical output
//! [`dummy_leaf_output()`] — a single-QM31 sequence carrying the marker `0xDEAD`
//! ([`DUMMY_LEAF_MARKER`]).
//!
//! Because dummies' outputs are fixed, every *fully-dummy* subtree has a hash that depends only
//! on `pp_root` and depth — not on `N`. The unpacker precomputes the chain
//! `dummy_hash[d]` for `d ∈ 0..=tree_height` **off-circuit** (one `QM31::blake` per depth) and
//! wires the result as `ctx.constant`s. During the recursive walk, when a subtree is determined
//! statically to be fully-dummy (its leaf range starts at or after `N`), the unpacker returns
//! the cached constant directly — **no Blake gate is emitted on the dummy side**, no recursion
//! happens, and no `Var`s are guessed for dummy outputs. Mixed subtrees (one real child, one
//! dummy) recurse only on the real side and combine with the cached dummy constant under one
//! Blake gate.
//!
//! Soundness: the dummy constants are bound by being included in the root's preimage at fixed
//! positions; any prover-supplied substitution would change the root Blake hash and falsify the
//! `eq` check against `root_hash`.
//!
//! Dummy leaves are *not* emitted in the unpacker's output: the returned `Vec<Vec<Var>>` has
//! exactly `N` entries (one per real leaf, in tree position order). The internal padding is
//! invisible to the caller.
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
//! | Dummies                         | Not applicable                       | Right-aligned, off-circuit-precomputed hashes short-circuit fully-dummy subtrees |

#[cfg(test)]
mod tests;

use circuits::blake::{HashValue, blake};
use circuits::context::{Context, Var};
use circuits::ivalue::{IValue, qm31_from_u32s};
use circuits::ops::{eq, guess};
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
/// Dummy slots carry [`dummy_leaf_output()`] — a deterministic constant. The hash of every
/// fully-dummy subtree is precomputed off-circuit (via [`precompute_dummy_hashes`]) and wired
/// in-circuit as `ctx.constant`s, so the recursion **short-circuits** at all-dummy subtrees: no
/// Blake gate is emitted there. Any prover-supplied substitution for a dummy slot would change
/// the root Blake hash and falsify the binding.
pub fn run_unpacker<Value: IValue>(
    ctx: &mut Context<Value>,
    root_hash: HashValue<Var>,
    preprocessed_root: HashValue<QM31>,
    hints: &UnpackerHints,
) -> Vec<Vec<Var>> {
    let n_real = hints.n_real_leaves();
    let n_total = hints.n_total_leaves();
    let tree_height = hints.tree_height() as usize;

    // Wire pp_root as constant Vars so the in-circuit recursion can read them.
    let pp_root_vars = HashValue(
        ctx.constant(preprocessed_root.0),
        ctx.constant(preprocessed_root.1),
    );

    // Precompute the dummy-hash chain off-circuit, then wire each entry as a `ctx.constant`.
    // `dummy_hash_vars[d]` is the hash of an all-dummy subtree of height `d`.
    let dummy_hashes_qm31 = precompute_dummy_hashes(preprocessed_root, tree_height);
    let dummy_hash_vars: Vec<HashValue<Var>> = dummy_hashes_qm31
        .iter()
        .map(|h| HashValue(ctx.constant(h.0), ctx.constant(h.1)))
        .collect();

    // Right-pad with dummies to the next power of two so the recursion sees a perfect tree.
    // Padded positions are never visited by the in-circuit recursion (the short-circuit catches
    // them at their containing all-dummy subtree root), but we keep them in `padded_outputs` so
    // a flat tree-position index lines up with leaf positions.
    let mut padded_outputs: Vec<Vec<QM31>> = hints.leaf_outputs.clone();
    padded_outputs.resize(n_total, dummy_leaf_output());

    let mut leaf_vars_out: Vec<Vec<Var>> = Vec::with_capacity(n_real);
    let computed_root = compute_subtree_hash(
        ctx,
        pp_root_vars,
        &padded_outputs,
        0,
        n_real,
        tree_height,
        &dummy_hash_vars,
        &mut leaf_vars_out,
    );

    // Bind the computed root hash to the caller-supplied root_hash.
    eq(ctx, computed_root.0, root_hash.0);
    eq(ctx, computed_root.1, root_hash.1);

    leaf_vars_out
}

/// Off-circuit computation of `dummy_hash_at_depth(d)` for every `d ∈ 0..=tree_height`.
///
/// `dummy_hashes[0] = blake(pp_root.0 || pp_root.1 || ...dummy_leaf_output())`, and for `d > 0`
/// `dummy_hashes[d] = blake(pp_root.0 || pp_root.1 || h_{d-1}.0 || h_{d-1}.1 || h_{d-1}.0 ||
/// h_{d-1}.1)`. The doubled child encodes that both children of an all-dummy subtree are identical.
fn precompute_dummy_hashes(pp_root: HashValue<QM31>, tree_height: usize) -> Vec<HashValue<QM31>> {
    let mut result = Vec::with_capacity(tree_height + 1);

    let dummy = dummy_leaf_output();
    let mut preimage = vec![pp_root.0, pp_root.1];
    preimage.extend(&dummy);
    result.push(QM31::blake(&preimage, preimage.len() * 16));

    for d in 1..=tree_height {
        let prev = result[d - 1];
        let preimage = vec![pp_root.0, pp_root.1, prev.0, prev.1, prev.0, prev.1];
        result.push(QM31::blake(&preimage, preimage.len() * 16));
    }

    result
}

/// Recursively builds the subtree of Blake gates and returns the subtree's hash. Side-effect:
/// appends each *real* leaf's guessed-output Vars to `leaf_vars_out` in tree position order.
///
/// All-dummy subtrees are short-circuited to a precomputed constant from `dummy_hash_vars`;
/// they emit no Blake gates and contribute nothing to `leaf_vars_out`.
///
/// `leaves.len()` must be a power of two; `depth` must equal `log2(leaves.len())`; `leaf_offset`
/// is the position of `leaves[0]` in the full padded array.
#[allow(clippy::too_many_arguments)]
fn compute_subtree_hash<Value: IValue>(
    ctx: &mut Context<Value>,
    pp_root: HashValue<Var>,
    leaves: &[Vec<QM31>],
    leaf_offset: usize,
    n_real: usize,
    depth: usize,
    dummy_hash_vars: &[HashValue<Var>],
    leaf_vars_out: &mut Vec<Vec<Var>>,
) -> HashValue<Var> {
    // All-dummy subtree: every position in this subtree is a dummy (the entire range starts at
    // or after `n_real`). Return the precomputed constant; no recursion, no Blake gate.
    if leaf_offset >= n_real {
        return dummy_hash_vars[depth];
    }

    // Single-leaf subtree (depth 0). The all-dummy guard above means this must be a real leaf.
    if leaves.len() == 1 {
        let leaf_output = &leaves[0];
        let leaf_vars: Vec<Var> = leaf_output
            .iter()
            .map(|qm31| guess(ctx, Value::from_qm31(*qm31)))
            .collect();
        let mut preimage = vec![pp_root.0, pp_root.1];
        preimage.extend(&leaf_vars);
        let leaf_hash = blake(ctx, &preimage, 16 * preimage.len());
        leaf_vars_out.push(leaf_vars);
        return leaf_hash;
    }

    // Internal (mixed or all-real): split, recurse, combine.
    let mid = leaves.len() / 2;
    let left_hash = compute_subtree_hash(
        ctx,
        pp_root,
        &leaves[..mid],
        leaf_offset,
        n_real,
        depth - 1,
        dummy_hash_vars,
        leaf_vars_out,
    );
    let right_hash = compute_subtree_hash(
        ctx,
        pp_root,
        &leaves[mid..],
        leaf_offset + mid,
        n_real,
        depth - 1,
        dummy_hash_vars,
        leaf_vars_out,
    );

    let preimage = vec![
        pp_root.0,
        pp_root.1,
        left_hash.0,
        left_hash.1,
        right_hash.0,
        right_hash.1,
    ];
    blake(ctx, &preimage, 16 * preimage.len())
}
