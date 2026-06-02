use circuits::blake::HashValue;
use circuits::context::Context;
use circuits::ivalue::{IValue, qm31_from_u32s};
use stwo::core::fields::qm31::QM31;

use crate::{UnpackerHints, dummy_leaf_output, run_unpacker};

/// Builds the preimage `[pp_root.0, pp_root.1, ...payload]` and Blake-hashes it off-circuit.
/// Mirrors the in-circuit hash construction used by both `circuit_verifier::verify` and the
/// unpacker, so the two are guaranteed to agree.
fn hash_with_pp_root(pp_root: HashValue<QM31>, payload: &[QM31]) -> HashValue<QM31> {
    let preimage: Vec<QM31> = std::iter::once(pp_root.0)
        .chain(std::iter::once(pp_root.1))
        .chain(payload.iter().copied())
        .collect();
    QM31::blake(&preimage, preimage.len() * 16)
}

/// Recursively computes the expected hash of a subtree of `leaves`, off-circuit. Mirrors the
/// in-circuit recursion done by `compute_subtree_hash`, so the test's expected value is
/// guaranteed to match whatever shape of recursion the unpacker emits.
///
/// If `leaves.len()` is not a power of two, the slice is padded on the right with
/// [`dummy_leaf_output()`] up to the next power of two — the tree shape the unpacker is
/// contracted to materialize.
fn expected_subtree_hash(pp_root: HashValue<QM31>, leaves: &[Vec<QM31>]) -> HashValue<QM31> {
    let n_total = leaves.len().next_power_of_two().max(1);
    if leaves.len() < n_total {
        let mut padded: Vec<Vec<QM31>> = leaves.to_vec();
        padded.resize(n_total, dummy_leaf_output());
        return expected_subtree_hash(pp_root, &padded);
    }
    if leaves.len() == 1 {
        return hash_with_pp_root(pp_root, &leaves[0]);
    }
    let mid = leaves.len() / 2;
    let left = expected_subtree_hash(pp_root, &leaves[..mid]);
    let right = expected_subtree_hash(pp_root, &leaves[mid..]);
    hash_with_pp_root(pp_root, &[left.0, left.1, right.0, right.1])
}

/// Test 1: `N = 2` real leaves, no dummies (`N` is already a power of two).
/// Tree height = 1; the root has two leaf children, each with a distinct output length.
///
/// Builds the expected root hash off-circuit, runs the unpacker with that hash and the matching
/// `leaf_outputs` hints, and asserts:
///   1. The resulting circuit is valid (every constraint holds for the chosen witness).
///   2. The returned `Vec<Vec<Var>>` has one inner `Vec` per real leaf with the right length.
///   3. The returned `Var`s carry the QM31 values from `leaf_outputs`.
#[test]
fn unpacker_n2_no_dummies() {
    // Distinguishable test data — pp_root, two leaf outputs of differing length.
    let pp_root: HashValue<QM31> =
        HashValue(qm31_from_u32s(1, 0, 0, 0), qm31_from_u32s(2, 0, 0, 0));
    let leaf_0_output: Vec<QM31> = (10..13).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect();
    let leaf_1_output: Vec<QM31> = (20..22).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect();

    // Off-circuit reference hashes.
    let leaf_0_hash = hash_with_pp_root(pp_root, &leaf_0_output);
    let leaf_1_hash = hash_with_pp_root(pp_root, &leaf_1_output);
    let root_payload = vec![leaf_0_hash.0, leaf_0_hash.1, leaf_1_hash.0, leaf_1_hash.1];
    let root_hash = hash_with_pp_root(pp_root, &root_payload);

    // Build the unpacker circuit with witness values. pp_root is passed by value; root_hash is
    // wired as constant Vars.
    let mut ctx: Context<QM31> = Context::default();
    let root_hash_vars = HashValue(ctx.constant(root_hash.0), ctx.constant(root_hash.1));
    let hints = UnpackerHints {
        leaf_outputs: vec![leaf_0_output.clone(), leaf_1_output.clone()],
    };

    let result = run_unpacker(&mut ctx, root_hash_vars, pp_root, &hints);

    // (1) The constraints must hold for the chosen witness.
    assert!(
        ctx.is_circuit_valid(),
        "circuit constraints failed for valid input"
    );

    // (2) Output shape: one Vec per real leaf, in tree position order, with the right size.
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].len(), leaf_0_output.len());
    assert_eq!(result[1].len(), leaf_1_output.len());

    // (3) Output values match the hinted leaf outputs.
    for (var, expected) in result[0].iter().zip(leaf_0_output.iter()) {
        assert_eq!(ctx.get(*var), *expected);
    }
    for (var, expected) in result[1].iter().zip(leaf_1_output.iter()) {
        assert_eq!(ctx.get(*var), *expected);
    }
}

/// Test 2: `N = 4` real leaves, no dummies. Tree height = 2.
///
/// Exercises the internal-node recursion below the root that test 1's depth-1 case does not
/// reach: each of the root's two children is itself an internal node combining two leaf hashes.
/// Leaf output sizes vary to keep the test honest about per-leaf k_i.
#[test]
fn unpacker_n4_no_dummies() {
    let pp_root: HashValue<QM31> =
        HashValue(qm31_from_u32s(7, 0, 0, 0), qm31_from_u32s(8, 0, 0, 0));

    // Four leaves with varying output sizes (3, 2, 4, 1 QM31s).
    let leaf_outputs: Vec<Vec<QM31>> = vec![
        (10..13).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        (20..22).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        (30..34).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        vec![qm31_from_u32s(40, 0, 0, 0)],
    ];

    let root_hash = expected_subtree_hash(pp_root, &leaf_outputs);

    let mut ctx: Context<QM31> = Context::default();
    let root_hash_vars = HashValue(ctx.constant(root_hash.0), ctx.constant(root_hash.1));
    let hints = UnpackerHints {
        leaf_outputs: leaf_outputs.clone(),
    };

    let result = run_unpacker(&mut ctx, root_hash_vars, pp_root, &hints);

    assert!(
        ctx.is_circuit_valid(),
        "circuit constraints failed for valid input"
    );

    assert_eq!(result.len(), leaf_outputs.len());
    for (got, expected) in result.iter().zip(leaf_outputs.iter()) {
        assert_eq!(got.len(), expected.len());
        for (var, expected_value) in got.iter().zip(expected.iter()) {
            assert_eq!(ctx.get(*var), *expected_value);
        }
    }
}

/// Test 3: `N = 3` real leaves, one dummy at slot 3. `N_total = 4`, tree height = 2.
///
/// Exercises the dummy-leaf path. Slot 3 is padded with [`dummy_leaf_output()`]; the right
/// internal node combines a real-leaf hash (L2) with the dummy-leaf hash. The unpacker must
/// produce exactly 3 entries in the returned `Vec<Vec<Var>>` — the dummy is not surfaced.
#[test]
fn unpacker_n3_one_dummy() {
    let pp_root: HashValue<QM31> =
        HashValue(qm31_from_u32s(5, 0, 0, 0), qm31_from_u32s(6, 0, 0, 0));

    let leaf_outputs: Vec<Vec<QM31>> = vec![
        (10..13).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        (20..22).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        vec![qm31_from_u32s(30, 0, 0, 0)],
    ];

    let root_hash = expected_subtree_hash(pp_root, &leaf_outputs);

    let mut ctx: Context<QM31> = Context::default();
    let root_hash_vars = HashValue(ctx.constant(root_hash.0), ctx.constant(root_hash.1));
    let hints = UnpackerHints {
        leaf_outputs: leaf_outputs.clone(),
    };

    let result = run_unpacker(&mut ctx, root_hash_vars, pp_root, &hints);

    assert!(
        ctx.is_circuit_valid(),
        "circuit constraints failed for valid input"
    );

    // Output should expose exactly the 3 real leaves; the dummy at slot 3 must not appear.
    assert_eq!(result.len(), leaf_outputs.len());
    for (got, expected) in result.iter().zip(leaf_outputs.iter()) {
        assert_eq!(got.len(), expected.len());
        for (var, expected_value) in got.iter().zip(expected.iter()) {
            assert_eq!(ctx.get(*var), *expected_value);
        }
    }
}

/// Test 4: `N = 5` real leaves, three dummies at slots 5..8. `N_total = 8`, tree height = 3.
///
/// Exercises the dummy short-circuit at *two* depths simultaneously:
/// - Slot 5 is a single dummy leaf — short-circuited at depth 0 via `dummy_hash_vars[0]`.
/// - Slots 6,7 form an all-dummy depth-1 subtree — short-circuited at depth 1 via
///   `dummy_hash_vars[1]`, with no recursion into the two dummy leaves underneath.
///
/// The unpacker must still expose exactly 5 entries in the output Vec, all real.
#[test]
fn unpacker_n5_dummies_short_circuit_at_two_depths() {
    let pp_root: HashValue<QM31> =
        HashValue(qm31_from_u32s(11, 0, 0, 0), qm31_from_u32s(12, 0, 0, 0));

    let leaf_outputs: Vec<Vec<QM31>> = vec![
        (10..13).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        (20..22).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        (30..34).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
        vec![qm31_from_u32s(40, 0, 0, 0)],
        (50..52).map(|i| qm31_from_u32s(i, 0, 0, 0)).collect(),
    ];

    let root_hash = expected_subtree_hash(pp_root, &leaf_outputs);

    let mut ctx: Context<QM31> = Context::default();
    let root_hash_vars = HashValue(ctx.constant(root_hash.0), ctx.constant(root_hash.1));
    let hints = UnpackerHints {
        leaf_outputs: leaf_outputs.clone(),
    };

    let result = run_unpacker(&mut ctx, root_hash_vars, pp_root, &hints);

    assert!(
        ctx.is_circuit_valid(),
        "circuit constraints failed for valid input"
    );

    assert_eq!(result.len(), leaf_outputs.len());
    for (got, expected) in result.iter().zip(leaf_outputs.iter()) {
        assert_eq!(got.len(), expected.len());
        for (var, expected_value) in got.iter().zip(expected.iter()) {
            assert_eq!(ctx.get(*var), *expected_value);
        }
    }
}
