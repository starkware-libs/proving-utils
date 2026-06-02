use circuits::blake::HashValue;
use circuits::context::Context;
use circuits::ivalue::{IValue, qm31_from_u32s};
use stwo::core::fields::qm31::QM31;

use crate::{UnpackerHints, run_unpacker};

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

    // Build the unpacker circuit with witness values, wire pp_root and root_hash as constant
    // Vars, then invoke the unpacker.
    let mut ctx: Context<QM31> = Context::default();
    let pp_root_vars = HashValue(ctx.constant(pp_root.0), ctx.constant(pp_root.1));
    let root_hash_vars = HashValue(ctx.constant(root_hash.0), ctx.constant(root_hash.1));
    let hints = UnpackerHints {
        leaf_outputs: vec![leaf_0_output.clone(), leaf_1_output.clone()],
    };

    let result = run_unpacker(&mut ctx, root_hash_vars, pp_root_vars, &hints);

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
