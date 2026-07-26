//! Generic leaf prove/preprocess tail: takes an already-built leaf [`FinalizedContext`] (the
//! AIR-specific circuit build stays with the caller) and pads then proves it ([`prove_leaf`]), or
//! pads then preprocesses it ([`leaf_preprocessed`]). Byte-identity: both reproduce the caller's
//! former inline sequence exactly (same pad target, prove args, `TreeProof` fields), so relocating
//! them here changes no proof.

use crate::TreeProof;
use crate::precomputes::RecursionPrecompute;

use circuit_common::finalize::{ComponentSizes, pad_to_targets};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_prover::prover::{
    prepare_circuit_proof_for_circuit_verifier, prove_circuit_with_precompute,
};
use circuits::blake::HashValue;
use circuits::context::FinalizedContext;
use circuits::ivalue::NoValue;
use stwo::core::fields::qm31::QM31;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;

/// Pads the built leaf `ctx` to `leaf_target`, proves it against the held leaf tree, and wraps the
/// result into a [`TreeProof`] reporting `leaf_root`. The caller builds the AIR-specific
/// `FinalizedContext<QM31>`; everything from the pad onward is generic.
pub fn prove_leaf(
    mut ctx: FinalizedContext<QM31>,
    leaf_target: ComponentSizes,
    pre: &RecursionPrecompute,
    leaf_root: HashValue<QM31>,
) -> TreeProof {
    pad_to_targets(&mut ctx, leaf_target);
    let leaf_tree = &pre.leaf;
    let circuit_proof = prove_circuit_with_precompute::<Blake2sM31MerkleChannel>(
        &pre.base_column_pool,
        &pre.twiddles,
        &leaf_tree.preprocessed,
        MaybeOwned::Borrowed(&leaf_tree.tree),
        ctx.values(),
        leaf_tree.pcs_config,
    )
    .expect("gate_air leaf prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
    let output_values = public_data
        .output_values
        .try_into()
        .expect("leaf emits N_RESERVED outputs");

    TreeProof {
        proof,
        preprocessed_root: leaf_root,
        output_values,
    }
}

/// Pads the built NoValue leaf `ctx` to `leaf_target` and preprocesses it into the leaf
/// [`PreprocessedCircuit`] — the witness-independent leaf shape the precompute / config derivation
/// commits.
pub fn leaf_preprocessed(
    mut ctx: FinalizedContext<NoValue>,
    leaf_target: ComponentSizes,
) -> PreprocessedCircuit {
    pad_to_targets(&mut ctx, leaf_target);
    PreprocessedCircuit::preprocess_circuit(&mut ctx)
}
