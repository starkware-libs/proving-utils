//! In-binary N-leaf `k`-to-1 multiverifier recursion tree.
//!
//! Given an ordered list of `N` leaf circuit proofs, this crate folds the entire recursion tree
//! above them into a single root proof by repeatedly proving a `FOLD_ARITY`-to-1
//! [`build_multiverifier_circuit`] node on groups of `k` children. Each node verifies its `k` child
//! proofs and emits a Blake hash binding `[ppRoot_i, outs_i for i in 0..k]` (children left-to-right)
//! as its own `N_RESERVED` (eight) output digest words; that hash is what the parent node (and, at
//! the top, the [`circuit_unpacker`](https://docs.rs/circuit-unpacker)) consumes. As of stwo #1425
//! the preprocessed root is the full eight-word Blake2s digest (`HashValue`), not the old reduced
//! two-QM31 form, and the node preimage is hashed with `blake2s_u32s`.
//!
//! Arity is the named constant [`FOLD_ARITY`]. Every full-`k` node is exactly-`k` (full-`k` nodes at
//! a level share one precompute / `preprocessed_root`); SHORT nodes (the level-0 leaf-remainder
//! groups and the ROOT) are `m`-child with `m ∈ 2..=k` — their arity, and hence circuit shape and
//! `preprocessed_root`, is a deterministic function of the public `N` alone, never prover-chosen.
//!
//! Because the multiverifier *self-verifies* (a multiverifier proof has the same circuit shape as
//! the proof it verifies), a single [`SharedConfig`] built from `all_circuit_components` works for
//! every level — the leaf level and all internal levels alike — and every internal node reports
//! the same fixed `preprocessed_root` ([`AggregateConfig::node_preprocessed_root`]).
//!
//! This crate folds the multiverifier tree, then proves the **root verification**
//! ([`prove_root_verification`]) — the only published, and only zk-blinded, proof. Every
//! multiverifier proof, the root included, is internal: consumed (guessed into the witness) by the
//! next circuit up, never published; no multiverifier node is ever blinded.
//!
//! The root verification (1) runs the STARK verifier on the root multiverifier proof in-circuit,
//! and (2) **unpacks** it: it reconstructs the tree's root hash in-circuit from prover-supplied
//! per-leaf output hints — via the same per-node `blake2s_u32s([ppR_i words, outs_i words] for the
//! k children)` binding the nodes used — binds the reconstructed root to the verified root output,
//! and emits the leaf
//! outputs. The unpack is inherently **O(N)** (it touches every leaf). Using one trusted
//! `leaf_preprocessed_root` for all leaves also forces them to share an AIR.
//!
//! Each leaf's output will be `H_i = blake(H_P ‖ x_i ‖ y_i)` (program commitment + input + output)
//! once gate_air leaves exist; rehashing every leaf against one shared `H_P` during the unpack is
//! what enforces same-program. With the current cairo stand-in leaves the output is just the leaf
//! circuit's `output_values`, so the unpack exercises the plumbing but not that encoding yet.
//!
//! Any `N >= 1` is supported via a two-phase deterministic fold (byte-identical in the sequential
//! and streaming paths, and reconstructed identically by the unpacker):
//!   - **Level 0** consumes ALL `N` leaves into height-1 leaf-verifying nodes (arities from
//!     `level0_group_sizes`, each `2..=k`, never a lone leaf). This is the LEAF↔NODE DECOUPLING FIX:
//!     leaves (lift24) and nodes (lift25) differ in proof shape, so a carried-up leaf under a
//!     height-≥2 (lift25) fold panics the in-circuit Merkle height check. Consuming every leaf at
//!     level 0 guarantees no leaf ever survives above height 1.
//!   - **Levels ≥ 1** group the height-1 nodes left-to-right into exactly-`k` node-verifying nodes,
//!     carry the `< k` remainder up unchanged (carrying a NODE is safe — all are lift25), and fold a
//!     final `2..=k` level into the (possibly short) root. Every height-≥2 fold is homogeneous.
//!
//! One deterministic unbalanced `k`-ary tree of real proofs (no power-of-`k` padding, no dummies). A
//! dynamic permutation-argument unpacker that handles an arbitrary tree shape unknown at
//! circuit-build time is a later optimization.

use std::sync::Arc;

/// Fold arity `k`: each internal node verifies exactly this many children (`k`-to-1 fold).
///
/// This is the single source of truth for the arity across the whole recursion pipeline — the
/// tree/streaming fold, the topology, `prove_node`, and (critically) the unpacker's per-node hash
/// preimage in [`prove_root_verification`] all read it, so the out-of-circuit unpacker and the
/// in-circuit node hash ([`build_multiverifier_circuit`]) stay byte-identical. Re-sweep the arity
/// (e.g. `4` vs `8`) by changing only this constant; nothing else hard-codes the child count.
///
/// A level's `len() % FOLD_ARITY` (< k) remainder is carried up unchanged (mirroring the old
/// carry-one), so nodes are always exactly `k` children — never variable-child.
pub const FOLD_ARITY: usize = 8;

/// Base-fanning arity `b`: how many gate_air BASE proofs one base-fanning node ("base-node") verifies
/// and folds. INDEPENDENT of [`FOLD_ARITY`] (the up-tree node-node fold arity): a base-node does the
/// work of `b` old leaves + one old R1 leaf-verifying node in a single circuit, and its own output
/// proof is folded up the tree with [`FOLD_ARITY`] like any other node.
///
/// It is the single source of truth for the level-0 (bottom) arity — the base-node topology
/// ([`base_fan_group_sizes`]) and the unpacker's bottom `fold_group` in [`prove_root_verification`]
/// both read it via [`base_fan_arity`], so the base-nodes proved upstream (in gate-air-leaf) and the
/// unpacker's reconstruction stay byte-identical.
///
/// Default `4`. Bounded by the 2^26 base-shard ceiling (roughly `b <= 32`) and O(shots/shard); the
/// optimal `b` is a later box-tuning question, not fixed here.
pub const BASE_FAN_ARITY: usize = 4;

/// The base-fanning arity `b` in effect, reading the `BASE_FAN_ARITY` env override (else the
/// [`BASE_FAN_ARITY`] const). Read at the consistent call sites (topology + unpacker) so the fold and
/// the reconstruction agree; a value `< 1` is clamped to 1 (`b == 1` = no fanning, one base per
/// base-node — the degenerate old-leaf behaviour).
///
/// Thin shim over [`TopologyConfig::from_env`]`().base_fan_arity` — kept so any residual call site (and
/// the `BASE_FAN_ARITY` env sweep) still resolves to the same value the config would carry.
pub fn base_fan_arity() -> usize {
    TopologyConfig::from_env().base_fan_arity
}

/// Default recursion (node-node / root) FRI blowup factor. Feeds the ~96-bit-secure `(pow_bits,
/// n_queries)` table via `get_pcs_config`; the value that makes production node/root proofs.
pub const RECURSION_LOG_BLOWUP: u32 = 3;

/// Default base (shard / "leaf") gate_air proof FRI blowup factor. `(pow_bits, n_queries)` and lifting
/// are derived from it via `leaf_pcs_config` to a ~96-bit-secure config. Sweep knob: 1/2/3.
pub const BASE_LOG_BLOWUP: u32 = 1;

/// Default shots (iadd256 executions) per base shard — the manual partition knob. `n_shards =
/// ceil(samples / shots_per_shard)`.
pub const SHOTS_PER_SHARD: usize = 2;

/// Which bottom-layer recursion topology the pipeline uses. The up-tree node-node (R2) fold above the
/// bottom layer is SHARED and identical in both modes — only the bottom layer (and the config /
/// unpacker reconstruction that binds it) differs.
///
/// - [`FoldMode::BaseFanning`] (DEFAULT): the current production topology. gate-air-leaf proves
///   **base-nodes** upstream (one circuit verifies `b` gate_air bases and folds them), and
///   `recursive_aggregate` folds those height-1 base-nodes up the tree with `FOLD_ARITY`. See
///   [`recursive_aggregate_prove`] / [`prove_root_verification`] (`BaseFanBottom`).
/// - [`FoldMode::LeafR1R2`]: the PREVIOUS (pre-base-fanning) topology. gate-air-leaf proves one
///   standalone **leaf** per shard; `recursive_aggregate` consumes ALL leaves at level 0 into height-1
///   **leaf-verifying (R1)** nodes ([`recursive_aggregate_prove_leaves`]) and then folds those up with
///   the SAME shared R2 fold. The unpacker reconstructs from the raw leaves
///   ([`prove_root_verification_leaves`], `LeafBottom`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum FoldMode {
    /// Base-fanning bottom (base-nodes proved upstream). The default.
    #[default]
    BaseFanning,
    /// Standalone-leaf bottom with a level-0 leaf-verifying (R1) layer.
    LeafR1R2,
}

/// All FREE topology parameters, in one place, threaded through the recursion + base-proof pipeline.
///
/// Every field is a *free knob*; everything else (the `(pow_bits, n_queries)` at 96-bit, the trusted
/// roots, the PCS/padding targets, `n_shards`, the base-shard trace log) is DERIVED from these (see
/// `leaf::derive_base_fanning_config_ex`, `leaf_pcs_config`, `get_pcs_config`). Security params
/// (`fold_step`, `log_last_layer`, the 96-bit floor, `INTERACTION_POW_BITS`) are pinned, NOT exposed
/// here — they must never be swept below the security floor.
///
/// Construct once (via [`TopologyConfig::from_env`] on the production path, or a literal in a test)
/// and thread it: `fold_arity` rides on the [`AggregateConfig`] (so every config-carrying fold fn
/// reads `config.fold_arity`), while the blowups / `base_fan_arity` / `shots_per_shard` are read at
/// the construction / derivation sites. The [`Default`] impl and [`TopologyConfig::from_env`] both
/// reproduce the current production values, so introducing the struct is a byte-identical no-op.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TopologyConfig {
    /// Base (shard) gate_air proof FRI blowup factor. Default [`BASE_LOG_BLOWUP`] (env `BASE_BLOWUP`).
    pub base_log_blowup: u32,
    /// Recursion (node-node / root) FRI blowup factor. Default [`RECURSION_LOG_BLOWUP`].
    pub recursion_log_blowup: u32,
    /// Node-node fold arity `k` (each internal R2 node verifies exactly `k` children). Default
    /// [`FOLD_ARITY`].
    pub fold_arity: usize,
    /// Base-fanning arity `b` (bases per base-node). Default [`BASE_FAN_ARITY`] (env `BASE_FAN_ARITY`);
    /// clamped to `>= 1`.
    pub base_fan_arity: usize,
    /// Shots per base shard (partition knob). Default [`SHOTS_PER_SHARD`] (env `GATE_AIR_SHARD_SHOTS`).
    pub shots_per_shard: usize,
    /// Bottom-layer topology (default [`FoldMode::BaseFanning`], env `GATE_AIR_FOLD_MODE` =
    /// `base_fanning` | `leaf_r1r2`). Selects the parallel bottom-layer path; the shared up-tree R2
    /// fold is identical in both.
    pub fold_mode: FoldMode,
}

impl Default for TopologyConfig {
    /// The current production values (a byte-identical no-op default).
    fn default() -> Self {
        TopologyConfig {
            base_log_blowup: BASE_LOG_BLOWUP,
            recursion_log_blowup: RECURSION_LOG_BLOWUP,
            fold_arity: FOLD_ARITY,
            base_fan_arity: BASE_FAN_ARITY,
            shots_per_shard: SHOTS_PER_SHARD,
            fold_mode: FoldMode::BaseFanning,
        }
    }
}

impl TopologyConfig {
    /// The topology config in effect, applying the env overrides existing sweep scripts rely on:
    /// `BASE_BLOWUP` → `base_log_blowup`, `BASE_FAN_ARITY` → `base_fan_arity` (clamped `>= 1`),
    /// `GATE_AIR_SHARD_SHOTS` → `shots_per_shard` (`> 0`), `GATE_AIR_FOLD_ARITY` → `fold_arity`
    /// (clamped `>= 2`). `recursion_log_blowup` keeps its [`Default`] value (no env knob today). Unset /
    /// unparseable env vars fall back to the default, so with a clean environment this equals
    /// [`TopologyConfig::default`] exactly (in particular `fold_arity` stays 8 — a byte-identical no-op
    /// unless `GATE_AIR_FOLD_ARITY` is explicitly set, e.g. `=4` for the a2 sweep).
    pub fn from_env() -> Self {
        fn parse_env<T: std::str::FromStr>(k: &str) -> Option<T> {
            std::env::var(k).ok().and_then(|s| s.parse().ok())
        }
        let d = TopologyConfig::default();
        TopologyConfig {
            base_log_blowup: parse_env("BASE_BLOWUP").unwrap_or(d.base_log_blowup),
            recursion_log_blowup: d.recursion_log_blowup,
            fold_arity: parse_env::<usize>("GATE_AIR_FOLD_ARITY")
                .unwrap_or(d.fold_arity)
                .max(2),
            base_fan_arity: parse_env::<usize>("BASE_FAN_ARITY")
                .unwrap_or(d.base_fan_arity)
                .max(1),
            shots_per_shard: parse_env::<usize>("GATE_AIR_SHARD_SHOTS")
                .filter(|&n| n > 0)
                .unwrap_or(d.shots_per_shard),
            fold_mode: match std::env::var("GATE_AIR_FOLD_MODE").ok().as_deref() {
                Some("leaf_r1r2") => FoldMode::LeafR1R2,
                Some("base_fanning") => FoldMode::BaseFanning,
                // Unset / unparseable falls back to the default (BaseFanning) — a byte-identical no-op.
                _ => d.fold_mode,
            },
        }
    }
}

use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_common::N_RESERVED;
use circuit_common::finalize::{
    ComponentSizes, add_zk_blinding, compute_padded_sizes, pad_context, pad_to_targets,
};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_multiverifier::verify::{
    MultiverifierInput, SharedConfig, build_multiverifier_circuit,
};
use circuit_prover::prover::{
    CircuitProof, prepare_circuit_proof_for_circuit_verifier, prove_circuit_assignment,
    prove_circuit_with_precompute,
};
use circuit_verifier::statement::CircuitStatement;
use circuit_verifier::verify::{CircuitConfig, CircuitPublicData, verify_circuit};
use circuits::blake::{HashValue, blake2s_u32s, unpack_qm31s_to_u32_words};
use circuits::wrappers::U32Wrapper;
use circuits::context::{Context, FinalizedContext, Var};
use circuits::ops::{Guess, eq, guess};
use circuits_stark_verifier::proof::Proof;
use circuits_stark_verifier::verify::verify;
use rayon::ThreadPool;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sM31MerkleChannel, Blake2sMerkleHasher};
use stwo::prover::ProvingError;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::twiddles::TwiddleTree;

/// A proven node carried up the tree.
///
/// Bundles a circuit proof with the two pieces the parent multiverifier needs to reconstruct the
/// inner [`circuits::context`] statement it verifies: the preprocessed root of the circuit that
/// produced the proof, and its two output values.
#[derive(Clone)]
pub struct TreeProof {
    pub proof: Proof<QM31>,
    pub preprocessed_root: HashValue<QM31>,
    pub output_values: [QM31; N_RESERVED],
}

/// One gate_air BASE's contribution to the unpacker's base-node reconstruction: the base's own
/// preprocessed root and its output digest `H_i`. These are the two pieces a base-node's fold-hash
/// binds per child (`[preprocessed_root words, H_i words]`), so the unpacker reconstructs each
/// base-node's hash from `b` of these — byte-identical to `build_gate_air_base_node_circuit`.
///
/// A base has no circuit `proof` field here: the unpacker never re-verifies a base (the upstream
/// base-node already did, in-circuit); it only rehashes each base's public `(preprocessed_root, H_i)`.
#[derive(Clone)]
pub struct BaseOutput {
    /// The base's preprocessed (tree0) root — shard-invariant, equal to `AggregateConfig`'s
    /// `base_preprocessed_root` for every honest base; guessed per base in the reconstruction.
    pub preprocessed_root: HashValue<QM31>,
    /// The base's output digest `H_i = blake2s(H_P ‖ x_i ‖ y_i)` (eight QM31 words).
    pub output_values: [QM31; N_RESERVED],
}

/// The bottom-level input to the unpacker under base-fanning: the ordered bases plus the public data
/// needed to reconstruct their base-nodes.
///
/// The base-nodes were proved UPSTREAM (in gate-air-leaf); recursive_aggregate cannot rebuild the
/// gate_air base-node circuit, so gate-air-leaf supplies the trusted (public, arity-derived) root
/// each base-node reported. `base_node_roots[g]` is the reported preprocessed root of the `g`-th
/// base-node, whose children are the bases at group `g` of `base_fan_group_sizes(bases.len(), b)`.
pub struct BaseFanBottom {
    /// The gate_air bases in canonical order (base `i` is shard `i`).
    pub bases: Vec<BaseOutput>,
    /// The base-fanning arity `b` used to group bases into base-nodes (from [`base_fan_arity`]).
    pub b: usize,
    /// Per base-node group (in `base_fan_group_sizes` order), the trusted preprocessed root the
    /// corresponding base-node reported (full-`b` groups all share `R_base`; a short trailing group
    /// reports its own `R_base'(m)`). Public + arity-derived, computed by gate-air-leaf's
    /// `derive_base_fanning_config`; the unpacker binds them.
    pub base_node_roots: Vec<HashValue<QM31>>,
}

/// zk-blinding parameters for the root verification (the only blinded proof).
#[derive(Clone, Copy)]
pub struct ZkBlind {
    /// Seed for the ChaCha20 RNG that draws the blinding values.
    pub seed: [u8; 32],
    /// Number of blinding rows per witness component — must be the root proof's `n_queries`.
    pub n_padding: usize,
}

/// Static configuration shared by every node in the tree.
///
/// BASE-FANNING. The bottom of the tree is a **base-node** (`R_base`): a single circuit that verifies
/// `b` = [`base_fan_arity`] gate_air BASE proofs directly and folds them (built + proved UPSTREAM in
/// gate-air-leaf's `build_gate_air_base_node_circuit` — `recursive_aggregate` is leaf-type-agnostic
/// and never builds it). It replaces the old standalone leaf layer AND the old R1 leaf-verifying
/// node in one proof. `recursive_aggregate` therefore only folds the base-nodes up the tree with
/// `FOLD_ARITY`, and only needs two trusted bottom roots + the R2 machinery:
///   - **R_base** ([`base_node_preprocessed_root`]) — the base-node circuit's own preprocessed root.
///     A height-1 base-node reports it to its R2 parent, and the unpacker binds it when it
///     reconstructs a base-node from `b` bases.
///   - **base tree0** ([`base_preprocessed_root`]) — the shard-invariant preprocessed root of the
///     gate_air BASE proofs. The unpacker uses this single constant for *every* base, which both
///     reconstructs the base-node hashes and forces every base to share this AIR.
///   - **R2** ([`node_preprocessed_root`]) — height-≥2 full-`k` nodes, which verify `FOLD_ARITY`
///     NODES (child config [`node_shared_config`], the multiverifier's own shape — the
///     self-verifying fixed point). A base-node's OWN proof is a circuit-prover proof of the common
///     node shape, so R2 verifies base-nodes exactly as it verified R1 nodes; UNCHANGED from the
///     pre-base-fanning topology.
///
/// SHORT nodes (arity `2..=k-1`: the level-0 base-node-remainder groups and the short root) have a
/// structurally different circuit ⇒ a DISTINCT preprocessed root per (level, arity). These are not
/// stored here; they are recomputed on the fly (`prove_short_node` when proving, and
/// `short_node_preprocessed_root` in the unpacker) from the public (level, arity) — never
/// prover-chosen. All node variants pad to a COMMON `node_target_padding_sizes` so their *output*
/// proofs share one shape (one [`node_shared_config`], one node PCS).
pub struct AggregateConfig {
    /// Verifier/prover config for a node whose CHILDREN are NODES (level-≥2 nodes) and for
    /// verifying the ROOT proof in the unpacker. Built from the multiverifier node's own
    /// preprocessed shape (the self-verifying fixed point). A base-node's own proof shares this shape
    /// (padded to the common `node_target_padding_sizes`), so R2 verifies base-nodes with it too.
    pub node_shared_config: SharedConfig,
    /// **R2** — the preprocessed root of a level-≥2 (node-verifying) multiverifier node. Reported by
    /// every internal node of height ≥ 2 to its parent.
    pub node_preprocessed_root: HashValue<QM31>,
    /// **R_base** — the preprocessed root of the base-fanning node circuit (verifies `b` bases). A
    /// height-1 base-node reports it to its R2 parent; the unpacker binds it for the reconstructed
    /// base-node. Analogous to the old R1 (level-1 leaf-verifying node) root.
    pub base_node_preprocessed_root: HashValue<QM31>,
    /// The trusted (shard-invariant) preprocessed root of the gate_air BASE proofs. The root
    /// verification's unpacker uses this single constant for *all* bases, which both reconstructs the
    /// base-node hashes and forces every base to share this AIR (a base with a different `pp_root`
    /// makes the reconstruction miss the verified root). Analogous to the old `leaf_preprocessed_root`.
    pub base_preprocessed_root: HashValue<QM31>,
    /// Padding targets applied to every node's trace, so all node *proofs* (R2 nodes AND the
    /// upstream-built base-nodes) share one circuit shape (hence one `node_shared_config`).
    pub node_target_padding_sizes: ComponentSizes,
    /// PCS config used to prove each NODE and to VERIFY the root (a node proof) in
    /// [`prove_root_verification`]. A node proof's Merkle auth-path height is
    /// `node_log_size + log_blowup`; this field carries the node-sized lifting.
    pub node_pcs_config: PcsConfig,
    /// Witness-independent precompute for the level-≥2 (node-verifying) multiverifier node circuit.
    /// Reused for every [`prove_node`] call at height ≥ 2. `None` falls back to the self-contained
    /// [`prove_circuit_assignment`] path (rebuilds tree0 each call).
    pub node_precompute: Option<Arc<CircuitPrecompute>>,
    /// Node-node fold arity `k` in effect (from [`TopologyConfig::fold_arity`]). Carried on the config
    /// so every config-threaded fold fn (`recursive_aggregate_prove`, `prove_node`, `prove_short_node`,
    /// the unpacker, the root-consistency check) reads the SAME `k` — the single source of truth the
    /// out-of-circuit unpacker and the in-circuit node hash both depend on for byte-identity.
    pub fold_arity: usize,

    // ---- LEAF/R1/R2 topology extras ([`FoldMode::LeafR1R2`] only) --------------------------------
    // These reintroduce the PRE-BASE-FANNING three-tier bottom layer (standalone leaf → level-0
    // leaf-verifying R1 node → shared R2 up-tree fold) as a PARALLEL path. They are `None` under
    // [`FoldMode::BaseFanning`] (the base-fanning fields above carry that mode's bottom layer) and
    // `Some` under [`FoldMode::LeafR1R2`], populated by gate-air-leaf's `derive_aggregate_config`.
    // The shared height-≥2 R2 fold above the bottom layer uses ONLY the base-fanning fields above
    // (`node_shared_config`, `node_preprocessed_root`, `node_precompute`), so it is untouched.
    /// Verifier/prover config for a level-1 node whose CHILDREN are LEAVES ([`FoldMode::LeafR1R2`]).
    /// Built from the leaf circuit's preprocessed shape (`shared_config_for_leaf`); also deserializes
    /// the leaf proofs a level-1 (R1) node verifies. `None` under base-fanning.
    pub leaf_shared_config: Option<SharedConfig>,
    /// **R1** — the preprocessed root of a level-1 (leaf-verifying) multiverifier node
    /// ([`FoldMode::LeafR1R2`]). Reported by every height-1 leaf-node to its R2 parent. `None` under
    /// base-fanning.
    pub level1_preprocessed_root: Option<HashValue<QM31>>,
    /// The trusted preprocessed root of the leaf circuit (same AIR for every leaf,
    /// [`FoldMode::LeafR1R2`]). The unpacker uses this single constant for *all* leaves. `None` under
    /// base-fanning (base-fanning uses `base_preprocessed_root` for its bases instead).
    pub leaf_preprocessed_root: Option<HashValue<QM31>>,
    /// Padding targets applied to every LEAF's trace — the leaf's OWN target (~2^20), decoupled from
    /// the node size so `t_leaf` is pinned independent of `FOLD_ARITY` ([`FoldMode::LeafR1R2`]).
    /// `None` under base-fanning.
    pub leaf_target_padding_sizes: Option<ComponentSizes>,
    /// PCS config used to prove each LEAF (and to describe the leaf proof shape a level-1 node
    /// verifies) ([`FoldMode::LeafR1R2`]). Leaf lifting ~24 (below the node's ~25). `None` under
    /// base-fanning.
    pub leaf_pcs_config: Option<PcsConfig>,
    /// Witness-independent precompute for the level-1 (leaf-verifying) multiverifier node circuit,
    /// reused for every [`prove_leaf_or_short`] full-`k` call ([`FoldMode::LeafR1R2`]). `None` under
    /// base-fanning (or `GATE_AIR_NO_PRECOMPUTE`).
    pub level1_precompute: Option<Arc<CircuitPrecompute>>,
    /// Witness-independent precompute for the leaf circuit, reused for every `prove_gate_air_leaf`
    /// call ([`FoldMode::LeafR1R2`]). `None` under base-fanning (or `GATE_AIR_NO_PRECOMPUTE`).
    pub leaf_precompute: Option<Arc<CircuitPrecompute>>,
}

/// Witness-independent proving precompute for one fixed circuit shape: its preprocessed circuit, the
/// twiddles, and the committed preprocessed (tree0) commitment tree, plus a shared column pool.
///
/// The preprocessed trace, its interpolation, and its Merkle commitment depend only on the circuit's
/// gate structure (constants/multiplicities), not on the witness, so for the recursion's repeated
/// fixed shapes (the multiverifier node, the leaf) they are computed once here and reused across all
/// proves via [`prove_circuit_with_precompute`] — host-resident on the [`SimdBackend`] and shared
/// (read-only) across the [`PoolSet`] workers via `Arc`.
pub struct CircuitPrecompute {
    /// The fixed preprocessed circuit (preprocessed trace + structural params) for this shape.
    pub preprocessed: PreprocessedCircuit,
    /// Twiddles sized for this shape's `trace_log_size + max(log_blowup, 1)` (the prove's largest
    /// domain), reused for both this tree and the per-proof base/interaction interpolation.
    pub twiddles: TwiddleTree<SimdBackend>,
    /// The committed preprocessed (tree0) commitment tree for this shape.
    pub tree: CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>,
    /// Shared memory pool for the prover's SIMD columns.
    pub base_column_pool: BaseColumnPool<SimdBackend>,
    /// PCS config for proving this shape, with `lifting_log_size` pinned to the cached tree's
    /// `trace_log_size + log_blowup` (so [`prove_circuit_with_precompute`] uses the same domain the
    /// cached tree was committed over).
    pub pcs_config: PcsConfig,
}

impl CircuitPrecompute {
    /// Builds the precompute for a fixed `preprocessed` circuit shape at `log_blowup_factor`,
    /// mirroring exactly what [`prove_circuit_assignment`] would build internally (same column order,
    /// `store_polynomials_coefficients = true`, `lifting_log_size = trace_log_size + log_blowup`,
    /// twiddles over `trace_log_size + max(log_blowup, 1)`).
    ///
    /// SOUNDNESS GUARD: asserts once, at build time, that the freshly committed tree's root equals
    /// the already-trusted `expected_root`. Because every later prove reuses this same tree, this one
    /// check transfers the trust in `expected_root` to all of them; a mismatch (wrong column order /
    /// blowup / shape) aborts before any proof is produced.
    ///
    /// `pcs_config` is the prove config for this shape (pow/n_queries/blowup); its `lifting_log_size`
    /// is (re)pinned to `trace_log_size + log_blowup` to match the cached tree.
    pub fn new(
        preprocessed: PreprocessedCircuit,
        pcs_config: PcsConfig,
        expected_root: HashValue<QM31>,
    ) -> Self {
        let log_blowup_factor = pcs_config.fri_config.log_blowup_factor;
        let trace_log_size = preprocessed.trace_log_size;
        let lifting_log_size = trace_log_size + log_blowup_factor;
        let pcs_config = PcsConfig {
            lifting_log_size: Some(lifting_log_size),
            ..pcs_config
        };
        let base_column_pool = BaseColumnPool::<SimdBackend>::new();

        // Match `prove_circuit_assignment`'s twiddle domain: max(blowup, composition degree bound=1).
        let twiddles = SimdBackend::precompute_twiddles(
            CanonicCoset::new(trace_log_size + log_blowup_factor.max(1))
                .circle_domain()
                .half_coset,
        );

        let preprocessed_trace = preprocessed.preprocessed_trace.get_trace::<SimdBackend>();
        let preprocessed_trace_polys =
            SimdBackend::interpolate_columns(preprocessed_trace, &twiddles);
        let tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
            preprocessed_trace_polys,
            log_blowup_factor,
            &twiddles,
            true,
            Some(lifting_log_size),
            &base_column_pool,
        );

        let root: HashValue<QM31> = tree.commitment.root().into();
        assert_eq!(
            root, expected_root,
            "precomputed preprocessed (tree0) root must equal the trusted preprocessed_root \
             (column order / log_blowup / shape mismatch)"
        );

        Self {
            preprocessed,
            twiddles,
            tree,
            base_column_pool,
            pcs_config,
        }
    }
}

/// Result of folding the tree.
pub struct AggregateOutput {
    /// The single root proof, with its preprocessed root and output values.
    pub root: TreeProof,
    /// Number of recursion levels above the leaves (the level loop's `k`-ary depth over `N`).
    pub n_levels: usize,
}

/// A fixed set of rayon thread pools for partitioning prove work across the cores of a *single*
/// machine.
///
/// Each prove already saturates rayon's default global pool (stwo's NTT/Merkle/FRI loops fan over
/// all logical CPUs), so running independent proves on the *same* pool just makes them contend. A
/// [`PoolSet`] of `K` pools with `M` threads each lets `K` proves run concurrently, one per pool,
/// each confined to its own `M` cores (via [`ThreadPool::install`]) — turning the tree's
/// independent leaves / sibling nodes into real single-machine speedup when per-prove scaling
/// plateaus below the full core count.
///
/// Build it once and reuse it for every level (pool creation spawns OS threads, so it is not free).
pub struct PoolSet {
    pools: Vec<Arc<ThreadPool>>,
}

impl PoolSet {
    /// Creates `n_pools` pools of `threads_per_pool` worker threads each. On a 96-core machine with
    /// a measured sweet spot of 48 threads/prove, use `PoolSet::new(2, 48)`.
    pub fn new(n_pools: usize, threads_per_pool: usize) -> Self {
        let pools = (0..n_pools.max(1))
            .map(|_| {
                Arc::new(
                    rayon::ThreadPoolBuilder::new()
                        .num_threads(threads_per_pool)
                        .build()
                        .expect("build rayon pool"),
                )
            })
            .collect();
        Self { pools }
    }

    /// Number of pools (the max concurrency this set can run).
    pub fn n_pools(&self) -> usize {
        self.pools.len()
    }

    /// Runs `jobs` across the pools, preserving input order. Jobs are assigned round-robin to pools
    /// and the pools run concurrently, so up to `n_pools()` jobs are in flight at once; each job's
    /// internal rayon work runs on its assigned pool. A single job runs on the global pool (all
    /// cores) — there is nothing to run alongside it, so it should use the whole machine.
    pub fn map<T, F>(&self, jobs: Vec<F>) -> Vec<T>
    where
        F: FnOnce() -> T + Send,
        T: Send,
    {
        if jobs.len() <= 1 {
            return jobs.into_iter().map(|f| f()).collect();
        }
        let k = self.pools.len();
        let mut buckets: Vec<Vec<(usize, F)>> = (0..k).map(|_| Vec::new()).collect();
        for (i, f) in jobs.into_iter().enumerate() {
            buckets[i % k].push((i, f));
        }
        let n: usize = buckets.iter().map(Vec::len).sum();
        let mut slots: Vec<Option<T>> = (0..n).map(|_| None).collect();
        std::thread::scope(|s| {
            let handles: Vec<_> = buckets
                .into_iter()
                .zip(self.pools.iter())
                .map(|(bucket, pool)| {
                    s.spawn(move || {
                        bucket
                            .into_iter()
                            .map(|(i, f)| (i, pool.install(f)))
                            .collect::<Vec<(usize, T)>>()
                    })
                })
                .collect();
            for h in handles {
                for (i, r) in h.join().expect("pool job panicked") {
                    slots[i] = Some(r);
                }
            }
        });
        slots.into_iter().map(Option::unwrap).collect()
    }
}

/// The arities of the base-fanning nodes over `n_bases` bases, left-to-right — a deterministic
/// function of the public base count `N` and the base-fanning arity `b` (SOUNDNESS: the topology is
/// public, never prover-chosen).
///
/// Each group of `b` (plus a short trailing group of the `n_bases % b` remainder, if any) becomes one
/// base-node (proved upstream in gate-air-leaf; reconstructed in the unpacker). Contiguous groups,
/// left-to-right, each an arity in `1..=b`:
///   - `n_bases <= b`: one group of arity `n_bases`.
///   - `n_bases > b`: `n_bases / b` groups of arity `b`, then (if `r = n_bases % b > 0`) one short
///     group of arity `r`.
///
/// A short (or even lone, `r == 1`) trailing group is fine: a base-node wrapping `m < b` bases is
/// just a smaller base-node of a distinct (public, arity-derived) shape `R_base'(m)`; unlike the old
/// leaf/R1 decoupling there is no lone-child hazard (every base-node's OWN proof pads to the common
/// node shape, so R2 verifies them all identically). The single source of truth for how bases bundle
/// into base-nodes: gate-air-leaf proves base-nodes with exactly these groups, and the unpacker
/// reconstructs them with exactly these groups.
///
/// # Panics
/// If `n_bases == 0` or `b < 1`.
pub fn base_fan_group_sizes(n_bases: usize, b: usize) -> Vec<usize> {
    assert!(n_bases >= 1, "base_fan_group_sizes needs n_bases >= 1");
    assert!(b >= 1, "base_fan_arity b must be >= 1");
    if n_bases <= b {
        return vec![n_bases];
    }
    let full = n_bases / b;
    let r = n_bases % b;
    let mut v = vec![b; full];
    if r > 0 {
        v.push(r);
    }
    v
}

/// Folds `base_nodes` (each a height-1 base-fanning-node proof, reported root `R_base`, proved
/// UPSTREAM in gate-air-leaf) into a single root proof by repeatedly proving `FOLD_ARITY`-to-1
/// multiverifier nodes.
///
/// Under base-fanning the bottom of the tree — verifying `b` bases per base-node — is already done
/// before this is called, so this is JUST the classic group+carry node-node fold over the base-nodes
/// (every base-node is height 1; the produced R2 nodes are height ≥ 2). Any `M >= 1` base-nodes:
///   - `M == 1`: the lone base-node IS the root (no further fold).
///   - `M >= 2`: group the leading full-`k` runs into exactly-`k` node-verifying (R2) nodes and carry
///     the `< k` remainder up unchanged; the first level to reach `2..=k` entries folds whole into
///     the (possibly short) root. Every internal node-node is exactly-`k` (shares `node_precompute` /
///     R2); the root may be short (arity `root_arity(M)`), proved via [`prove_short_node`].
///
/// Sibling groups at each level are independent and are proved concurrently across `pools` (a lone
/// group — e.g. the last fold step — runs on the full machine).
///
/// # Panics
/// If `base_nodes` is empty.
pub fn recursive_aggregate_prove(
    base_nodes: Vec<TreeProof>,
    config: &AggregateConfig,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!base_nodes.is_empty(), "need at least one base-node");
    // Fold arity `k`, threaded via the config (the single source of truth shared with the unpacker).
    let k = config.fold_arity;

    // M == 1: the lone base-node is itself the root (no fold). Its height is 1.
    if base_nodes.len() == 1 {
        return AggregateOutput {
            root: base_nodes.into_iter().next().unwrap(),
            n_levels: 1,
        };
    }

    // Seed the fold with the base-nodes at height 1. A node's height is `max(child heights) + 1` —
    // byte-identical to `build_fold_topology`'s per-task `height`, which selects R2 (height ≥ 2,
    // verifies nodes). No R_base node is ever built here (base-nodes arrive already proved).
    let mut level: Vec<(usize, TreeProof)> =
        base_nodes.into_iter().map(|bn| (1usize, bn)).collect();

    // --- group+carry over NODES only (all base-nodes / R2 nodes share the node proof shape). ---
    while level.len() > 1 {
        if level.len() <= k {
            // Terminal step: fold the whole (2..=k) level into the single (possibly short) root.
            let height = level.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children: Vec<TreeProof> = level.into_iter().map(|(_, p)| p).collect();
            let root = prove_short_node(&children, config, height);
            return AggregateOutput {
                root,
                n_levels: height,
            };
        }
        // `len > k`: carry the trailing `< k` remainder up unchanged; group the leading full-k runs
        // into exactly-k internal nodes. Prove the groups concurrently across the pools.
        let remainder = level.len() % k;
        let carry: Vec<(usize, TreeProof)> = level.split_off(level.len() - remainder);
        // Consume `level` into exactly-k groups, computing each group's height (max child + 1)
        // before moving its proofs into a prove closure — no proof is cloned.
        let mut groups: Vec<(usize, Vec<TreeProof>)> = Vec::with_capacity(level.len() / k);
        let mut iter = level.into_iter().peekable();
        while iter.peek().is_some() {
            let group: Vec<(usize, TreeProof)> = iter.by_ref().take(k).collect();
            let height = group.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children: Vec<TreeProof> = group.into_iter().map(|(_, p)| p).collect();
            groups.push((height, children));
        }
        let jobs: Vec<_> = groups
            .iter()
            .map(|(height, children)| move || (*height, prove_node(children, config, *height)))
            .collect();
        let mut next: Vec<(usize, TreeProof)> = pools.map(jobs);
        next.extend(carry);
        level = next;
    }

    // M >= 2 always folds to a root above (the loop's terminal step returns it); reaching here means
    // the loop exited with a single carried entry, which is that root.
    let (height, root) = level.into_iter().next().unwrap();
    AggregateOutput {
        root,
        n_levels: height,
    }
}

/// The arity of the ROOT node of the fold tree over `m` base-nodes — a deterministic function of the
/// public base-node count `M` (SOUNDNESS: the root shape is public, never prover-chosen).
///
/// The classic group+carry loop folds the `M` base-NODES (levels with `> k` entries carry the `< k`
/// remainder and emit `len / k` exactly-`k` node-nodes; the first level to reach `2..=k` folds whole
/// into the root). Returns that terminal size (`∈ 2..=k`). For `m == 1` there is no fold (returns
/// `1`, the lone base-node is the root).
pub fn root_arity(m_base_nodes: usize, k: usize) -> usize {
    if m_base_nodes == 1 {
        return 1;
    }
    let mut len = m_base_nodes;
    while len > k {
        len = len / k + len % k;
    }
    len
}

/// A reference to one input of a streaming fold node: either a base-node proof (by base-node index,
/// the canonical arrival order) or the output of an earlier fold node (by node index).
#[derive(Clone, Copy)]
enum Child {
    Leaf(usize),
    Node(usize),
}

/// One fold in the fixed tree: prove an R2 node over `children` base-nodes/nodes, children
/// left-to-right. An internal task has `children.len() == FOLD_ARITY`; the single ROOT task may be
/// short (`2..=k`). The arity is `children.len()` and the level is `NodeLevel::from_height(height)`
/// (always `VerifiesNodes` here — every fold task is height ≥ 2, verifying base-nodes/nodes).
struct FoldTask {
    children: Vec<Child>,
    /// Height above the bases of this node's output (bases are height 0; base-nodes are height 1;
    /// the first fold produced here is height 2).
    height: usize,
}

/// Computes the FIXED node-node fold topology for `m_base_nodes` base-nodes, decided up front and
/// independent of completion order, **byte-identical** to [`recursive_aggregate_prove`]'s level loop.
///
/// The base-nodes are height 1 (proved upstream); this runs the group+carry loop over them: while a
/// level has `> k` entries it groups the leading full-`k` runs left-to-right into `prove_node(group)`
/// and carries the trailing `< k` remainder up unchanged; a level of `2..=k` entries is folded whole
/// into the root. The returned `Vec<FoldTask>` is in the same order the level loop would prove them;
/// the returned [`Child`] is the root (a `Node` for `m > 1`, else `Leaf(0)` = the lone base-node).
/// `Child::Leaf(i)` denotes base-node `i`. Each task's `children` order matches `prove_node`'s
/// exactly, so each node sees the same inputs as the sequential fold ⇒ same proof bytes.
fn build_fold_topology(m_base_nodes: usize, k: usize) -> (Vec<FoldTask>, Child) {
    if m_base_nodes == 1 {
        return (Vec::new(), Child::Leaf(0));
    }
    let mut tasks: Vec<FoldTask> = Vec::new();

    // Seed the level with the `m` base-nodes at height 1 (each a `Child::Leaf(i)` = base-node i).
    let mut level: Vec<(usize, Child)> = (0..m_base_nodes).map(|i| (1, Child::Leaf(i))).collect();

    // --- group+carry over NODES only (base-nodes and R2 nodes share the node proof shape). ---
    while level.len() > 1 {
        if level.len() <= k {
            // Terminal step: the whole (2..=k) level folds into the single (possibly short) root.
            let height = level.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children = level.iter().map(|(_, c)| *c).collect();
            let idx = tasks.len();
            tasks.push(FoldTask { children, height });
            return (tasks, Child::Node(idx));
        }
        let remainder = level.len() % k;
        let carry: Vec<(usize, Child)> = level.split_off(level.len() - remainder);
        let mut next: Vec<(usize, Child)> = Vec::with_capacity(level.len() / k + remainder);
        for group in level.chunks(k) {
            let height = group.iter().map(|(h, _)| *h).max().unwrap() + 1;
            let children = group.iter().map(|(_, c)| *c).collect();
            let idx = tasks.len();
            tasks.push(FoldTask { children, height });
            next.push((height, Child::Node(idx)));
        }
        // Carry the `< k` remainder up unchanged (all NODES now — safe under decoupling).
        next.extend(carry);
        level = next;
    }
    (tasks, level[0].1)
}

/// Streaming variant of [`recursive_aggregate_prove`]: folds base-nodes as they arrive over a
/// channel, dispatching each fold to a [`PoolSet`] worker the instant all its children are ready — so
/// the node-node fold runs concurrently with (and overlaps) the upstream base-node producer feeding
/// `rx`.
///
/// This exists so the GPU base-proving + base-node producer can overlap with the CPU fold consumer
/// (see the `GATE_AIR_PIPELINE` path in gate-air-leaf). The producer is modelled as a stream of
/// completed base-node proofs sent over `rx` in **canonical order** (base-node `i` is the `i`-th
/// `recv()`), NOT as GPU calls — this crate stays leaf-type-agnostic.
///
/// BYTE-IDENTITY: the result is byte-identical to [`recursive_aggregate_prove`] for the same ordered
/// base-nodes. The topology is FIXED up front by [`build_fold_topology`] (group+carry over the `m`
/// base-nodes; e.g. at k=8 the m=9 root is `node([node([0..7]), node([7..9])])`) and does not depend
/// on completion order; every [`FoldTask`] sees the same ordered children the sequential fold gives
/// its matching `prove_node`/`prove_short_node`. Because those are pure functions of their ordered
/// children, identical topology + identical per-node inputs ⇒ identical root proof and
/// `recursion_fingerprint`, which the [`prove_root_verification`] unpacker still binds.
///
/// Streaming schedule: one coordinator owns the dataflow state; `pools.n_pools()` workers (one per
/// pool) pull ready folds and run the fold via [`ThreadPool::install`]. As base-nodes arrive on `rx`,
/// any fold whose `k` children are now available becomes ready; a fold completing makes its parent's
/// child available in turn. Up to `n_pools()` folds run at once while later base-nodes are still
/// being produced.
///
/// Consumes exactly `m_base_nodes` from `rx` in arrival order. Returns the same [`AggregateOutput`]
/// as the level loop. For `m_base_nodes == 1` returns the single base-node as root with
/// `n_levels = 1` (the base-node itself is height 1).
///
/// # Panics
/// If `m_base_nodes == 0`, or if `rx` yields fewer than `m_base_nodes` entries.
pub fn recursive_aggregate_prove_streaming(
    rx: std::sync::mpsc::Receiver<TreeProof>,
    m_base_nodes: usize,
    config: &AggregateConfig,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(m_base_nodes >= 1, "need at least one base-node");
    // Fold arity `k`, threaded via the config (must match the sequential path + the unpacker).
    let k = config.fold_arity;

    let (tasks, root_ref) = build_fold_topology(m_base_nodes, k);

    if m_base_nodes == 1 {
        let root = rx.recv().expect("streaming fold: missing base-node 0");
        return AggregateOutput { root, n_levels: 1 };
    }

    // For each task, count its not-yet-available children and record which task consumes each
    // produced value, so completing a fold (or receiving a leaf) can decrement the right parent.
    //   parent_of[Leaf i] / parent_of_node[Node j] = Some((task_idx, slot)), slot = child position
    //   in the task's `children` (left-to-right), so inputs reassemble in the fold's exact order.
    let mut leaf_parent: Vec<Option<(usize, usize)>> = vec![None; m_base_nodes];
    let mut node_parent: Vec<Option<(usize, usize)>> = vec![None; tasks.len()];
    let mut pending: Vec<usize> = vec![0; tasks.len()];
    let arity: Vec<usize> = tasks.iter().map(|t| t.children.len()).collect();
    for (ti, t) in tasks.iter().enumerate() {
        for (slot, ch) in t.children.iter().enumerate() {
            pending[ti] += 1;
            match ch {
                Child::Leaf(i) => leaf_parent[*i] = Some((ti, slot)),
                Child::Node(j) => node_parent[*j] = Some((ti, slot)),
            }
        }
    }

    // Dataflow state shared between the coordinator and the worker threads.
    struct State {
        // Resolved child inputs for each task (one `Option` slot per child, left-to-right), filled
        // as children become available.
        inputs: Vec<Vec<Option<TreeProof>>>,
        pending: Vec<usize>,
        ready: std::collections::VecDeque<usize>,
        done: usize,
        // The root proof, captured when the root fold (the one with no parent) completes.
        root: Option<TreeProof>,
    }
    let n_tasks = tasks.len();
    let state = std::sync::Mutex::new(State {
        inputs: arity.iter().map(|&k| (0..k).map(|_| None).collect()).collect(),
        pending,
        ready: std::collections::VecDeque::new(),
        done: 0,
        root: None,
    });
    // Signalled when a fold becomes ready or all folds are done (so idle workers wake up).
    let cv = std::sync::Condvar::new();

    // Records that `proof` is the value of `child`, wiring it into the consuming task and enqueuing
    // that task once all its child inputs are present. Returns nothing; mutates `st` under its lock.
    let deliver = |st: &mut State, parent: Option<(usize, usize)>, proof: TreeProof| {
        if let Some((ti, slot)) = parent {
            st.inputs[ti][slot] = Some(proof);
            st.pending[ti] -= 1;
            if st.pending[ti] == 0 {
                st.ready.push_back(ti);
            }
        }
        // No parent ⇒ this is the root value; the root is always a Node here (n_leaves > 1).
    };

    let n_workers = pools.n_pools().max(1);
    std::thread::scope(|s| {
        // Workers: one per pool. Each pulls a ready task, proves it on its pool's cores, then
        // delivers the result to the parent and signals.
        for pool in pools.pools.iter().take(n_workers) {
            let state = &state;
            let cv = &cv;
            let deliver = &deliver;
            let node_parent = &node_parent;
            let tasks = &tasks;
            s.spawn(move || {
                loop {
                    let ti = {
                        let mut st = state.lock().unwrap();
                        loop {
                            if let Some(ti) = st.ready.pop_front() {
                                break ti;
                            }
                            if st.done == n_tasks {
                                return;
                            }
                            st = cv.wait(st).unwrap();
                        }
                    };
                    // Take ownership of this task's resolved inputs and prove off-lock. All child
                    // `TreeProof`s are `take()`n out of `inputs` here, so once this node's result is
                    // delivered to its parent the children have no remaining references and are freed
                    // (dropped when `children` leaves scope). Nothing retains proved node proofs:
                    // peak host memory therefore holds only the N leaves (owned by the caller for
                    // `prove_root_verification`) + the O(log_k N) in-flight fold path, never all the
                    // node proofs.
                    let children: Vec<TreeProof> = {
                        let mut st = state.lock().unwrap();
                        st.inputs[ti]
                            .iter_mut()
                            .map(|slot| slot.take().unwrap())
                            .collect()
                    };
                    // Dispatch EXACTLY as the sequential fold, so the two paths stay byte-identical.
                    // Every fold task here is a node-node fold (height ≥ 2, verifies base-nodes/nodes
                    // ⇒ R2) — base-nodes arrive already proved:
                    //   - the ROOT (no parent) ⇒ `prove_short_node` (the self-contained recompute
                    //     path) even at arity `FOLD_ARITY` — the sequential terminal step always uses
                    //     it, so the streaming root must too;
                    //   - every non-root internal node: full-`k` ⇒ `prove_node` (precompute, fixed
                    //     R2), short (impossible for non-root) ⇒ `prove_short_node`.
                    let is_root = node_parent[ti].is_none();
                    let height = tasks[ti].height;
                    let result = pool.install(|| {
                        if is_root {
                            prove_short_node(&children, config, height)
                        } else if children.len() == k {
                            prove_node(&children, config, height)
                        } else {
                            prove_short_node(&children, config, height)
                        }
                    });
                    {
                        let mut st = state.lock().unwrap();
                        match node_parent[ti] {
                            Some(parent) => deliver(&mut st, Some(parent), result),
                            None => st.root = Some(result), // the root fold (no parent)
                        }
                        st.done += 1;
                        // Wake idle workers: either a new fold is ready, or all folds are done.
                        cv.notify_all();
                    }
                }
            });
        }

        // Coordinator: drain base-nodes in canonical order, delivering each to its consumer. A
        // base-node that completes a fold's inputs enqueues it; workers pick it up immediately, so
        // folds overlap with the still-arriving later base-nodes.
        for &parent in &leaf_parent {
            let base_node = rx
                .recv()
                .expect("streaming fold: fewer base-nodes than m_base_nodes");
            let mut st = state.lock().unwrap();
            deliver(&mut st, parent, base_node);
            cv.notify_all();
        }
    });

    // All folds complete; pull the root the root fold captured.
    let root_idx = match root_ref {
        Child::Node(j) => j,
        Child::Leaf(_) => unreachable!("m_base_nodes > 1 ⇒ root is a fold node"),
    };
    let root = state
        .into_inner()
        .unwrap()
        .root
        .expect("root not produced");
    AggregateOutput {
        root,
        n_levels: tasks[root_idx].height,
    }
}

// =================================================================================================
// LEAF/R1/R2 bottom layer ([`FoldMode::LeafR1R2`], PARALLEL to base-fanning) — restored from the
// pre-base-fanning topology (proving-utils 79eaa0b). Confined to the BOTTOM layer + config +
// unpacker; the shared height-≥2 R2 up-tree fold (`recursive_aggregate_prove`, `prove_node`,
// `prove_short_node`, `build_node_context`, `build_fold_topology`) is UNCHANGED and reused by both
// modes. Under this mode the caller proves standalone leaves upstream; the level-0 layer below
// consumes ALL leaves into height-1 leaf-verifying (R1) nodes, then delegates the up-tree fold to the
// shared base-fanning path (a height-1 leaf-node's OWN proof has the same shape as a base-node's, so
// R2 verifies them identically).
// =================================================================================================

/// A node's tree level, which selects its shape under leaf↔node padding decoupling
/// ([`FoldMode::LeafR1R2`]). A **level-1** node verifies `FOLD_ARITY` LEAVES (child config
/// `leaf_shared_config`) and reports **R1** (`level1_preprocessed_root`); a **level-≥2** node verifies
/// NODES (child config `node_shared_config`) and reports **R2** (`node_preprocessed_root`). The level
/// is fixed by the public topology (`FoldTask::height`), never prover-chosen. Only the leaf-node
/// bottom layer uses `VerifiesLeaves`; the shared up-tree fold is always `VerifiesNodes`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeLevel {
    /// Children are leaves (node height == 1).
    VerifiesLeaves,
    /// Children are nodes (node height >= 2).
    VerifiesNodes,
}

impl NodeLevel {
    /// The node level for a node of the given height above the leaves (leaves are height 0).
    fn from_height(height: usize) -> Self {
        if height == 1 {
            NodeLevel::VerifiesLeaves
        } else {
            NodeLevel::VerifiesNodes
        }
    }

    /// The child-verifier config: `leaf_shared_config` (R1) for leaf children, `node_shared_config`
    /// (R2) for node children. Panics if the leaf config is absent (i.e. not a `LeafR1R2` config).
    fn shared_config(self, config: &AggregateConfig) -> &SharedConfig {
        match self {
            NodeLevel::VerifiesLeaves => config
                .leaf_shared_config
                .as_ref()
                .expect("leaf_shared_config required for a leaf-verifying (R1) node — LeafR1R2 mode"),
            NodeLevel::VerifiesNodes => &config.node_shared_config,
        }
    }

    /// The trusted preprocessed root a node of this level reports (R1 vs R2).
    fn preprocessed_root(self, config: &AggregateConfig) -> HashValue<QM31> {
        match self {
            NodeLevel::VerifiesLeaves => config
                .level1_preprocessed_root
                .clone()
                .expect("level1_preprocessed_root required for an R1 node — LeafR1R2 mode"),
            NodeLevel::VerifiesNodes => config.node_preprocessed_root.clone(),
        }
    }

    /// The witness-independent precompute for this level's node circuit, if built.
    fn precompute(self, config: &AggregateConfig) -> Option<&Arc<CircuitPrecompute>> {
        match self {
            NodeLevel::VerifiesLeaves => config.level1_precompute.as_ref(),
            NodeLevel::VerifiesNodes => config.node_precompute.as_ref(),
        }
    }
}

/// The arities of the LEVEL-0 (leaf-verifying) nodes for `n_leaves`, left-to-right — a deterministic
/// function of the public `N` and fold arity `k` ([`FoldMode::LeafR1R2`]; SOUNDNESS: public topology,
/// never prover-chosen).
///
/// LEAF↔NODE DECOUPLING FIX: leaves (lift24) and nodes (lift25) have different proof shapes, so a
/// carried-up leaf landing under a height-≥2 (node-verifying, lift25) fold panics the in-circuit
/// Merkle height check. To prevent that, ALL leaves are consumed at level 0 into height-1 leaf-nodes.
/// Contiguous groups, each an arity in `2..=k`, NEVER a lone leaf:
///   - `N <= k`: one group of arity `N` (that node IS the root).
///   - `N > k`, `r = N % k`: `r == 0` -> `N/k` full-`k`; `r >= 2` -> `N/k` full-`k` then one arity-`r`
///     group; `r == 1` -> `(N/k - 1)` full-`k` then arity-`(k-1)` and arity-`2` groups (the `k+1`
///     trailing leaves split so every arity stays in `2..=k` with no lone leaf).
///
/// # Panics
/// If `n_leaves < 2` (callers handle the lone-leaf no-fold case before calling this).
fn level0_group_sizes(n_leaves: usize, k: usize) -> Vec<usize> {
    assert!(n_leaves >= 2, "level0_group_sizes needs n_leaves >= 2");
    if n_leaves <= k {
        return vec![n_leaves];
    }
    let full = n_leaves / k;
    let r = n_leaves % k;
    match r {
        0 => vec![k; full],
        1 => {
            let mut v = vec![k; full - 1];
            v.push(k - 1);
            v.push(2);
            v
        }
        _ => {
            let mut v = vec![k; full];
            v.push(r);
            v
        }
    }
}

/// Builds and pads (to the common `node_target_padding_sizes`) the multiverifier circuit that verifies
/// `children`, using the child-verifier config for the node's `level` ([`FoldMode::LeafR1R2`]).
/// Distinct from the shared `build_node_context` (always R2) — this selects the child config by level.
fn build_leaf_node_context(
    children: &[TreeProof],
    config: &AggregateConfig,
    level: NodeLevel,
) -> FinalizedContext<QM31> {
    let inputs: Vec<MultiverifierInput<QM31>> = children.iter().map(child_input).collect();
    let mut context = build_multiverifier_circuit::<QM31>(inputs, level.shared_config(config));
    pad_to_targets(&mut context, config.node_target_padding_sizes.clone());
    context.validate_circuit();
    context
}

/// Proves one LEVEL-0 (height-1, leaf-verifying) node over `children` leaves ([`FoldMode::LeafR1R2`]):
/// full-`k` groups go through the R1 precompute/`prove_circuit_assignment` path (reporting R1); short
/// groups (`2..=k-1`) recompute their real root R1'(m). `height` is always 1.
fn prove_leaf_or_short(
    children: &[TreeProof],
    config: &AggregateConfig,
    height: usize,
) -> TreeProof {
    debug_assert_eq!(height, 1, "level-0 leaf nodes are always height 1");
    let level = NodeLevel::VerifiesLeaves;
    let _t_node = std::time::Instant::now();
    let full = children.len() == config.fold_arity;
    let mut context = build_leaf_node_context(children, config, level);

    let (preprocessed_root_reported, circuit_proof) = if full {
        // Full-`k` leaf-node: reuse the R1 precompute (or the self-contained path) and report the
        // fixed R1.
        let cp = match level.precompute(config) {
            Some(pc) => prove_with_precompute(context.values(), pc),
            None => {
                let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
                prove_circuit_assignment(
                    context.values(),
                    &preprocessed,
                    &BaseColumnPool::<SimdBackend>::new(),
                    config.node_pcs_config,
                )
            }
        };
        (level.preprocessed_root(config), cp)
    } else {
        // Short leaf group: distinct shape, rebuild tree0 and report the recomputed real root R1'(m).
        let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
        let root =
            preprocessed_root(&preprocessed, config.node_pcs_config.fri_config.log_blowup_factor);
        let cp = prove_circuit_assignment(
            context.values(),
            &preprocessed,
            &BaseColumnPool::<SimdBackend>::new(),
            config.node_pcs_config,
        );
        (root, cp)
    };
    let circuit_proof = circuit_proof.expect("leaf-node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);
    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("leaf-node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_leaf_node(arity={},h={height})={:.3}s",
        children.len(),
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: preprocessed_root_reported,
        output_values,
    }
}

/// Folds standalone `leaves` into a single root proof ([`FoldMode::LeafR1R2`]). LEVEL 0 consumes ALL
/// leaves into height-1 leaf-verifying (R1) nodes via [`level0_group_sizes`] + [`prove_leaf_or_short`]
/// (so no leaf survives above height 1), then the SHARED [`recursive_aggregate_prove`] folds those
/// height-1 leaf-nodes up the tree with the identical R2 group+carry.
///
/// `n_leaves == 1`: the lone leaf is the root (no fold, `n_levels == 0`). `N <= k`: the single level-0
/// leaf-node is the root (`n_levels == 1`), same as delegating a 1-element vec to the shared fold.
///
/// # Panics
/// If `leaves` is empty, or if the config lacks the `LeafR1R2` extras.
pub fn recursive_aggregate_prove_leaves(
    leaves: Vec<TreeProof>,
    config: &AggregateConfig,
    pools: &PoolSet,
) -> AggregateOutput {
    assert!(!leaves.is_empty(), "need at least one leaf");
    assert!(
        config.leaf_shared_config.is_some(),
        "recursive_aggregate_prove_leaves requires a LeafR1R2 config (leaf_shared_config present)"
    );
    let k = config.fold_arity;

    // n_leaves == 1: the lone leaf is itself the root (no fold, height 0).
    if leaves.len() == 1 {
        return AggregateOutput {
            root: leaves.into_iter().next().unwrap(),
            n_levels: 0,
        };
    }

    // --- Level 0: consume ALL leaves into height-1 leaf-verifying (R1) nodes. After this every entry
    //     is a NODE, so the shared up-tree fold sees only nodes (homogeneous, no carried leaf). ---
    let sizes = level0_group_sizes(leaves.len(), k);
    let mut leaves_iter = leaves.into_iter();
    let groups: Vec<Vec<TreeProof>> = sizes
        .iter()
        .map(|&m| leaves_iter.by_ref().take(m).collect())
        .collect();
    let jobs: Vec<_> = groups
        .iter()
        .map(|children| move || prove_leaf_or_short(children, config, 1))
        .collect();
    let leaf_nodes: Vec<TreeProof> = pools.map(jobs);

    // --- Levels ≥ 1: SHARED up-tree R2 fold over the height-1 leaf-nodes (byte-identical to the
    //     base-fanning fold over base-nodes; a lone leaf-node is returned as the root at n_levels 1). ---
    recursive_aggregate_prove(leaf_nodes, config, pools)
}

/// The preprocessed root a SHORT leaf-verifying (R1) node of the given `arity` (`2..=k-1`) reports —
/// recomputed witness-independently over `leaf_shared_config`, byte-identical to what
/// [`prove_leaf_or_short`] recomputes for the same shape ([`FoldMode::LeafR1R2`]). Pure function of
/// the public `arity`.
fn short_leaf_node_preprocessed_root(config: &AggregateConfig, arity: usize) -> HashValue<QM31> {
    let shared = NodeLevel::VerifiesLeaves.shared_config(config);
    let pp = node_preprocessed_from_shared(
        shared,
        config.node_target_padding_sizes.clone(),
        arity,
    );
    preprocessed_root(&pp, config.node_pcs_config.fri_config.log_blowup_factor)
}

/// The bottom-level input to the unpacker under [`FoldMode::LeafR1R2`]: the ordered standalone leaves
/// (each a proved height-0 leaf `TreeProof` reporting `leaf_preprocessed_root`).
pub struct LeafBottom {
    /// The standalone leaves in canonical order (leaf `i` is shard `i`).
    pub leaves: Vec<TreeProof>,
}

/// The published root-verification proof.
pub struct RootVerificationOutput {
    /// The root verification's STARK proof — the single public artifact of the whole aggregation.
    pub proof: Proof<QM31>,
    /// The unpacked leaf outputs, in tree-position order — the result the proof exposes.
    pub leaf_outputs: Vec<[QM31; N_RESERVED]>,
    /// The root-verification circuit's trace log size (from which its PCS config was derived).
    pub trace_log_size: u32,
}

/// Builds and proves the **root verification** — the only published, only zk-blinded proof.
///
/// In-circuit it (1) reconstructs the root multiverifier statement and runs the STARK verifier on
/// the root proof, then (2) **unpacks**: it guesses each base's `(preprocessed_root, H_i)`,
/// reconstructs the tree's root hash via the same per-node `blake([ppR_i, outs_i] for the children)`
/// binding the nodes used — the BOTTOM level groups `b` bases into base-node hashes (binding the
/// trusted `R_base` roots `bottom.base_node_roots` and one trusted `base_preprocessed_root` for every
/// base), then LEVELS ≥ 1 fold the base-nodes with `node_preprocessed_root` (R2) — `eq`-binds the
/// reconstructed root to the verified root output, and (3) emits the per-base `H_i` as public
/// outputs. The unpack is **O(N)** — it touches every base — and using one `base_preprocessed_root`
/// for all bases forces them to share the base AIR.
///
/// `bottom.bases` must be the same ordered bases the upstream base-nodes were proved over, and `root`
/// the root [`recursive_aggregate_prove`] returned over those base-nodes; the unpacker reconstructs
/// the same shape the fold built. The circuit's own prove config is derived from its actual trace
/// size.
///
/// If `zk_blind` is `Some`, the circuit is zk-blinded before proving — this is where hiding lives,
/// since this is the only published proof and its trace transitively encodes the whole tree.
pub fn prove_root_verification(
    root: &TreeProof,
    bottom: &BaseFanBottom,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_blind: Option<ZkBlind>,
) -> RootVerificationOutput {
    let n = bottom.bases.len();
    assert!(!bottom.bases.is_empty(), "need at least one base");
    let b = bottom.b;
    // Fold arity `k` (from the config) — must match the fold that built `root` + the unpacker's own
    // group+carry so the reconstructed root hash equals the verified one.
    let k = config.fold_arity;

    // Exposes every base's N_RESERVED outputs (its H_i).
    let mut context = Context::<QM31>::new(n * N_RESERVED);

    // (1) Verify the root multiverifier proof in-circuit. The root is a NODE proof, so it is
    //     verified with `node_shared_config` (the node's own shape). All node variants pad to the
    //     common `node_target_padding_sizes`, so a node proof's shape
    //     (preprocessed_column_log_sizes, n_columns, PCS) is level-independent; only the root's
    //     `preprocessed_root` (R_base for a lone-base-node root, R2 above) differs, and that is
    //     guessed here from `root.preprocessed_root`, not part of the topology.
    let circuit_config = CircuitConfig {
        // The root is a NODE proof, so it is described/verified with the node-sized PCS (node
        // lifting ~25), not the leaf PCS (~24). Using the leaf PCS here mis-sizes the Merkle
        // lifting and panics the R2 root fold.
        config: config.node_pcs_config,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: config
            .node_shared_config
            .preprocessed_column_log_sizes
            .clone(),
        preprocessed_root: root.preprocessed_root.clone(),
    };
    let statement = CircuitStatement::new(&mut context, &circuit_config, &root.output_values);
    let proof_vars = root.proof.guess(&mut context);
    verify(
        &mut context,
        &proof_vars,
        &config.node_shared_config.proof_config,
        &statement,
    );
    let root_out_vars: Vec<Var> = statement.get_output_values().to_vec();

    // (2) Unpack: reconstruct the tree root from the guessed per-base outputs and bind it to the
    //     verified root.
    //
    // Each level entry is `(height, pp_root: HashValue<Var>, outs: Vec<Var>)`, where `pp_root` is the
    // eight guessed digest words of the child's preprocessed root and `outs` is the child's
    // `N_RESERVED` output QM31 values (for a base: its H_i; for a produced node: the eight words of
    // its Blake digest, each a QM31 `(lo, hi, 0, 0)`). Guessing the pp_root here mirrors
    // `CircuitStatement::new` / `GateAirStatement::new`, which also guess the eight root words.
    let guess_pp = |context: &mut Context<QM31>, pp: &HashValue<QM31>| -> HashValue<Var> {
        pp.guess(context)
    };
    // One trusted base tree0 root for EVERY base (forces a shared base AIR): a base whose guessed
    // pp_root differs makes the reconstruction miss the verified root ⇒ REJECTED.
    let base_pp = guess_pp(&mut context, &config.base_preprocessed_root);
    // Per-base entries (height 0), each carrying `base_pp` and its guessed H_i.
    let mut base_output_vars: Vec<Vec<Var>> = Vec::with_capacity(n);
    let mut base_entries: Vec<(usize, HashValue<Var>, Vec<Var>)> = bottom
        .bases
        .iter()
        .map(|base| {
            let outs: Vec<Var> = base
                .output_values
                .iter()
                .map(|v| guess(&mut context, *v))
                .collect();
            base_output_vars.push(outs.clone());
            (0usize, base_pp.clone(), outs)
        })
        .collect();

    // The shared child-preimage hash for one ordered group of children, byte-identical to the
    // in-circuit node hash in `build_multiverifier_circuit` / `build_gate_air_base_node_circuit`:
    // per child `chain!(preprocessed_root.into_iter() [8 words], unpack_qm31s_to_u32_words(outputs))`,
    // children left-to-right, hashed with `blake2s_u32s` over `4 * n_words` bytes. THE ONE ORDERING
    // SPEC shared with the node circuits.
    let fold_hash = |context: &mut Context<QM31>,
                     group: &[(usize, HashValue<Var>, Vec<Var>)]|
     -> Vec<Var> {
        let mut preimage: Vec<U32Wrapper<Var>> = Vec::new();
        for (_, pp, outs) in group {
            let output_words = unpack_qm31s_to_u32_words(context, outs.iter().copied());
            preimage.extend(pp.iter().copied().chain(output_words));
        }
        let n_bytes = 4 * preimage.len();
        let h = blake2s_u32s(context, preimage, n_bytes);
        h.iter().map(|w| *w.get()).collect()
    };

    // `fold_group` folds one ordered group of NODES (height ≥ 1) into an R2 node (height ≥ 2),
    // guessing the SAME reported preprocessed root the prover reported for that node, selected by
    // public (height, arity): arity == k -> the fixed R2 (`node_preprocessed_root`) via `NodeLevel`;
    // arity < k (short root) -> the recomputed short-root real root via `short_node_preprocessed_root`
    // (matches `prove_short_node` byte-for-byte). A wrong selection makes the reconstructed root miss
    // the verified root ⇒ the proof is REJECTED, never accepted-invalid.
    let fold_group = |context: &mut Context<QM31>,
                      group: &[(usize, HashValue<Var>, Vec<Var>)]|
     -> (usize, HashValue<Var>, Vec<Var>) {
        let outs = fold_hash(context, group);
        let height = group.iter().map(|(h, _, _)| *h).max().unwrap() + 1;
        let reported_root = if group.len() == k {
            config.node_preprocessed_root.clone()
        } else {
            short_node_preprocessed_root(config, group.len())
        };
        let node_pp = guess_pp(context, &reported_root);
        (height, node_pp, outs)
    };

    // --- BOTTOM LEVEL: group `b` bases into height-1 base-nodes, per `base_fan_group_sizes`. Each
    //     base-node's hash is the shared fold-hash over its `b` bases; its reported root is the
    //     trusted `bottom.base_node_roots[g]` (public, arity-derived, supplied by gate-air-leaf — the
    //     unpacker cannot rebuild the gate_air base-node circuit). This replaces the old level-0
    //     leaf-consumption; above it the fold is identical (group+carry over nodes). ---
    // n == 1: a single base cannot form a base-node — the base-node was proved over >= 2 bases
    // upstream. n bases -> base_fan_group_sizes.len() base-nodes.
    let mut level: Vec<(usize, HashValue<Var>, Vec<Var>)> = {
        let sizes = base_fan_group_sizes(n, b);
        assert_eq!(
            sizes.len(),
            bottom.base_node_roots.len(),
            "base_node_roots count must equal the number of base-node groups"
        );
        let mut bases_iter = base_entries.drain(..);
        let bottom_level: Vec<(usize, HashValue<Var>, Vec<Var>)> = sizes
            .iter()
            .zip(bottom.base_node_roots.iter())
            .map(|(&m, reported_root)| {
                let group: Vec<(usize, HashValue<Var>, Vec<Var>)> =
                    (0..m).map(|_| bases_iter.next().unwrap()).collect();
                let outs = fold_hash(&mut context, &group);
                let node_pp = guess_pp(&mut context, reported_root);
                (1usize, node_pp, outs)
            })
            .collect();
        drop(bases_iter);
        bottom_level
    };

    // --- LEVELS ≥ 1: classic group+carry over NODES only (base-nodes and R2 nodes). ---
    while level.len() > 1 {
        if level.len() <= k {
            // Terminal step: fold the whole (2..=k) level into the single (possibly short) root.
            let root = fold_group(&mut context, &level);
            level = vec![root];
            break;
        }
        let remainder = level.len() % k;
        let carry: Vec<(usize, HashValue<Var>, Vec<Var>)> =
            level.split_off(level.len() - remainder);
        let mut next = Vec::with_capacity(level.len() / k + remainder);
        for group in level.chunks(k) {
            next.push(fold_group(&mut context, group));
        }
        next.extend(carry);
        level = next;
    }
    // Bind the reconstructed root's eight digest words to the verified root's eight output words.
    // The verified root's `output_values` are the eight QM31 digest words; `root_out_vars` holds
    // them directly (same encoding as `computed_root`), so the eight `eq`s are word-for-word.
    let computed_root = &level[0].2;
    for i in 0..N_RESERVED {
        eq(&mut context, computed_root[i], root_out_vars[i]);
    }

    // (3) Emit the unpacked per-base outputs (each base's H_i) as public outputs.
    let flat_outputs: Vec<Var> = base_output_vars.iter().flatten().copied().collect();
    context.set_outputs(&flat_outputs);

    // (4) Finalize, (optionally) blind, pad to power-of-two sizes, derive prove config, prove.
    //     Blinding runs before padding so the extra rows are absorbed into the padding.
    let mut context = context.finalize(false);
    context.validate_circuit();
    if let Some(zk) = zk_blind {
        add_zk_blinding(&mut context, zk.seed, zk.n_padding);
        context.validate_circuit();
    }
    pad_context(&mut context);
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let trace_log_size = preprocessed.trace_log_size;
    let pcs_config = get_pcs_config(trace_log_size, log_blowup_factor);
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
        pcs_config,
    )
    .expect("root-verification prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    // SANITY CHECK: verify the final published proof natively before returning it. Mirrors
    // `privacy_circuit_verify::verify_recursive_circuit` — the root-verification proof is a
    // `prepare_circuit_proof_for_circuit_verifier` (circuit_verifier-family) proof, so it is checked
    // with `verify_circuit(CircuitConfig, proof, CircuitPublicData)`. Every input is derived from the
    // circuit that produced this proof: the same `pcs_config`, its real output count (`n *
    // N_RESERVED` flat leaf-output wires), the just-built preprocessed trace's column log sizes, and
    // its real preprocessed root. `CircuitPublicData` is the `public_data` returned alongside the
    // proof (the flat leaf outputs). Asserts the produced proof actually verifies.
    let verify_config = CircuitConfig {
        config: pcs_config,
        n_outputs: n * N_RESERVED,
        preprocessed_column_log_sizes: preprocessed.preprocessed_trace.log_sizes(),
        preprocessed_root: preprocessed_root(&preprocessed, log_blowup_factor),
    };
    verify_circuit(
        verify_config,
        proof.clone(),
        CircuitPublicData { output_values: public_data.output_values },
    )
    .expect("root-verification proof failed to verify (final-proof sanity check)");

    RootVerificationOutput {
        proof,
        leaf_outputs: bottom.bases.iter().map(|base| base.output_values).collect(),
        trace_log_size,
    }
}

/// Builds and proves the **root verification** for [`FoldMode::LeafR1R2`] — the parallel unpacker for
/// the standalone-leaf topology. Same two phases as [`prove_root_verification`] (verify the root
/// multiverifier proof in-circuit, then reconstruct + bind the tree root and emit the leaf outputs),
/// but the BOTTOM reconstruction differs: it guesses each LEAF's `(leaf_preprocessed_root,
/// output_values)`, groups the leaves into height-1 leaf-nodes via [`level0_group_sizes`] (each
/// reporting R1 for a full-`k` group, else the recomputed short R1'(m)), then folds those up with the
/// SHARED level-≥1 R2 group+carry (byte-identical to `prove_root_verification`). Reconstructs the same
/// shape [`recursive_aggregate_prove_leaves`] folds.
///
/// `bottom.leaves` must be the same ordered leaves fed to [`recursive_aggregate_prove_leaves`], and
/// `root` the returned root. Requires a `LeafR1R2` config.
pub fn prove_root_verification_leaves(
    root: &TreeProof,
    bottom: &LeafBottom,
    config: &AggregateConfig,
    log_blowup_factor: u32,
    zk_blind: Option<ZkBlind>,
) -> RootVerificationOutput {
    let leaves = &bottom.leaves;
    let n = leaves.len();
    assert!(!leaves.is_empty(), "need at least one leaf");
    let leaf_preprocessed_root = config
        .leaf_preprocessed_root
        .clone()
        .expect("leaf_preprocessed_root required for prove_root_verification_leaves (LeafR1R2 mode)");
    // Fold arity `k` — must match the fold that built `root` + the unpacker's own group+carry.
    let k = config.fold_arity;

    // Exposes every leaf's N_RESERVED outputs.
    let mut context = Context::<QM31>::new(n * N_RESERVED);

    // (1) Verify the root multiverifier proof in-circuit (a NODE proof, node_shared_config / node PCS).
    let circuit_config = CircuitConfig {
        config: config.node_pcs_config,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: config
            .node_shared_config
            .preprocessed_column_log_sizes
            .clone(),
        preprocessed_root: root.preprocessed_root.clone(),
    };
    let statement = CircuitStatement::new(&mut context, &circuit_config, &root.output_values);
    let proof_vars = root.proof.guess(&mut context);
    verify(
        &mut context,
        &proof_vars,
        &config.node_shared_config.proof_config,
        &statement,
    );
    let root_out_vars: Vec<Var> = statement.get_output_values().to_vec();

    // (2) Unpack: reconstruct the tree root from the guessed per-leaf outputs and bind it.
    let guess_pp = |context: &mut Context<QM31>, pp: &HashValue<QM31>| -> HashValue<Var> {
        pp.guess(context)
    };
    // One trusted leaf tree0 root for EVERY leaf (forces a shared leaf AIR).
    let leaf_pp = guess_pp(&mut context, &leaf_preprocessed_root);
    let mut leaf_output_vars: Vec<Vec<Var>> = Vec::with_capacity(n);
    // Per-leaf entries (height 0), each carrying `leaf_pp` and its guessed outputs.
    let mut leaf_entries: Vec<(usize, HashValue<Var>, Vec<Var>)> = leaves
        .iter()
        .map(|l| {
            let outs: Vec<Var> = l
                .output_values
                .iter()
                .map(|v| guess(&mut context, *v))
                .collect();
            leaf_output_vars.push(outs.clone());
            (0usize, leaf_pp.clone(), outs)
        })
        .collect();

    // Shared child-preimage hash for one ordered group — byte-identical to the in-circuit node hash in
    // `build_multiverifier_circuit`.
    let fold_hash = |context: &mut Context<QM31>,
                     group: &[(usize, HashValue<Var>, Vec<Var>)]|
     -> Vec<Var> {
        let mut preimage: Vec<U32Wrapper<Var>> = Vec::new();
        for (_, pp, outs) in group {
            let output_words = unpack_qm31s_to_u32_words(context, outs.iter().copied());
            preimage.extend(pp.iter().copied().chain(output_words));
        }
        let n_bytes = 4 * preimage.len();
        let h = blake2s_u32s(context, preimage, n_bytes);
        h.iter().map(|w| *w.get()).collect()
    };

    // `fold_group` folds one ordered group into a node, guessing the SAME reported preprocessed root
    // the prover reported, selected by public (height, arity): R1 vs R2 (full-`k`) or the recomputed
    // short root (short leaf-node R1'(m) / short root). A wrong selection makes the reconstructed root
    // miss the verified root ⇒ REJECTED.
    let fold_group = |context: &mut Context<QM31>,
                      group: &[(usize, HashValue<Var>, Vec<Var>)]|
     -> (usize, HashValue<Var>, Vec<Var>) {
        let outs = fold_hash(context, group);
        let height = group.iter().map(|(h, _, _)| *h).max().unwrap() + 1;
        let level = NodeLevel::from_height(height);
        let reported_root = if group.len() == k {
            level.preprocessed_root(config)
        } else if matches!(level, NodeLevel::VerifiesLeaves) {
            short_leaf_node_preprocessed_root(config, group.len())
        } else {
            short_node_preprocessed_root(config, group.len())
        };
        let node_pp = guess_pp(context, &reported_root);
        (height, node_pp, outs)
    };

    // --- BOTTOM (LEVEL 0): consume ALL leaves into height-1 leaf-nodes (per level0_group_sizes). ---
    // n == 1: the lone leaf is itself the root (no fold), matching recursive_aggregate_prove_leaves.
    let mut level: Vec<(usize, HashValue<Var>, Vec<Var>)> = if n == 1 {
        leaf_entries
    } else {
        let sizes = level0_group_sizes(n, k);
        let mut leaves_iter = leaf_entries.drain(..);
        let level0: Vec<(usize, HashValue<Var>, Vec<Var>)> = sizes
            .iter()
            .map(|&m| {
                let group: Vec<(usize, HashValue<Var>, Vec<Var>)> =
                    (0..m).map(|_| leaves_iter.next().unwrap()).collect();
                fold_group(&mut context, &group)
            })
            .collect();
        drop(leaves_iter);
        level0
    };

    // --- LEVELS ≥ 1: SHARED classic group+carry over NODES only (identical to prove_root_verification). ---
    while level.len() > 1 {
        if level.len() <= k {
            let root = fold_group(&mut context, &level);
            level = vec![root];
            break;
        }
        let remainder = level.len() % k;
        let carry: Vec<(usize, HashValue<Var>, Vec<Var>)> =
            level.split_off(level.len() - remainder);
        let mut next = Vec::with_capacity(level.len() / k + remainder);
        for group in level.chunks(k) {
            next.push(fold_group(&mut context, group));
        }
        next.extend(carry);
        level = next;
    }
    // Bind the reconstructed root's eight digest words to the verified root's eight output words.
    let computed_root = &level[0].2;
    for i in 0..N_RESERVED {
        eq(&mut context, computed_root[i], root_out_vars[i]);
    }

    // (3) Emit the unpacked per-leaf outputs as public outputs.
    let flat_outputs: Vec<Var> = leaf_output_vars.iter().flatten().copied().collect();
    context.set_outputs(&flat_outputs);

    // (4) Finalize, (optionally) blind, pad, derive prove config, prove.
    let mut context = context.finalize(false);
    context.validate_circuit();
    if let Some(zk) = zk_blind {
        add_zk_blinding(&mut context, zk.seed, zk.n_padding);
        context.validate_circuit();
    }
    pad_context(&mut context);
    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    let trace_log_size = preprocessed.trace_log_size;
    let pcs_config = get_pcs_config(trace_log_size, log_blowup_factor);
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
        pcs_config,
    )
    .expect("root-verification prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let verify_config = CircuitConfig {
        config: pcs_config,
        n_outputs: n * N_RESERVED,
        preprocessed_column_log_sizes: preprocessed.preprocessed_trace.log_sizes(),
        preprocessed_root: preprocessed_root(&preprocessed, log_blowup_factor),
    };
    verify_circuit(
        verify_config,
        proof.clone(),
        CircuitPublicData { output_values: public_data.output_values },
    )
    .expect("root-verification proof failed to verify (final-proof sanity check)");

    RootVerificationOutput {
        proof,
        leaf_outputs: leaves.iter().map(|l| l.output_values).collect(),
        trace_log_size,
    }
}

/// Proves a padded circuit's `values` against a prebuilt witness-independent [`CircuitPrecompute`],
/// reusing its committed preprocessed (tree0) tree and twiddles instead of rebuilding them.
fn prove_with_precompute(
    values: &[QM31],
    pc: &CircuitPrecompute,
) -> Result<CircuitProof<Blake2sMerkleHasher>, ProvingError> {
    prove_circuit_with_precompute::<Blake2sM31MerkleChannel>(
        &pc.base_column_pool,
        &pc.twiddles,
        &pc.preprocessed,
        MaybeOwned::Borrowed(&pc.tree),
        values,
        pc.pcs_config,
    )
}

/// The `MultiverifierInput` for one child (its proof + the two pieces its parent needs).
fn child_input(c: &TreeProof) -> MultiverifierInput<QM31> {
    MultiverifierInput {
        proof: c.proof.clone(),
        preprocessed_root: c.preprocessed_root.clone(),
        output_values: c.output_values,
    }
}

// Under base-fanning every node `recursive_aggregate` builds verifies NODE children (base-nodes at
// height 1, or R2 nodes at height ≥ 2) — the old leaf-verifying (R1) level is gone (base-nodes are
// proved upstream). So there is a single node kind: `node_shared_config` (child config, the
// self-verifying fixed point), reporting R2 (`node_preprocessed_root`) at full arity, and a
// recomputed short-root real root at a short arity (the short ROOT only). `NodeLevel` (which used to
// select R1 vs R2) is therefore removed; the unpacker still selects the trusted reported root by
// public (height, arity) — R2 for full-`k`, `short_node_preprocessed_root` for the short root, and
// `bottom.base_node_roots` for the base-node bottom level.

/// Builds and pads (to the common `node_target_padding_sizes`) the multiverifier circuit that
/// verifies `children` (base-nodes / R2 nodes) with `node_shared_config`.
fn build_node_context(children: &[TreeProof], config: &AggregateConfig) -> FinalizedContext<QM31> {
    let inputs: Vec<MultiverifierInput<QM31>> = children.iter().map(child_input).collect();
    let mut context = build_multiverifier_circuit::<QM31>(inputs, &config.node_shared_config);
    pad_to_targets(&mut context, config.node_target_padding_sizes.clone());
    context.validate_circuit();
    context
}

/// Proves one exactly-`FOLD_ARITY` INTERNAL R2 node verifying `children` (base-nodes / R2 nodes;
/// `children.len() == FOLD_ARITY`). Reports **R2** (`node_preprocessed_root`) and reuses
/// `node_precompute`. `height` (≥ 2) is recorded for the measurement log only.
fn prove_node(children: &[TreeProof], config: &AggregateConfig, height: usize) -> TreeProof {
    debug_assert_eq!(
        children.len(),
        config.fold_arity,
        "internal fold node must have exactly fold_arity children"
    );
    let _t_node = std::time::Instant::now();
    let mut context = build_node_context(children, config);

    let circuit_proof = match config.node_precompute.as_ref() {
        Some(pc) => prove_with_precompute(context.values(), pc),
        None => {
            let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
            prove_circuit_assignment(
                context.values(),
                &preprocessed,
                &BaseColumnPool::<SimdBackend>::new(),
                config.node_pcs_config,
            )
        }
    }
    .expect("node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_node(h={height})={:.3}s",
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: config.node_preprocessed_root.clone(),
        output_values,
    }
}

/// Proves one SHORT R2 node (arity `m ∈ 2..=FOLD_ARITY`) verifying `children` (base-nodes / R2
/// nodes). Used for the short ROOT (the terminal fold step). A short node's circuit shape differs
/// from the exactly-`k` internal shape (fewer child-verify sub-circuits), so it cannot reuse
/// `node_precompute`; it is proved via the self-contained rebuild path. Its reported
/// `preprocessed_root` is the circuit's *real* preprocessed root (recomputed here) — a value fixed by
/// the node's arity (a deterministic function of the public base-node count), hence verifier-derivable
/// (the unpacker recomputes the identical value via [`short_node_preprocessed_root`]) and never
/// prover-chosen. When `m == FOLD_ARITY` this yields exactly the same shape (and root) as a full-`k`
/// internal node.
fn prove_short_node(children: &[TreeProof], config: &AggregateConfig, height: usize) -> TreeProof {
    assert!(
        (2..=config.fold_arity).contains(&children.len()),
        "short/root fold node must have 2..=fold_arity children (got {})",
        children.len()
    );
    let _t_node = std::time::Instant::now();
    let mut context = build_node_context(children, config);

    let preprocessed = PreprocessedCircuit::preprocess_circuit(&mut context);
    // The node's real preprocessed root — pinned by the (public) arity + level, not prover-chosen.
    let short_preprocessed_root =
        preprocessed_root(&preprocessed, config.node_pcs_config.fri_config.log_blowup_factor);
    let circuit_proof = prove_circuit_assignment(
        context.values(),
        &preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
        config.node_pcs_config,
    )
    .expect("short/root node prove failed");
    let (proof, public_data) = prepare_circuit_proof_for_circuit_verifier(circuit_proof);

    let output_values: [QM31; N_RESERVED] = public_data
        .output_values
        .try_into()
        .expect("short/root node must emit exactly N_RESERVED output values");

    eprintln!(
        "recursive_aggregate: MEASURE t_short_node(arity={},h={height})={:.3}s",
        children.len(),
        _t_node.elapsed().as_secs_f64()
    );
    TreeProof {
        proof,
        preprocessed_root: short_preprocessed_root,
        output_values,
    }
}

// ---------------------------------------------------------------------------
// Config-derivation helpers (general): build an `AggregateConfig` whose multiverifier verifies
// leaves of a given circuit's config. Replicate stwo-circuits' test-only helpers (not exported).
// ---------------------------------------------------------------------------

use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuits::ivalue::NoValue;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use num_traits::Zero;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::poly::circle::PolyOps;

/// Merkle root of a circuit's preprocessed trace.
pub fn preprocessed_root(
    preprocessed: &PreprocessedCircuit,
    log_blowup_factor: u32,
) -> HashValue<QM31> {
    let lifting_log_size = preprocessed.trace_log_size + log_blowup_factor;
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(lifting_log_size)
            .circle_domain()
            .half_coset,
    );
    let trace = preprocessed.preprocessed_trace.get_trace::<SimdBackend>();
    let polys = SimdBackend::interpolate_columns(trace, &twiddles);
    let tree = CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new(
        polys,
        log_blowup_factor,
        &twiddles,
        true,
        Some(lifting_log_size),
        &BaseColumnPool::<SimdBackend>::new(),
    );
    tree.commitment.root().into()
}

/// The `SharedConfig` a multiverifier needs to verify leaves of `leaf_preprocessed`'s config.
pub fn shared_config_for_leaf(
    leaf_preprocessed: &PreprocessedCircuit,
    pcs_config: PcsConfig,
) -> SharedConfig {
    let proof_config = ProofConfig::new(
        &all_circuit_components::<QM31>(),
        leaf_preprocessed.preprocessed_trace.n_columns(),
        &pcs_config,
        INTERACTION_POW_BITS,
    );
    SharedConfig {
        pcs_config,
        proof_config,
        preprocessed_column_log_sizes: leaf_preprocessed.preprocessed_trace.log_sizes(),
    }
}

/// Builds + preprocesses the NoValue multiverifier node circuit of `arity` children for a given
/// `shared` config (the one a node is proved with) padded to `target_padding`. For `arity ==
/// FOLD_ARITY` this is the fixed shape every internal node proves (the one to cache in a node
/// [`CircuitPrecompute`]); for `arity < FOLD_ARITY` it is a SHORT node (a level-0 short leaf group or
/// the short root), whose preprocessed root the unpacker recomputes to match `prove_short_node`.
///
/// Mirrors the node-shape construction inside [`multiverifier_node_preprocessed`], but keyed on the
/// already-built `SharedConfig` (so a caller holding only a [`AggregateConfig`] can rebuild the cache
/// without the leaf's `PreprocessedCircuit`).
pub fn node_preprocessed_from_shared(
    shared: &SharedConfig,
    target_padding: ComponentSizes,
    arity: usize,
) -> PreprocessedCircuit {
    // Build the same node circuit `prove_node`/`prove_short_node` does, with NoValue witnesses (the
    // preprocessed trace is witness-independent). The verification topology is sized from a NoValue
    // `proof_config` over the shared `n_preprocessed_columns`, mirroring stwo-circuits' node-shape
    // construction.
    let proof_config = ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        shared.proof_config.n_preprocessed_columns,
        &shared.pcs_config,
        INTERACTION_POW_BITS,
    );
    let node_shared = SharedConfig {
        pcs_config: shared.pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: shared.preprocessed_column_log_sizes.clone(),
    };
    let empty = || MultiverifierInput {
        proof: empty_proof(&proof_config),
        preprocessed_root: HashValue::from([0u32; N_RESERVED]),
        output_values: [QM31::zero(); N_RESERVED],
    };
    let inputs: Vec<MultiverifierInput<NoValue>> = (0..arity).map(|_| empty()).collect();
    let mut ctx = build_multiverifier_circuit::<NoValue>(inputs, &node_shared);
    pad_to_targets(&mut ctx, target_padding);
    PreprocessedCircuit::preprocess_circuit(&mut ctx)
}

/// The preprocessed root a SHORT R2 node of the given `arity` (`2..=FOLD_ARITY-1`, the short ROOT)
/// reports — recomputed witness-independently over `node_shared_config`, byte-identical to what
/// [`prove_short_node`] recomputes for the same shape. Pure function of the public `arity`, so the
/// unpacker binds the same value the prover reported.
fn short_node_preprocessed_root(config: &AggregateConfig, arity: usize) -> HashValue<QM31> {
    let pp = node_preprocessed_from_shared(
        &config.node_shared_config,
        config.node_target_padding_sizes.clone(),
        arity,
    );
    preprocessed_root(&pp, config.node_pcs_config.fri_config.log_blowup_factor)
}

impl AggregateConfig {
    /// Defense-in-depth consistency check: the full-`FOLD_ARITY` node-node root recomputed via
    /// [`short_node_preprocessed_root`] must equal the trusted R2 (`node_preprocessed_root`) the
    /// unpacker binds full-`k` nodes to. They agree by construction (same node circuit shape via
    /// `node_preprocessed_from_shared`); a divergence is fail-closed (the root verification rejects
    /// via the missing-root reconstruction), so this just turns the recompute equivalence into a loud
    /// check. (The cached precompute already asserts tree0 == root in [`CircuitPrecompute::new`].)
    pub fn assert_full_arity_roots_consistent(&self) {
        let k = self.fold_arity;
        assert_eq!(
            short_node_preprocessed_root(self, k),
            self.node_preprocessed_root,
            "full-{k} node-node preprocessed root recompute != trusted R2",
        );
        // LeafR1R2 mode: also check the R1 (leaf-verifying) full-`k` root against its recompute. The
        // `decoupled_roots_consistent` regression test exercises this branch in the genuinely
        // decoupled R1 != R2 regime. Skipped under base-fanning (no leaf tier).
        if let Some(level1_root) = &self.level1_preprocessed_root {
            assert_eq!(
                short_leaf_node_preprocessed_root(self, k),
                *level1_root,
                "full-{k} leaf-node preprocessed root recompute != trusted R1",
            );
        }
    }
}

/// Builds + preprocesses the NoValue multiverifier node that verifies two leaves of
/// `leaf_preprocessed`'s config (optionally padded), to recompute the node's `preprocessed_root`
/// and component sizes for a given leaf circuit. Also returns the node's *unpadded* component sizes
/// (for deriving the shared `TARGET_PADDING_SIZES = max(leaf, node)`).
pub fn multiverifier_node_preprocessed(
    leaf_preprocessed: &PreprocessedCircuit,
    pcs_config: PcsConfig,
    target_padding: Option<ComponentSizes>,
    fold_arity: usize,
) -> (PreprocessedCircuit, ComponentSizes) {
    let proof_config = ProofConfig::new(
        &all_circuit_components::<NoValue>(),
        leaf_preprocessed.preprocessed_trace.n_columns(),
        &pcs_config,
        INTERACTION_POW_BITS,
    );
    let shared = SharedConfig {
        pcs_config,
        proof_config: proof_config.clone(),
        preprocessed_column_log_sizes: leaf_preprocessed.preprocessed_trace.log_sizes(),
    };
    let empty = || MultiverifierInput {
        proof: empty_proof(&proof_config),
        preprocessed_root: HashValue::from([0u32; N_RESERVED]),
        output_values: [QM31::zero(); N_RESERVED],
    };
    // The internal node shape is exactly-`fold_arity` children (matches `prove_node`).
    let inputs: Vec<MultiverifierInput<NoValue>> = (0..fold_arity).map(|_| empty()).collect();
    let mut ctx = build_multiverifier_circuit::<NoValue>(inputs, &shared);
    let unpadded_sizes = compute_padded_sizes(&ctx);
    if let Some(t) = target_padding {
        pad_to_targets(&mut ctx, t);
    }
    (
        PreprocessedCircuit::preprocess_circuit(&mut ctx),
        unpadded_sizes,
    )
}

#[cfg(test)]
mod topology_tests {
    use super::{Child, FOLD_ARITY, base_fan_group_sizes, build_fold_topology, root_arity};

    /// The arity these topology tests run at — the [`TopologyConfig`](super::TopologyConfig) default
    /// (`fold_arity = FOLD_ARITY`). Threaded explicitly into `build_fold_topology`/`root_arity` (which
    /// now take `k`) so the tests exercise the production default; the k=8-pinned expectations below
    /// assert `K == 8` so they trip loudly if the default ever changes.
    const K: usize = FOLD_ARITY;

    /// A symbolic tree shape, index-aware — the byte-identity-relevant structure of the node-node fold
    /// tree over the base-nodes (each node's ordered children and the resulting nesting). `Leaf(i)` is
    /// base-node `i` (the fold's height-1 inputs, proved upstream).
    #[derive(PartialEq, Eq, Debug)]
    enum Shape {
        Leaf(usize),
        Node(Vec<Shape>),
    }

    /// The shape `recursive_aggregate_prove`'s node-node fold builds over `m` base-nodes, computed over
    /// indices — the classic `k`-ary group+carry over the base-nodes (leading full-`k` runs into
    /// nodes, `< k` remainder carried up, a `2..=k` level folded whole into the root). The single
    /// source of truth the topology must match. `m == 1` ⇒ the lone base-node is the root.
    fn sequential_shape(m: usize) -> Shape {
        if m == 1 {
            return Shape::Leaf(0);
        }
        let mut level: Vec<Shape> = (0..m).map(Shape::Leaf).collect();
        while level.len() > 1 {
            if level.len() <= K {
                return Shape::Node(level);
            }
            let remainder = level.len() % K;
            let carry: Vec<Shape> = level.split_off(level.len() - remainder);
            let mut next: Vec<Shape> = Vec::new();
            let mut iter = level.into_iter().peekable();
            while iter.peek().is_some() {
                let group: Vec<Shape> = iter.by_ref().take(K).collect();
                next.push(Shape::Node(group));
            }
            next.extend(carry);
            level = next;
        }
        level.into_iter().next().unwrap()
    }

    /// Reference count of R2 nodes the node-node fold proves over `m` base-nodes (`m == 1` ⇒ 0, the
    /// lone base-node is the root; base-nodes themselves are proved upstream, not counted here).
    fn sequential_node_count(m: usize) -> usize {
        if m == 1 {
            return 0;
        }
        let mut count = 0usize;
        let mut len = m;
        while len > 1 {
            if len <= K {
                count += 1;
                break;
            }
            count += len / K;
            len = len / K + len % K;
        }
        count
    }

    /// Reference root height of the node-node fold over `m` base-nodes: base-nodes are height 1, each
    /// fold level adds 1 (`m == 1` ⇒ height 1, the lone base-node IS the root).
    fn sequential_height(m: usize) -> usize {
        if m == 1 {
            return 1;
        }
        let mut height = 1usize; // base-nodes
        let mut len = m;
        while len > 1 {
            height += 1;
            if len <= K {
                break;
            }
            len = len / K + len % K;
        }
        height
    }

    /// The shape the streaming scheduler realizes, reconstructed from `build_fold_topology`'s task
    /// list + root reference. Each task's ordered `children` resolve to the same `Shape` nodes,
    /// proving the streaming dataflow folds the identical tree with the identical child inputs.
    fn streaming_shape(m: usize) -> Shape {
        let (tasks, root) = build_fold_topology(m, K);
        fn resolve(c: Child, tasks: &[super::FoldTask]) -> Shape {
            match c {
                Child::Leaf(i) => Shape::Leaf(i),
                Child::Node(j) => Shape::Node(
                    tasks[j].children.iter().map(|&ch| resolve(ch, tasks)).collect(),
                ),
            }
        }
        resolve(root, &tasks)
    }

    /// The streamed tree is byte-identical to the sequential one because it has the IDENTICAL shape:
    /// same nesting, same base-node-index-to-child-slot assignment for every node. Since `prove_node`
    /// is a pure function of its ordered children, identical shape + identical per-node inputs ⇒
    /// identical proof bytes and `recursion_fingerprint`. Checks every `m` up to 260 base-nodes —
    /// covers ALL `m mod k` residues at k=FOLD_ARITY across several levels, plus power-of-k boundaries.
    #[test]
    fn streaming_topology_matches_sequential() {
        for m in 1..=260usize {
            assert_eq!(
                streaming_shape(m),
                sequential_shape(m),
                "fold topology diverges from the level loop at m={m}"
            );
        }
    }

    /// Pins k=8 group+carry examples over base-nodes (the fold's height-1 inputs).
    ///   - m=9 (`r=1`): root over `node([0..8]) + carried Leaf(8)`? No — the loop carries the `< k`
    ///     remainder and folds the whole `2..=k` level into the root, so m=9 → `node([node([0..8]),
    ///     Leaf(8)])` where Leaf(8) is a carried base-node (a NODE, safe to carry).
    ///   - m=17 (`r=1`): 17 base-nodes → first level `node([0..8]), node([8..16])` + carried Leaf(16)
    ///     → root over those three.
    #[test]
    fn streaming_topology_m9_m17_example_k8() {
        assert_eq!(K, 8, "this pinned example is written for k=8 (the TopologyConfig default)");
        use Shape::{Leaf, Node};
        // m=9: 9 > 8 ⇒ first level groups [0..8) into one node, carries base-node 8; 2 entries ≤ k ⇒
        // root over [node([0..8)), Leaf(8)].
        let m9 = Node(vec![Node((0..8).map(Leaf).collect()), Leaf(8)]);
        assert_eq!(streaming_shape(9), m9);
        // m=17: first level [0..8),[8..16) + carried base-node 16 ⇒ 3 entries ≤ k ⇒ root over them.
        let m17 = Node(vec![
            Node((0..8).map(Leaf).collect()),
            Node((8..16).map(Leaf).collect()),
            Leaf(16),
        ]);
        assert_eq!(streaming_shape(17), m17);
    }

    /// `build_fold_topology`'s R2-node count and root height match the reference over `m` base-nodes,
    /// across every `m mod k` residue. `m == 1` ⇒ no fold node, root is the lone base-node at height 1.
    #[test]
    fn topology_node_count_and_height() {
        for m in 1..=260usize {
            let (tasks, root) = build_fold_topology(m, K);
            assert_eq!(
                tasks.len(),
                sequential_node_count(m),
                "m={m}: node count diverges from the fold loop"
            );
            let h = match root {
                Child::Node(j) => tasks[j].height,
                Child::Leaf(_) => 1, // the lone base-node (m == 1) is height 1
            };
            assert_eq!(
                h,
                sequential_height(m),
                "m={m}: root height diverges from the fold loop"
            );
        }
    }

    /// Arity invariants of the node-node fold over `m` base-nodes: every non-root R2 fold node is
    /// exactly-`k`; the root may be short (`2..=k`) with arity == `root_arity(m)`. Every fold task is
    /// height ≥ 2 (base-nodes are the height-1 inputs). All arities are in `2..=k`.
    #[test]
    fn arities_valid_shorts_at_root() {
        for m in 2..=260usize {
            let (tasks, root) = build_fold_topology(m, K);
            let root_idx = match root {
                Child::Node(j) => j,
                Child::Leaf(_) => unreachable!("m>1 root is a fold node"),
            };
            for (ti, t) in tasks.iter().enumerate() {
                assert!(
                    (2..=K).contains(&t.children.len()),
                    "m={m}: node {ti} arity {} out of 2..=k",
                    t.children.len()
                );
                assert!(t.height >= 2, "m={m}: fold node {ti} must be height >= 2");
                if ti == root_idx {
                    assert_eq!(
                        t.children.len(),
                        root_arity(m, K),
                        "m={m}: root arity must equal root_arity(m)"
                    );
                } else {
                    // Non-root fold nodes are always exactly-k.
                    assert_eq!(
                        t.children.len(),
                        K,
                        "m={m}: non-root fold node {ti} is not exactly-k"
                    );
                }
            }
        }
    }

    /// Pins k=8 root arities + total R2-node count for the group+carry fold over `m` base-nodes.
    /// m=8 is a clean full-`k` root (one node, no shorts); m∈{9,35,69} exercise the carry.
    ///   - m=8: root over [0..8) (arity 8, 1 node).
    ///   - m=9: [node([0..8)), carried 8] → root arity 2 (2 nodes total).
    ///   - m=35: 35 = 4·8 + 3 → level1 = 4 full-8 nodes + carried 3 = 7 entries ≤ k → root arity 7
    ///     (5 nodes total).
    ///   - m=69: 69 = 8·8 + 5 → level1 = 8 full-8 nodes + carried 5 = 13 entries > k → level2 =
    ///     node([those 8]) + carried 5 = 6 entries → root arity 6 (8 + 1 + 1 = 10 nodes total).
    #[test]
    fn fold_pins_key_m() {
        assert_eq!(K, 8, "these pinned expectations are for k=8 (the TopologyConfig default)");
        // (m, expected root_arity).
        let cases = [(8usize, 8usize), (9, 2), (35, 7), (69, 6)];
        for (m, want_root_arity) in cases {
            let (tasks, root) = build_fold_topology(m, K);
            let root_idx = match root {
                Child::Node(j) => j,
                Child::Leaf(_) => unreachable!(),
            };
            assert_eq!(
                tasks[root_idx].children.len(),
                want_root_arity,
                "m={m}: unexpected root arity"
            );
            assert_eq!(root_arity(m, K), want_root_arity, "m={m}: root_arity mismatch");
            assert_eq!(
                tasks.len(),
                sequential_node_count(m),
                "m={m}: node count mismatch"
            );
        }
    }

    /// Base-node grouping (`base_fan_group_sizes`) invariants over `n` bases: every group arity is in
    /// `1..=b`, the groups partition all `n` bases in order, all but the last are full-`b`, and the
    /// count matches `ceil(n/b)`. Swept for a few `b` (independent of FOLD_ARITY).
    #[test]
    fn base_fan_groups_valid() {
        for b in 1..=8usize {
            for n in 1..=260usize {
                let sizes = base_fan_group_sizes(n, b);
                assert_eq!(sizes.iter().sum::<usize>(), n, "b={b} n={n}: groups must cover all bases");
                assert_eq!(sizes.len(), n.div_ceil(b), "b={b} n={n}: group count != ceil(n/b)");
                for (gi, &m) in sizes.iter().enumerate() {
                    assert!((1..=b).contains(&m), "b={b} n={n}: group {gi} arity {m} out of 1..=b");
                    if gi + 1 < sizes.len() {
                        assert_eq!(m, b, "b={b} n={n}: non-last group {gi} must be full-b");
                    }
                }
            }
        }
    }
}
