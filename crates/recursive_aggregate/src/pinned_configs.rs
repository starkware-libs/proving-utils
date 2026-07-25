//! Const-friendly pinned verifier config + its runtime rebuild — PRODUCTION machinery (a consumer
//! pins the per-operating-point [`RecursionConfig`] and this module turns it into an
//! [`AggregateConfig`] on the prove path), so it is NOT feature-gated. The fresh-cascade DERIVATION
//! that (re)captures / drift-checks these values lives in the test-only `test_utils`.
//!
//! [`RecursionConfig`] is the const-constructible single config a consumer holds: the pinned
//! verifier shapes/roots (the const twin of [`DerivedConfigs`] — a `const` can't hold a
//! `CircuitConfig`'s heap `OrderedHashMap` cols / `Vec` arities) PLUS the plain recursion params
//! (blowups, fold arity, leaf count). [`RecursionConfig::to_derived`] rebuilds the runtime
//! [`DerivedConfigs`], and [`assemble_aggregate_config`] packs it into the [`AggregateConfig`] the
//! fold/unpacker consume — the SAME builder the fresh derivation uses, so a pinned config is
//! byte-identical to a freshly-derived one.

use std::collections::BTreeMap;

use crate::{AggregateConfig, shared_config_from_circuit_config};

use circuit_cairo_verifier::privacy::get_pcs_config;
use circuit_common::N_RESERVED;
use circuit_common::finalize::ComponentSizes;
use circuit_verifier::verify::CircuitConfig;
use circuits::blake::HashValue;
use circuits_stark_verifier::order_hash_map::OrderedHashMap;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

/// The single const-constructible recursion config a consumer pins per operating point. Its pinned
/// verifier shapes (the const twin of [`DerivedConfigs`]) use `&'static [(id, log_size)]` cols and
/// `[u32; 8]` roots; node layers share one shape across arities (all pad to `node_target`), only
/// the per-arity root differs. It also carries the plain recursion params (blowups, fold arity,
/// leaf count) so it is self-contained — proving-utils reads them here, no external global.
/// [`RecursionConfig::to_aggregate_config`] turns it into the runtime [`AggregateConfig`].
pub struct RecursionConfig {
    pub leaf: PinnedLayer,
    pub level1: PinnedNodeLayer,
    pub fold: PinnedNodeLayer,
    pub node_target: PinnedComponentSizes,
    pub unpacker: PinnedUnpacker,
    /// Recursion (node-node / root) FRI blowup factor.
    pub recursion_log_blowup: u32,
    /// Leaf-wrap FRI blowup factor (decoupled from the node blowup).
    pub leaf_log_blowup: u32,
    /// Fold arity `k` (each internal node verifies exactly `k` children).
    pub fold_arity: usize,
    /// This point's leaf/shard count `N`.
    pub n_leaves: usize,
}

impl RecursionConfig {
    /// The pinned trusted per-N unpacker [`CircuitConfig`], rebuilt from the pinned literals at
    /// this config's leaf/node blowups. The one runtime verifier config a consumer needs off the
    /// pinned config (the fold-node/leaf/level1 configs stay internal to the prove-path assembly).
    pub fn unpacker_config(&self) -> CircuitConfig {
        self.to_derived(self.leaf_log_blowup, self.recursion_log_blowup)
            .unpacker
    }

    /// The pinned → runtime [`AggregateConfig`] recipe: [`to_derived`](Self::to_derived) at this
    /// config's leaf/node FRI blowups, packed by [`assemble_aggregate_config`] with the leaf's
    /// natural padding target and this config's fold arity. The single prove-path entry.
    pub(crate) fn to_aggregate_config(&self, leaf_target: ComponentSizes) -> AggregateConfig {
        assemble_aggregate_config(
            &self.to_derived(self.leaf_log_blowup, self.recursion_log_blowup),
            leaf_target,
            self.fold_arity,
        )
    }

    /// Rebuilds the runtime [`DerivedConfigs`] from the pinned literals: leaf/node configs get the
    /// leaf/node PCS at their pinned trace-log (`get_pcs_config` at `leaf_blowup`/`node_blowup`,
    /// the FRI blowups the pinned points were captured with); the unpacker PCS is pinned
    /// verbatim. `n_outputs` is `N_RESERVED` for leaf/node layers.
    pub(crate) fn to_derived(&self, leaf_blowup: u32, node_blowup: u32) -> DerivedConfigs {
        DerivedConfigs {
            leaf: circuit_config(
                get_pcs_config(self.leaf.trace_log_size, leaf_blowup),
                self.leaf.preprocessed_column_log_sizes,
                self.leaf.root,
            ),
            node_target: ComponentSizes {
                eq: self.node_target.eq,
                qm31_ops: self.node_target.qm31_ops,
                m31_to_u32: self.node_target.m31_to_u32,
                triple_xor: self.node_target.triple_xor,
                blake_g_gate: self.node_target.blake_g_gate,
            },
            level1: pinned_node_configs(&self.level1, node_blowup),
            fold: pinned_node_configs(&self.fold, node_blowup),
            unpacker: CircuitConfig {
                config: self.unpacker.pcs,
                n_outputs: self.unpacker.n_outputs,
                preprocessed_column_log_sizes: cols(self.unpacker.preprocessed_column_log_sizes),
                preprocessed_root: HashValue::from(self.unpacker.root),
            },
        }
    }
}

/// A single verifier layer's pinned shape + preprocessed root (leaf: one root, not per-arity).
pub struct PinnedLayer {
    pub trace_log_size: u32,
    pub preprocessed_column_log_sizes: &'static [(&'static str, u32)],
    pub root: [u32; 8],
}

/// A pinned node layer (level1 or fold): one shared shape + a per-arity root, indexed `arity - 2`
/// over `2..=arity_count + 1`.
pub struct PinnedNodeLayer {
    pub trace_log_size: u32,
    pub preprocessed_column_log_sizes: &'static [(&'static str, u32)],
    pub roots: &'static [[u32; 8]],
}

/// The pinned common node-padding `ComponentSizes` (const-constructible mirror).
pub struct PinnedComponentSizes {
    pub eq: usize,
    pub qm31_ops: usize,
    pub m31_to_u32: usize,
    pub triple_xor: usize,
    pub blake_g_gate: usize,
}

/// The pinned trusted per-N unpacker [`CircuitConfig`] fields.
pub struct PinnedUnpacker {
    pub pcs: PcsConfig,
    pub n_outputs: usize,
    pub preprocessed_column_log_sizes: &'static [(&'static str, u32)],
    pub root: [u32; 8],
}

/// Every verifier config a fresh cascade derives for one operating point: the leaf, the common
/// `node_target`, the per-arity level1 (leaf-verifying) and fold (node-verifying) node configs
/// (arity `2..=fold_arity`, index `arity - 2`), and the trusted per-N unpacker.
#[derive(Debug, PartialEq)]
pub(crate) struct DerivedConfigs {
    pub leaf: CircuitConfig,
    pub node_target: ComponentSizes,
    pub level1: Vec<CircuitConfig>,
    pub fold: Vec<CircuitConfig>,
    pub unpacker: CircuitConfig,
}

/// Assembles a runtime [`AggregateConfig`] from a [`DerivedConfigs`] — the single builder both the
/// fresh-cascade derivation (`test_utils::derive_configs`) and a consumer's pinned path use, so a
/// pinned `AggregateConfig` is byte-identical to a freshly-derived one. Leaf/fold shared configs
/// come from the leaf/level1[k] [`CircuitConfig`]s; the leaf/node PCS + preprocessed roots read
/// straight from `derived` (never recomputed here). `leaf_target` is the leaf's natural padding
/// target (used only by the prove path, not the unpacker).
///
/// `derived.unpacker` is NOT read here (this builds the config the unpacker derivation consumes),
/// so a partially-filled `DerivedConfigs` (unpacker placeholder) is fine.
pub(crate) fn assemble_aggregate_config(
    derived: &DerivedConfigs,
    leaf_target: ComponentSizes,
    fold_arity: usize,
) -> AggregateConfig {
    let level1_k = &derived.level1[fold_arity - 2];
    let level1_roots = per_arity_roots(&derived.level1);
    let fold_roots = per_arity_roots(&derived.fold);
    AggregateConfig {
        fold_shared_config: shared_config_from_circuit_config(level1_k),
        node_target_padding_sizes: derived.node_target.clone(),
        node_pcs_config: level1_k.config,
        fold_arity,
        leaf_shared_config: shared_config_from_circuit_config(&derived.leaf),
        level1_roots,
        fold_roots,
        leaf_preprocessed_root: derived.leaf.preprocessed_root.clone(),
        leaf_target_padding_sizes: leaf_target,
        leaf_pcs_config: derived.leaf.config,
    }
}

/// Assembles a leaf/node verifier [`CircuitConfig`] from a pinned PCS + columns + root. `n_outputs`
/// is `N_RESERVED` (the reserved-output count every recursion circuit emits).
pub(crate) fn circuit_config(
    pcs: PcsConfig,
    preprocessed_column_log_sizes: &'static [(&'static str, u32)],
    root: [u32; 8],
) -> CircuitConfig {
    CircuitConfig {
        config: pcs,
        n_outputs: N_RESERVED,
        preprocessed_column_log_sizes: cols(preprocessed_column_log_sizes),
        preprocessed_root: HashValue::from(root),
    }
}

/// Builds an [`OrderedHashMap`] of preprocessed column id → log_size from pinned literal pairs,
/// preserving their (canonical committed) order.
pub(crate) fn cols(
    pairs: &'static [(&'static str, u32)],
) -> OrderedHashMap<PreProcessedColumnId, u32> {
    pairs
        .iter()
        .map(|(id, log_size)| {
            (
                PreProcessedColumnId {
                    id: (*id).to_owned(),
                },
                *log_size,
            )
        })
        .collect()
}

/// The per-arity node [`CircuitConfig`]s a pinned node layer rebuilds: one shared shape (PCS at the
/// layer's pinned trace-log + `node_blowup`, pinned cols) with each arity's pinned root.
fn pinned_node_configs(layer: &PinnedNodeLayer, node_blowup: u32) -> Vec<CircuitConfig> {
    layer
        .roots
        .iter()
        .map(|r| {
            circuit_config(
                get_pcs_config(layer.trace_log_size, node_blowup),
                layer.preprocessed_column_log_sizes,
                *r,
            )
        })
        .collect()
}

/// Per-arity (`2..=k`, index `arity - 2`) preprocessed-root table from a layer's per-arity configs.
fn per_arity_roots(configs: &[CircuitConfig]) -> BTreeMap<usize, HashValue<QM31>> {
    configs
        .iter()
        .enumerate()
        .map(|(i, c)| (i + 2, c.preprocessed_root.clone()))
        .collect()
}
