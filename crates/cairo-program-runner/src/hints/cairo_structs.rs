use std::any::Any;

use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::Felt252;
use serde::{Deserialize, Serialize};

use crate::maybe_relocatable_box;
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VectorCommitmentConfig {
    pub height: Felt252,
    pub n_verifier_friendly_commitment_layers: Felt252,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TableCommitmentConfig {
    pub n_columns: Felt252,
    pub vector: VectorCommitmentConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracesConfig {
    pub original: TableCommitmentConfig,
    pub interaction: TableCommitmentConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FriConfig {
    pub log_input_size: Felt252,
    pub n_layers: Felt252,
    pub inner_layers: Vec<TableCommitmentConfig>,
    pub fri_step_sizes: Vec<Felt252>,
    pub log_last_layer_degree_bound: Felt252,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofOfWorkConfig {
    pub n_bits: Felt252,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarkConfig {
    pub traces: TracesConfig,
    pub composition: TableCommitmentConfig,
    pub fri: FriConfig,
    pub proof_of_work: ProofOfWorkConfig,
    pub log_trace_domain_size: Felt252,
    pub n_queries: Felt252,
    pub log_n_cosets: Felt252,
    pub n_verifier_friendly_commitment_layers: Felt252,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracesUnsentCommitment {
    pub original: Felt252,
    pub interaction: Felt252,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FriUnsentCommitment {
    pub inner_layers: Vec<Felt252>,
    pub last_layer_coefficients: Vec<Felt252>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofOfWorkUnsentCommitment {
    pub nonce: Felt252,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarkUnsentCommitment {
    pub traces: TracesUnsentCommitment,
    pub composition: Felt252,
    pub oods_values: Vec<Felt252>,
    pub fri: FriUnsentCommitment,
    pub proof_of_work: ProofOfWorkUnsentCommitment,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VectorCommitmentWitness {
    pub n_authentications: Felt252,
    pub authentications: Vec<Felt252>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TableCommitmentWitness {
    pub vector: VectorCommitmentWitness,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TableDecommitment {
    pub n_values: Felt252,
    pub values: Vec<Felt252>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracesDecommitment {
    pub original: TableDecommitment,
    pub interaction: TableDecommitment,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracesWitness {
    pub original: TableCommitmentWitness,
    pub interaction: TableCommitmentWitness,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FriLayerWitness {
    pub n_leaves: Felt252,
    pub leaves: Vec<Felt252>,
    pub table_witness: TableCommitmentWitness,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FriWitness {
    pub layers: Vec<FriLayerWitness>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarkWitness {
    pub traces_decommitment: TracesDecommitment,
    pub traces_witness: TracesWitness,
    pub composition_decommitment: TableDecommitment,
    pub composition_witness: TableCommitmentWitness,
    pub fri_witness: FriWitness,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarkProof {
    pub config: StarkConfig,
    pub public_input: CairoPublicInput,
    pub unsent_commitment: StarkUnsentCommitment,
    pub witness: StarkWitness,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SegmentInfo {
    pub begin_addr: Felt252,
    pub stop_ptr: Felt252,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CairoPublicInput {
    pub log_n_steps: Felt252,
    pub range_check_min: Felt252,
    pub range_check_max: Felt252,
    pub layout: Felt252,
    pub dynamic_params: Vec<Felt252>,
    pub n_segments: Felt252,
    pub segments: Vec<SegmentInfo>,
    pub padding_addr: Felt252,
    pub padding_value: Felt252,
    pub main_page_len: Felt252,
    pub main_page: Vec<Felt252>,
    pub n_continuous_pages: Felt252,
    pub continuous_page_headers: Vec<Felt252>,
}
pub trait ToVec {
    fn to_vec(&self) -> Vec<Box<dyn Any>>;
}

// Implement ToVec for each struct

impl ToVec for VectorCommitmentConfig {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            maybe_relocatable_box!(self.height),
            maybe_relocatable_box!(self.n_verifier_friendly_commitment_layers),
        ]
    }
}

impl ToVec for TableCommitmentConfig {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            maybe_relocatable_box!(self.n_columns),
            Box::new(self.vector.to_vec()),
        ]
    }
}

impl ToVec for TracesConfig {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            Box::new(self.original.to_vec()),
            Box::new(self.interaction.to_vec()),
        ]
    }
}

impl ToVec for FriConfig {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let inner_layers_vec: Vec<Box<dyn Any>> = self
            .inner_layers
            .iter()
            .flat_map(|layer| layer.to_vec())
            .collect();
        let fri_step_sizes_vec: Vec<Box<dyn Any>> = self
            .fri_step_sizes
            .iter()
            .map(|size| maybe_relocatable_box!(*size))
            .collect();
        vec![
            maybe_relocatable_box!(self.log_input_size),
            maybe_relocatable_box!(self.n_layers),
            Box::new(inner_layers_vec),
            Box::new(fri_step_sizes_vec),
            maybe_relocatable_box!(self.log_last_layer_degree_bound),
        ]
    }
}

impl ToVec for ProofOfWorkConfig {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![maybe_relocatable_box!(self.n_bits)]
    }
}

impl ToVec for StarkConfig {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            Box::new(self.traces.to_vec()),
            Box::new(self.composition.to_vec()),
            Box::new(self.fri.to_vec()),
            Box::new(self.proof_of_work.to_vec()),
            maybe_relocatable_box!(self.log_trace_domain_size),
            maybe_relocatable_box!(self.n_queries),
            maybe_relocatable_box!(self.log_n_cosets),
            maybe_relocatable_box!(self.n_verifier_friendly_commitment_layers),
        ]
    }
}

impl ToVec for TracesUnsentCommitment {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            maybe_relocatable_box!(self.original),
            maybe_relocatable_box!(self.interaction),
        ]
    }
}

impl ToVec for FriUnsentCommitment {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let inner_layers_vec: Vec<Box<dyn Any>> = self
            .inner_layers
            .iter()
            .map(|layer| maybe_relocatable_box!(*layer))
            .collect();
        let last_layer_coefficients_vec: Vec<Box<dyn Any>> = self
            .last_layer_coefficients
            .iter()
            .map(|coeff| maybe_relocatable_box!(*coeff))
            .collect();
        vec![
            Box::new(inner_layers_vec),
            Box::new(last_layer_coefficients_vec),
        ]
    }
}

impl ToVec for ProofOfWorkUnsentCommitment {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![maybe_relocatable_box!(self.nonce)]
    }
}

impl ToVec for StarkUnsentCommitment {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let oods_values_vec: Vec<Box<dyn Any>> = self
            .oods_values
            .iter()
            .map(|value| maybe_relocatable_box!(*value))
            .collect();
        vec![
            Box::new(self.traces.to_vec()),
            maybe_relocatable_box!(self.composition),
            Box::new(oods_values_vec),
            Box::new(self.fri.to_vec()),
            Box::new(self.proof_of_work.to_vec()),
        ]
    }
}

impl ToVec for VectorCommitmentWitness {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let authentications_vec: Vec<Box<dyn Any>> = self
            .authentications
            .iter()
            .map(|auth| maybe_relocatable_box!(*auth))
            .collect();
        vec![
            maybe_relocatable_box!(self.n_authentications),
            Box::new(authentications_vec),
        ]
    }
}

impl ToVec for TableCommitmentWitness {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![Box::new(self.vector.to_vec())]
    }
}

impl ToVec for TableDecommitment {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let values_vec: Vec<Box<dyn Any>> = self
            .values
            .iter()
            .map(|value| maybe_relocatable_box!(*value))
            .collect();
        vec![maybe_relocatable_box!(self.n_values), Box::new(values_vec)]
    }
}

impl ToVec for TracesDecommitment {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            Box::new(self.original.to_vec()),
            Box::new(self.interaction.to_vec()),
        ]
    }
}

impl ToVec for TracesWitness {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            Box::new(self.original.to_vec()),
            Box::new(self.interaction.to_vec()),
        ]
    }
}

impl ToVec for FriLayerWitness {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let leaves_vec: Vec<Box<dyn Any>> = self
            .leaves
            .iter()
            .map(|leaf| maybe_relocatable_box!(*leaf))
            .collect();
        vec![
            maybe_relocatable_box!(self.n_leaves),
            Box::new(leaves_vec),
            Box::new(self.table_witness.to_vec()),
        ]
    }
}

impl ToVec for FriWitness {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let layers_vec: Vec<Box<dyn Any>> = self
            .layers
            .iter()
            .flat_map(|layer| layer.to_vec())
            .collect();
        vec![Box::new(layers_vec)]
    }
}

impl ToVec for StarkWitness {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            Box::new(self.traces_decommitment.to_vec()),
            Box::new(self.traces_witness.to_vec()),
            Box::new(self.composition_decommitment.to_vec()),
            Box::new(self.composition_witness.to_vec()),
            Box::new(self.fri_witness.to_vec()),
        ]
    }
}

impl ToVec for SegmentInfo {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            maybe_relocatable_box!(self.begin_addr),
            maybe_relocatable_box!(self.stop_ptr),
        ]
    }
}

impl ToVec for CairoPublicInput {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        let dynamic_params_vec: Vec<Box<dyn Any>> = self
            .dynamic_params
            .iter()
            .map(|param| maybe_relocatable_box!(*param))
            .collect();
        let segments_vec: Vec<Box<dyn Any>> = self
            .segments
            .iter()
            .flat_map(|segment| segment.to_vec())
            .collect();
        let main_page_vec: Vec<Box<dyn Any>> = self
            .main_page
            .iter()
            .map(|page| maybe_relocatable_box!(*page))
            .collect();
        let continuous_page_headers_vec: Vec<Box<dyn Any>> = self
            .continuous_page_headers
            .iter()
            .map(|header| maybe_relocatable_box!(*header))
            .collect();
        vec![
            maybe_relocatable_box!(self.log_n_steps),
            maybe_relocatable_box!(self.range_check_min),
            maybe_relocatable_box!(self.range_check_max),
            maybe_relocatable_box!(self.layout),
            Box::new(dynamic_params_vec),
            maybe_relocatable_box!(self.n_segments),
            Box::new(segments_vec),
            maybe_relocatable_box!(self.padding_addr),
            maybe_relocatable_box!(self.padding_value),
            maybe_relocatable_box!(self.main_page_len),
            Box::new(main_page_vec),
            maybe_relocatable_box!(self.n_continuous_pages),
            Box::new(continuous_page_headers_vec),
        ]
    }
}

impl ToVec for StarkProof {
    fn to_vec(&self) -> Vec<Box<dyn Any>> {
        vec![
            Box::new(self.config.to_vec()),
            Box::new(self.public_input.to_vec()),
            Box::new(self.unsent_commitment.to_vec()),
            Box::new(self.witness.to_vec()),
        ]
    }
}
