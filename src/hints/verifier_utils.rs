use cairo_vm::{
    air_public_input::{MemorySegmentAddresses, PublicMemoryEntry},
    serde::deserialize_program::Identifier,
    types::builtin_name::BuiltinName,
    vm::errors::hint_errors::HintError,
    Felt252,
};
use serde_json::Value as JsonValue;
use std::collections::HashMap;

use super::{
    cairo_structs::*,
    types::{ExtractedIDsAndInputValues, ExtractedProofValues, OwnedPublicInput},
    COMPONENT_HEIGHT,
};
use num_bigint::BigUint;
use num_traits::{Num, ToPrimitive};
use regex::Regex;
use starknet_types_core::hash::{Pedersen, StarkHash};

// safe_log2 function
pub fn safe_log2(x: u64) -> Result<u32, HintError> {
    if x.is_power_of_two() {
        Ok(x.trailing_zeros())
    } else {
        Err(HintError::CustomHint(
            format!("safe_log2: Input {} is not a power of two.", x).into(),
        ))
    }
}

// extract_annotations function
pub fn extract_annotations(
    annotations: &[String],
    prefix: &str,
    kind: &str,
) -> Result<Vec<BigUint>, HintError> {
    let mut res = Vec::new();

    let pattern = format!(
        r"P->V\[(\d+):(\d+)\]: /cpu air/{}: .*?{}\((.+)\)",
        prefix, kind
    );

    let re = Regex::new(&pattern)
        .map_err(|e| HintError::CustomHint(format!("Regex error: {}", e).into()))?;

    for line in annotations {
        if let Some(captures) = re.captures(line) {
            let str_value = captures
                .get(3)
                .ok_or_else(|| {
                    HintError::CustomHint(
                        "Failed to get capture group 3 in extract_annotations.".into(),
                    )
                })?
                .as_str();

            let mut parse_and_push = |value_str: &str| -> Result<(), HintError> {
                let value_str = value_str.trim().trim_start_matches("0x");
                let value = BigUint::from_str_radix(value_str, 16).map_err(|_| {
                    HintError::CustomHint(
                        format!("Failed to parse value_str '{}'", value_str).into(),
                    )
                })?;
                res.push(value);
                Ok(())
            };

            if kind == "Field Elements" {
                for x in str_value.split(',') {
                    parse_and_push(x)?;
                }
            } else {
                parse_and_push(str_value)?;
            }
        }
    }
    Ok(res)
}

// extract_z_and_alpha function
fn extract_z_and_alpha(annotations: &[String]) -> Result<(BigUint, BigUint), HintError> {
    let annotations_str = annotations.join("\n");
    let re = Regex::new(
        r"V->P: /cpu air/STARK/Interaction: Interaction element #\d+: Field Element\(0x([0-9a-f]+)\)",
    )
    .map_err(|e| HintError::CustomHint(format!("Regex error: {}", e).into()))?;

    let mut interaction_elements = Vec::new();

    for caps in re.captures_iter(&annotations_str) {
        let hex_str = caps
            .get(1)
            .ok_or_else(|| {
                HintError::CustomHint(
                    "Failed to get capture group 1 in extract_z_and_alpha.".into(),
                )
            })?
            .as_str();
        let value = BigUint::from_str_radix(hex_str, 16).map_err(|_| {
            HintError::CustomHint(format!("Failed to parse hex_str '{}'", hex_str).into())
        })?;
        interaction_elements.push(value);
    }

    // Ensure the number of interaction elements is as expected
    if ![3, 6, 8].contains(&interaction_elements.len()) {
        return Err(HintError::CustomHint(
            format!(
                "Unexpected number of interaction elements: {}",
                interaction_elements.len()
            )
            .into(),
        ));
    }

    let z = interaction_elements[0].clone();
    let alpha = interaction_elements[1].clone();

    Ok((z, alpha))
}

pub fn extract_proof_values(
    proof: &HashMap<String, JsonValue>,
) -> Result<ExtractedProofValues, HintError> {
    // Extract annotations into a vector of strings
    let annotations_vec: Vec<String> = proof
        .get("annotations")
        .and_then(|v| v.as_array())
        .ok_or_else(|| HintError::CustomHint("Missing or invalid 'annotations' in proof.".into()))?
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();

    // Closure to extract annotations with given prefix and kind
    let annotations = |prefix: &str, kind: &str| -> Result<Vec<BigUint>, HintError> {
        extract_annotations(&annotations_vec, prefix, kind)
    };

    // Extract elements from annotations
    let original_commitment_hash_vec = annotations("STARK/Original/Commit on Trace", "Hash")?;
    let original_commitment_hash = original_commitment_hash_vec
        .first()
        .ok_or_else(|| HintError::CustomHint("Failed to get original commitment hash.".into()))?
        .clone();

    let interaction_commitment_hash_vec = annotations("STARK/Interaction/Commit on Trace", "Hash")?;
    let interaction_commitment_hash = interaction_commitment_hash_vec
        .first()
        .ok_or_else(|| HintError::CustomHint("Failed to get interaction commitment hash.".into()))?
        .clone();

    let composition_commitment_hash_vec =
        annotations("STARK/Out Of Domain Sampling/Commit on Trace", "Hash")?;
    let composition_commitment_hash = composition_commitment_hash_vec
        .first()
        .ok_or_else(|| HintError::CustomHint("Failed to get composition commitment hash.".into()))?
        .clone();

    let oods_values = annotations("STARK/Out Of Domain Sampling/OODS values", "Field Elements")?;

    let fri_layers_commitments = annotations("STARK/FRI/Commitment/Layer [0-9]+", "Hash")?;

    let fri_last_layer_coefficients =
        annotations("STARK/FRI/Commitment/Last Layer", "Field Elements")?;

    let proof_of_work_nonce_vec = annotations("STARK/FRI/Proof of Work", "Data")?;
    let proof_of_work_nonce = proof_of_work_nonce_vec
        .first()
        .ok_or_else(|| HintError::CustomHint("Failed to get proof of work nonce.".into()))?
        .clone();

    // Closure to collect authentication values
    let get_authentications = |prefix: &str| -> Result<Vec<BigUint>, HintError> {
        let mut res = annotations(prefix, "Data")?;
        res.extend(annotations(prefix, "Hash")?);
        Ok(res)
    };

    let original_witness_leaves = annotations(
        "STARK/FRI/Decommitment/Layer 0/Virtual Oracle/Trace 0",
        "Field Element",
    )?;

    let original_witness_authentications =
        get_authentications("STARK/FRI/Decommitment/Layer 0/Virtual Oracle/Trace 0")?;

    let interaction_witness_leaves = annotations(
        "STARK/FRI/Decommitment/Layer 0/Virtual Oracle/Trace 1",
        "Field Element",
    )?;

    let interaction_witness_authentications =
        get_authentications("STARK/FRI/Decommitment/Layer 0/Virtual Oracle/Trace 1")?;

    let composition_witness_leaves = annotations(
        "STARK/FRI/Decommitment/Layer 0/Virtual Oracle/Trace 2",
        "Field Element",
    )?;

    let composition_witness_authentications =
        get_authentications("STARK/FRI/Decommitment/Layer 0/Virtual Oracle/Trace 2")?;

    // Extract proof parameters
    let proof_parameters = proof
        .get("proof_parameters")
        .ok_or_else(|| HintError::CustomHint("Missing 'proof_parameters' in proof.".into()))?;

    let fri_step_list_json = proof_parameters["stark"]["fri"]["fri_step_list"]
        .as_array()
        .ok_or_else(|| {
            HintError::CustomHint("Missing or invalid 'fri_step_list' in proof parameters.".into())
        })?;

    let fri_step_list: Vec<u64> = fri_step_list_json
        .iter()
        .map(|v| {
            v.as_u64()
                .ok_or_else(|| HintError::CustomHint("Invalid 'fri_step_list' entry.".into()))
        })
        .collect::<Result<_, _>>()?;

    let n_fri_layers = fri_step_list.len();

    // Extract details for config
    let log_n_cosets = proof_parameters["stark"]["log_n_cosets"]
        .as_u64()
        .ok_or_else(|| {
            HintError::CustomHint("Missing or invalid 'log_n_cosets' in proof parameters.".into())
        })?;

    let last_layer_degree_bound = proof_parameters["stark"]["fri"]["last_layer_degree_bound"]
        .as_u64()
        .ok_or_else(|| {
            HintError::CustomHint(
                "Missing or invalid 'last_layer_degree_bound' in proof parameters.".into(),
            )
        })?;

    let log_last_layer_degree_bound = safe_log2(last_layer_degree_bound)?;

    let n_verifier_friendly_commitment_layers = proof_parameters
        .get("n_verifier_friendly_commitment_layers")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    // Extract additional proof parameters
    let proof_of_work_bits = proof_parameters["stark"]["fri"]["proof_of_work_bits"]
        .as_u64()
        .ok_or_else(|| {
            HintError::CustomHint(
                "Missing or invalid 'proof_of_work_bits' in proof parameters.".into(),
            )
        })?;

    let n_queries = proof_parameters["stark"]["fri"]["n_queries"]
        .as_u64()
        .ok_or_else(|| {
            HintError::CustomHint("Missing or invalid 'n_queries' in proof parameters.".into())
        })?;

    // Extract z and alpha from annotations
    let (z, alpha) = extract_z_and_alpha(&annotations_vec)?;

    // Extract FRI witnesses leaves and authentications
    let mut fri_witnesses_leaves: Vec<Vec<BigUint>> = Vec::new();
    let mut fri_witnesses_authentications: Vec<Vec<BigUint>> = Vec::new();

    for i in 1..n_fri_layers {
        let prefix = &format!("STARK/FRI/Decommitment/Layer {}", i);
        let leaves = annotations(prefix, "Field Element")?;
        let authentications = annotations(prefix, "Hash")?;
        fri_witnesses_leaves.push(leaves);
        fri_witnesses_authentications.push(authentications);
    }

    // FRI layers assertion
    if fri_layers_commitments.len() != n_fri_layers - 1 {
        return Err(HintError::CustomHint(
            format!(
                "FRI layers commitments length mismatch: expected {}, got {}",
                n_fri_layers - 1,
                fri_layers_commitments.len()
            )
            .into(),
        ));
    }

    // Return the extracted values as a struct
    Ok(ExtractedProofValues {
        original_commitment_hash,
        interaction_commitment_hash,
        composition_commitment_hash,
        oods_values,
        fri_layers_commitments,
        fri_last_layer_coefficients,
        proof_of_work_nonce,
        original_witness_leaves,
        original_witness_authentications,
        interaction_witness_leaves,
        interaction_witness_authentications,
        composition_witness_leaves,
        composition_witness_authentications,
        fri_step_list,
        n_fri_layers,
        log_n_cosets,
        log_last_layer_degree_bound,
        n_verifier_friendly_commitment_layers,
        z,
        alpha,
        proof_of_work_bits,
        n_queries,
        fri_witnesses_leaves,
        fri_witnesses_authentications,
    })
}

fn get_dynamic_or_const_value(
    dynamic_params: Option<&HashMap<String, u128>>,
    name: &str,
    identifiers: &HashMap<String, Identifier>,
    module_name: &str,
) -> Result<BigUint, HintError> {
    let name_lower = name.to_lowercase();

    // Check dynamic_params
    if let Some(dynamic_params) = dynamic_params {
        if let Some(value) = dynamic_params.get(&name_lower) {
            return Ok((*value).into());
        }
    }

    // Construct the full identifier name
    let full_name = format!("{}.{}", module_name, name);

    // Retrieve the identifier from identifiers
    if let Some(identifier) = identifiers.get(&full_name) {
        // Check if the identifier is a constant
        if let Some(type_) = &identifier.type_ {
            if type_ != "const" {
                return Err(HintError::CustomHint(
                    format!("Identifier '{}' is not a constant.", full_name).into(),
                ));
            }
        }

        // Convert Felt252 value to BigUint if available
        if let Some(felt_value) = &identifier.value {
            let big_uint: BigUint = felt_value.to_biguint();
            return Ok(big_uint);
        } else {
            // If the identifier exists but has no value, return an error
            return Err(HintError::CustomHint(
                format!("Identifier '{}' has no value.", full_name).into(),
            ));
        }
    }

    // If the identifier wasn't found in `dynamic_params` or `identifiers`
    Err(HintError::CustomHint(
        format!(
            "Identifier '{}' not found in dynamic_params or identifiers.",
            name
        )
        .into(),
    ))
}

pub fn extract_from_ids_and_public_input(
    public_input: &OwnedPublicInput,
    identifiers: &HashMap<String, Identifier>,
    extracted_values: &ExtractedProofValues,
) -> Result<ExtractedIDsAndInputValues, HintError> {
    // Extract module_name inside the function
    let module_name = format!(
        "starkware.cairo.stark_verifier.air.layouts.{}.autogenerated",
        public_input.layout
    );

    // dynamic_params from public_input
    let dynamic_params = public_input.dynamic_params.as_ref();

    // Retrieve CPU_COMPONENT_STEP
    let cpu_component_step = get_dynamic_or_const_value(
        dynamic_params,
        "CPU_COMPONENT_STEP",
        identifiers,
        &module_name,
    )?;

    let effective_component_height = BigUint::from(COMPONENT_HEIGHT) * &cpu_component_step;

    // Compute log_trace_domain_size
    let n_steps = BigUint::from(public_input.n_steps);
    let trace_domain_size = &effective_component_height * &n_steps;
    let trace_domain_size_u64 = trace_domain_size
        .to_u64()
        .ok_or_else(|| HintError::CustomHint("trace_domain_size is too large.".into()))?;
    let log_trace_domain_size = safe_log2(trace_domain_size_u64)?;

    // Get log_n_cosets from extracted_values
    let log_n_cosets = extracted_values.log_n_cosets;

    // Compute log_eval_domain_size
    let log_eval_domain_size = log_trace_domain_size + log_n_cosets as u32;

    // Retrieve fri_step_list from extracted_values
    let fri_step_list = &extracted_values.fri_step_list;

    // Initialize layer_log_sizes
    let mut layer_log_sizes = vec![log_eval_domain_size];

    // Compute layer_log_sizes
    for &layer_step in fri_step_list {
        let last_size = *layer_log_sizes
            .last()
            .ok_or_else(|| HintError::CustomHint("layer_log_sizes is empty.".into()))?;
        layer_log_sizes.push(last_size - layer_step as u32);
    }

    // Get n_fri_layers from extracted_values
    let n_fri_layers = extracted_values.n_fri_layers;

    // Assertions
    if layer_log_sizes.len() != n_fri_layers + 1 {
        return Err(HintError::CustomHint(
            format!(
                "layer_log_sizes length mismatch: expected {}, got {}",
                n_fri_layers + 1,
                layer_log_sizes.len()
            )
            .into(),
        ));
    }

    // Get log_last_layer_degree_bound from extracted_values
    let log_last_layer_degree_bound = extracted_values.log_last_layer_degree_bound;

    if *layer_log_sizes.last().unwrap() != log_last_layer_degree_bound + log_n_cosets as u32 {
        return Err(HintError::CustomHint(
            format!(
                "Last layer log size mismatch: expected {}, got {}",
                log_last_layer_degree_bound + log_n_cosets as u32,
                layer_log_sizes.last().unwrap()
            )
            .into(),
        ));
    }

    let fri_last_layer_coefficients = &extracted_values.fri_last_layer_coefficients;

    if fri_last_layer_coefficients.len() != (1 << log_last_layer_degree_bound) {
        return Err(HintError::CustomHint(
            format!(
                "FRI last layer coefficients length mismatch: expected {}, got {}",
                1 << log_last_layer_degree_bound,
                fri_last_layer_coefficients.len()
            )
            .into(),
        ));
    }

    // Retrieve NUM_COLUMNS_FIRST
    let num_columns_first = get_dynamic_or_const_value(
        dynamic_params,
        "NUM_COLUMNS_FIRST",
        identifiers,
        &module_name,
    )?;

    // Retrieve NUM_COLUMNS_SECOND
    let num_columns_second = get_dynamic_or_const_value(
        dynamic_params,
        "NUM_COLUMNS_SECOND",
        identifiers,
        &module_name,
    )?;

    // Retrieve CONSTRAINT_DEGREE (dynamic_params is None)
    let constraint_degree =
        get_dynamic_or_const_value(None, "CONSTRAINT_DEGREE", identifiers, &module_name)?;

    // Return the computed values in ExtractedIDsAndInputValues
    Ok(ExtractedIDsAndInputValues {
        log_trace_domain_size,
        log_eval_domain_size,
        layer_log_sizes,
        num_columns_first,
        num_columns_second,
        constraint_degree,
    })
}

pub fn get_stark_proof_cairo_struct(
    extracted_proof_vals: &ExtractedProofValues,
    extracted_ids_and_pub_in_vals: &ExtractedIDsAndInputValues,
    public_input: &OwnedPublicInput,
) -> Result<StarkProof, HintError> {
    // Placeholder for cairo_public_input
    let cairo_public_input = public_input_to_cairo(
        public_input,
        &extracted_proof_vals.z,
        &extracted_proof_vals.alpha,
    )?;
    // Instantiate StarkConfig
    let stark_config = StarkConfig {
        traces: TracesConfig {
            original: TableCommitmentConfig {
                n_columns: extracted_ids_and_pub_in_vals
                    .num_columns_first
                    .clone()
                    .into(),
                vector: VectorCommitmentConfig {
                    height: extracted_ids_and_pub_in_vals.log_eval_domain_size.into(),
                    n_verifier_friendly_commitment_layers: extracted_proof_vals
                        .n_verifier_friendly_commitment_layers
                        .into(),
                },
            },
            interaction: TableCommitmentConfig {
                n_columns: extracted_ids_and_pub_in_vals
                    .num_columns_second
                    .clone()
                    .into(),
                vector: VectorCommitmentConfig {
                    height: extracted_ids_and_pub_in_vals.log_eval_domain_size.into(),
                    n_verifier_friendly_commitment_layers: extracted_proof_vals
                        .n_verifier_friendly_commitment_layers
                        .into(),
                },
            },
        },
        composition: TableCommitmentConfig {
            n_columns: extracted_ids_and_pub_in_vals
                .constraint_degree
                .clone()
                .into(),
            vector: VectorCommitmentConfig {
                height: extracted_ids_and_pub_in_vals.log_eval_domain_size.into(),
                n_verifier_friendly_commitment_layers: extracted_proof_vals
                    .n_verifier_friendly_commitment_layers
                    .into(),
            },
        },
        fri: FriConfig {
            log_input_size: extracted_ids_and_pub_in_vals.layer_log_sizes[0].into(),
            n_layers: extracted_proof_vals.n_fri_layers.into(),
            inner_layers: {
                // Build inner_layers
                let mut inner_layers = Vec::new();
                for (&layer_steps, &layer_log_rows) in extracted_proof_vals
                    .fri_step_list
                    .iter()
                    .skip(1)
                    .zip(&extracted_ids_and_pub_in_vals.layer_log_sizes[2..])
                {
                    inner_layers.push(TableCommitmentConfig {
                        n_columns: Felt252::from(1u64 << layer_steps),
                        vector: VectorCommitmentConfig {
                            height: layer_log_rows.into(),
                            n_verifier_friendly_commitment_layers: extracted_proof_vals
                                .n_verifier_friendly_commitment_layers
                                .into(),
                        },
                    });
                }
                inner_layers
            },
            fri_step_sizes: extracted_proof_vals
                .fri_step_list
                .iter()
                .map(|&x| Felt252::from(x))
                .collect(),
            log_last_layer_degree_bound: extracted_proof_vals.log_last_layer_degree_bound.into(),
        },
        proof_of_work: ProofOfWorkConfig {
            n_bits: extracted_proof_vals.proof_of_work_bits.into(),
        },
        log_trace_domain_size: extracted_ids_and_pub_in_vals.log_trace_domain_size.into(),
        n_queries: extracted_proof_vals.n_queries.into(),
        log_n_cosets: extracted_proof_vals.log_n_cosets.into(),
        n_verifier_friendly_commitment_layers: extracted_proof_vals
            .n_verifier_friendly_commitment_layers
            .into(),
    };

    // Instantiate StarkUnsentCommitment
    let stark_unsent_commitment = StarkUnsentCommitment {
        traces: TracesUnsentCommitment {
            original: extracted_proof_vals.original_commitment_hash.clone().into(),
            interaction: extracted_proof_vals
                .interaction_commitment_hash
                .clone()
                .into(),
        },
        composition: extracted_proof_vals
            .composition_commitment_hash
            .clone()
            .into(),
        oods_values: extracted_proof_vals
            .oods_values
            .iter()
            .map(|v| Felt252::from(v.clone()))
            .collect(),
        fri: FriUnsentCommitment {
            inner_layers: extracted_proof_vals
                .fri_layers_commitments
                .iter()
                .map(|v| Felt252::from(v.clone()))
                .collect(),
            last_layer_coefficients: extracted_proof_vals
                .fri_last_layer_coefficients
                .iter()
                .map(|v| Felt252::from(v.clone()))
                .collect(),
        },
        proof_of_work: ProofOfWorkUnsentCommitment {
            nonce: extracted_proof_vals.proof_of_work_nonce.clone().into(),
        },
    };

    // Instantiate FriWitness layers
    let mut fri_witnesses = Vec::new();

    for (leaves, authentications) in extracted_proof_vals
        .fri_witnesses_leaves
        .iter()
        .zip(&extracted_proof_vals.fri_witnesses_authentications)
    {
        fri_witnesses.push(FriLayerWitness {
            n_leaves: leaves.len().into(),
            leaves: leaves.iter().map(|v| Felt252::from(v.clone())).collect(),
            table_witness: TableCommitmentWitness {
                vector: VectorCommitmentWitness {
                    n_authentications: authentications.len().into(),
                    authentications: authentications
                        .iter()
                        .map(|v| Felt252::from(v.clone()))
                        .collect(),
                },
            },
        });
    }

    // Instantiate StarkWitness
    let stark_witness = StarkWitness {
        traces_decommitment: TracesDecommitment {
            original: TableDecommitment {
                n_values: extracted_proof_vals.original_witness_leaves.len().into(),
                values: extracted_proof_vals
                    .original_witness_leaves
                    .iter()
                    .map(|v| Felt252::from(v.clone()))
                    .collect(),
            },
            interaction: TableDecommitment {
                n_values: extracted_proof_vals.interaction_witness_leaves.len().into(),
                values: extracted_proof_vals
                    .interaction_witness_leaves
                    .iter()
                    .map(|v| Felt252::from(v.clone()))
                    .collect(),
            },
        },
        traces_witness: TracesWitness {
            original: TableCommitmentWitness {
                vector: VectorCommitmentWitness {
                    n_authentications: extracted_proof_vals
                        .original_witness_authentications
                        .len()
                        .into(),
                    authentications: extracted_proof_vals
                        .original_witness_authentications
                        .iter()
                        .map(|v| Felt252::from(v.clone()))
                        .collect(),
                },
            },
            interaction: TableCommitmentWitness {
                vector: VectorCommitmentWitness {
                    n_authentications: extracted_proof_vals
                        .interaction_witness_authentications
                        .len()
                        .into(),
                    authentications: extracted_proof_vals
                        .interaction_witness_authentications
                        .iter()
                        .map(|v| Felt252::from(v.clone()))
                        .collect(),
                },
            },
        },
        composition_decommitment: TableDecommitment {
            n_values: extracted_proof_vals.composition_witness_leaves.len().into(),
            values: extracted_proof_vals
                .composition_witness_leaves
                .iter()
                .map(|v| Felt252::from(v.clone()))
                .collect(),
        },
        composition_witness: TableCommitmentWitness {
            vector: VectorCommitmentWitness {
                n_authentications: extracted_proof_vals
                    .composition_witness_authentications
                    .len()
                    .into(),
                authentications: extracted_proof_vals
                    .composition_witness_authentications
                    .iter()
                    .map(|v| Felt252::from(v.clone()))
                    .collect(),
            },
        },
        fri_witness: FriWitness {
            layers: fri_witnesses,
        },
    };

    // Instantiate StarkProof
    let stark_proof = StarkProof {
        config: stark_config,
        public_input: cairo_public_input,
        unsent_commitment: stark_unsent_commitment,
        witness: stark_witness,
    };

    Ok(stark_proof)
}

pub fn public_input_to_cairo(
    public_input: &OwnedPublicInput,
    z: &BigUint,
    alpha: &BigUint,
) -> Result<CairoPublicInput, HintError> {
    // Compute continuous_page_headers
    let continuous_page_headers =
        compute_continuous_page_headers(&public_input.public_memory, z, alpha)?;

    // Compute main_page
    let main_page = get_main_page(&public_input.public_memory)?;

    // Handle dynamic_params
    let dynamic_params = if let Some(dynamic_params_map) = &public_input.dynamic_params {
        let mut dynamic_params_vec: Vec<(&String, &u128)> = dynamic_params_map.iter().collect();
        dynamic_params_vec.sort_by(|a, b| a.0.cmp(b.0));
        dynamic_params_vec.iter().map(|(_k, v)| *(*v)).collect()
    } else {
        Vec::new()
    };

    // Sort memory_segments
    let memory_segments = sort_segments(&public_input.memory_segments)?;

    // Compute log_n_steps
    let log_n_steps: Felt252 = safe_log2(public_input.n_steps as u64)?.into();

    // Range check min and max
    let range_check_min = public_input.rc_min;
    let range_check_max = public_input.rc_max;

    // Compute layout as BigUint
    let layout_bytes = public_input.layout.as_bytes();
    let layout = BigUint::from_bytes_be(layout_bytes);

    // n_segments
    let n_segments = public_input.memory_segments.len();

    // Segments
    let mut segments = memory_segments
        .values()
        .map(|elm| {
            Ok(SegmentInfo {
                begin_addr: elm.begin_addr.into(),
                stop_ptr: elm.stop_ptr.into(),
            })
        })
        .collect::<Result<Vec<SegmentInfo>, HintError>>()?;
    segments.sort_by(|a, b| {
        a.begin_addr
            .cmp(&b.begin_addr)
            .then(a.stop_ptr.cmp(&b.stop_ptr))
    });

    // Padding address and value
    let first_public_memory_entry = public_input.public_memory.first().ok_or_else(|| {
        HintError::CustomHint(
            "Public memory is empty; cannot get padding address and value.".into(),
        )
    })?;

    let padding_addr = first_public_memory_entry.address;
    let padding_value = first_public_memory_entry.value.unwrap_or_default();

    // Main page length and flatten main_page
    let main_page_len = main_page.len();

    let main_page_flat: Vec<Felt252> = main_page
        .into_iter()
        .flat_map(|(address, value)| vec![Felt252::from(address), value])
        .collect();
    // Number of continuous pages and flatten continuous_page_headers
    let n_continuous_pages = continuous_page_headers.len();

    let continuous_page_headers_flat: Vec<Felt252> = continuous_page_headers
        .into_iter()
        .flat_map(|(start_addr, size, hash_value, product)| {
            vec![
                Felt252::from(start_addr),
                Felt252::from(size),
                hash_value,
                product,
            ]
        })
        .collect();

    // Create CairoPublicInput
    let cairo_public_input = CairoPublicInput {
        log_n_steps,
        range_check_min: range_check_min.into(),
        range_check_max: range_check_max.into(),
        layout: layout.into(),
        dynamic_params: dynamic_params.into_iter().map(Felt252::from).collect(),
        n_segments: n_segments.into(),
        segments,
        padding_addr: padding_addr.into(),
        padding_value,
        main_page_len: main_page_len.into(),
        main_page: main_page_flat,
        n_continuous_pages: n_continuous_pages.into(),
        continuous_page_headers: continuous_page_headers_flat,
    };

    Ok(cairo_public_input)
}

// Make Clippy happy - making the output type of `get_pages_and_products` more readable.
type PageMap = HashMap<u32, Vec<Felt252>>;
type ProductMap = HashMap<u32, Felt252>;
type PagesAndProductsResult = Result<(PageMap, ProductMap), HintError>;

pub fn get_pages_and_products(
    public_memory: &[PublicMemoryEntry],
    z: &BigUint,
    alpha: &BigUint,
) -> PagesAndProductsResult {
    let mut pages: HashMap<u32, Vec<Felt252>> = HashMap::new();
    let mut page_prods: HashMap<u32, Felt252> = HashMap::new();

    for cell in public_memory.iter() {
        let page_id = cell.page;
        let addr = cell.address;
        let val = cell.value.ok_or_else(|| {
            HintError::CustomHint(
                format!(
                    "Value is missing in public memory entry at address {}.",
                    addr
                )
                .into(),
            )
        })?;

        // For pages
        let page = pages.entry(page_id as u32).or_default();
        page.push(addr.into());
        page.push(val);

        // For page_prods
        let previous_prod = page_prods.entry(page_id as u32).or_insert(Felt252::ONE);

        // Compute term = z - (addr + alpha * val)
        let term = Felt252::from(z) - (Felt252::from(addr) + (Felt252::from(alpha) * val));

        // Update page_prods[page_id] = previous_prod * term
        *previous_prod *= term;
    }

    Ok((pages, page_prods))
}

pub fn compute_continuous_page_headers(
    public_memory: &[PublicMemoryEntry],
    z: &BigUint,
    alpha: &BigUint,
) -> Result<Vec<(usize, usize, Felt252, Felt252)>, HintError> {
    let mut start_address: HashMap<u32, usize> = HashMap::new();
    let mut size: HashMap<u32, usize> = HashMap::new();
    let mut data: HashMap<u32, Vec<Felt252>> = HashMap::new();

    let (_pages, page_prods) = get_pages_and_products(public_memory, z, alpha)?;

    for access in public_memory.iter() {
        let page_id = access.page;
        let address = access.address;
        let value = access.value;

        // Set start_address if not already set
        start_address.entry(page_id as u32).or_insert(address);

        if page_id == 0 {
            continue;
        }

        let page_data = data.entry(page_id as u32).or_default();

        // Compute expected address: start_address[page_id] + data[page_id].len()
        let expected_address = start_address[&(page_id as u32)] + page_data.len();

        // Ensure access.address == expected_address
        if address != expected_address {
            return Err(HintError::CustomHint(
                format!(
                    "Address mismatch for page {}: expected {}, got {}",
                    page_id, expected_address, address
                )
                .into(),
            ));
        }

        page_data.push(value.ok_or_else(|| {
            HintError::CustomHint(
                format!(
                    "Value is missing for address {} on page {}.",
                    address, page_id
                )
                .into(),
            )
        })?);

        // Increment size[page_id]
        *size.entry(page_id as u32).or_insert(0) += 1;
    }

    let n_pages = 1 + size.len();

    if page_prods.len() != n_pages {
        return Err(HintError::CustomHint(
            format!(
                "Page products length mismatch: expected {}, got {}",
                n_pages,
                page_prods.len()
            )
            .into(),
        ));
    }

    // Build headers
    let mut headers = Vec::new();

    let mut sorted_pages: Vec<&u32> = size.keys().collect();
    sorted_pages.sort();

    for (i, &page_id) in sorted_pages.iter().enumerate() {
        let page_index = i + 1;
        if page_index as u32 != *page_id {
            return Err(HintError::CustomHint(
                format!(
                    "Page IDs are not consecutive: expected {}, got {}",
                    page_index, page_id
                )
                .into(),
            ));
        }

        let page_data = data.get(page_id).ok_or_else(|| {
            HintError::CustomHint(format!("Data for page {} not found.", page_id).into())
        })?;

        let hash_value = Pedersen::hash_array(page_data);

        let header = (
            start_address[page_id],
            size[page_id],
            hash_value,
            page_prods[page_id],
        );

        headers.push(header);
    }

    Ok(headers)
}

pub fn get_main_page(
    public_memory: &[PublicMemoryEntry],
) -> Result<Vec<(usize, Felt252)>, HintError> {
    let mut res = Vec::new();

    for access in public_memory.iter() {
        if access.page != 0 {
            continue;
        }
        if let Some(value) = access.value {
            res.push((access.address, value));
        } else {
            return Err(HintError::CustomHint(
                format!(
                    "Value is missing for address {} on main page.",
                    access.address
                )
                .into(),
            ));
        }
    }

    Ok(res)
}

pub fn sort_segments(
    memory_segments: &HashMap<String, MemorySegmentAddresses>,
) -> Result<HashMap<String, &MemorySegmentAddresses>, HintError> {
    // Define the desired serialization order with "program" and "execution"
    let mut segment_names = vec!["program".to_string(), "execution".to_string()];

    let builtin_ordered_list = [
        BuiltinName::output,
        BuiltinName::pedersen,
        BuiltinName::range_check,
        BuiltinName::ecdsa,
        BuiltinName::bitwise,
        BuiltinName::ec_op,
        BuiltinName::keccak,
        BuiltinName::poseidon,
        BuiltinName::range_check96,
        BuiltinName::add_mod,
        BuiltinName::mul_mod,
    ];
    // Add built-in names based on `builtin_ordered_list`
    segment_names.extend(builtin_ordered_list.iter().filter_map(|builtin| {
        let name = format!("{:?}", builtin); // Convert enum to string
        if memory_segments.contains_key(&name) {
            Some(name)
        } else {
            None
        }
    }));

    // Collect segments in the defined order
    let mut sorted_segments = HashMap::new();
    for name in &segment_names {
        if let Some(segment) = memory_segments.get(name) {
            sorted_segments.insert(name.clone(), segment);
        }
    }

    // Validate the segment count
    if sorted_segments.len() != memory_segments.len() {
        return Err(HintError::CustomHint(
            format!(
                "Wrong segments given. Expected segments: {:?}, but got: {:?}",
                memory_segments.keys().collect::<Vec<_>>(),
                sorted_segments.keys().collect::<Vec<_>>()
            )
            .into(),
        ));
    }

    Ok(sorted_segments)
}
