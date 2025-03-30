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
use num_traits::ToPrimitive;
use regex::Regex;
use starknet_types_core::hash::{Pedersen, StarkHash};

/// Computes the base-2 logarithm of a power-of-two number.
///
/// # Arguments
///
/// * `x` - A `u128` integer which must be a power of two.
///
/// # Returns
///
/// Returns `Ok` containing the logarithm value if `x` is a power of two,
/// or an error `HintError` if `x` is not a power of two.
///
/// # Errors
///
/// Returns `HintError::CustomHint` if `x` is not a power of two.
pub fn safe_log2(x: u128) -> Result<u32, HintError> {
    if x.is_power_of_two() {
        Ok(x.trailing_zeros())
    } else {
        Err(HintError::CustomHint(
            format!("safe_log2: Input {} is not a power of two.", x).into(),
        ))
    }
}

/// Extracts annotations from a list of strings based on a given prefix and kind.
///
/// # Arguments
///
/// * `annotations` - A slice of strings containing annotations to be processed.
/// * `prefix` - The prefix string to match in the annotations.
/// * `kind` - The kind of data to extract from the annotations.
///
/// # Returns
///
/// Returns a `Result` containing a vector of `Felt252` values extracted from the annotations.
///
/// # Errors
///
/// Returns a `HintError` if there is a regex error or if parsing of values fails.
pub fn extract_annotations(
    annotations: &[String],
    prefix: &str,
    kind: &str,
) -> Result<Vec<Felt252>, HintError> {
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
                let value_str = value_str.trim();
                let value = Felt252::from_hex(value_str).map_err(|_| {
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

/// Extracts the interaction elements z and alpha from the annotations.
///
/// # Arguments
///
/// * `annotations` - A slice of strings containing the annotations.
///
/// # Returns
///
/// Returns a `Result` containing a tuple `(z, alpha)` of `Felt252` values.
///
/// # Errors
///
/// Returns a `HintError` if the regex fails or if the expected number of interaction elements is
/// not found.
fn extract_z_and_alpha(annotations: &[String]) -> Result<(Felt252, Felt252), HintError> {
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
        let value = Felt252::from_hex(hex_str).map_err(|_| {
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

    let z = interaction_elements[0];
    let alpha = interaction_elements[1];

    Ok((z, alpha))
}

/// Extracts proof values from the given proof data.
///
/// # Arguments
///
/// * `proof` - A reference to a `HashMap` containing proof data.
///
/// # Returns
///
/// Returns a `Result` containing an `ExtractedProofValues` struct with extracted values.
///
/// # Errors
///
/// Returns a `HintError` if required data is missing or cannot be parsed.
pub fn extract_proof_values(
    proof: &HashMap<String, JsonValue>,
) -> Result<ExtractedProofValues, HintError> {
    let annotations_vec: Vec<String> = proof
        .get("annotations")
        .and_then(|v| v.as_array())
        .ok_or_else(|| HintError::CustomHint("Missing or invalid 'annotations' in proof.".into()))?
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();

    let annotations = |prefix: &str, kind: &str| -> Result<Vec<Felt252>, HintError> {
        extract_annotations(&annotations_vec, prefix, kind)
    };

    let original_commitment_hash_vec = annotations("STARK/Original/Commit on Trace", "Hash")?;
    let original_commitment_hash = original_commitment_hash_vec
        .first()
        .ok_or_else(|| HintError::CustomHint("Failed to get original commitment hash.".into()))?;

    let interaction_commitment_hash_vec = annotations("STARK/Interaction/Commit on Trace", "Hash")?;
    let interaction_commitment_hash = interaction_commitment_hash_vec.first().ok_or_else(|| {
        HintError::CustomHint("Failed to get interaction commitment hash.".into())
    })?;

    let composition_commitment_hash_vec =
        annotations("STARK/Out Of Domain Sampling/Commit on Trace", "Hash")?;
    let composition_commitment_hash = composition_commitment_hash_vec.first().ok_or_else(|| {
        HintError::CustomHint("Failed to get composition commitment hash.".into())
    })?;

    let oods_values = annotations("STARK/Out Of Domain Sampling/OODS values", "Field Elements")?;

    let fri_layers_commitments = annotations("STARK/FRI/Commitment/Layer [0-9]+", "Hash")?;

    let fri_last_layer_coefficients =
        annotations("STARK/FRI/Commitment/Last Layer", "Field Elements")?;

    let proof_of_work_nonce_vec = annotations("STARK/FRI/Proof of Work", "Data")?;
    let proof_of_work_nonce = proof_of_work_nonce_vec
        .first()
        .ok_or_else(|| HintError::CustomHint("Failed to get proof of work nonce.".into()))?;

    // Closure to collect authentication values
    let get_authentications = |prefix: &str| -> Result<Vec<Felt252>, HintError> {
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

    let log_last_layer_degree_bound = safe_log2(last_layer_degree_bound.into())?;

    let n_verifier_friendly_commitment_layers = proof_parameters
        .get("n_verifier_friendly_commitment_layers")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

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

    let (z, alpha) = extract_z_and_alpha(&annotations_vec)?;

    let mut fri_witnesses_leaves: Vec<Vec<Felt252>> = Vec::new();
    let mut fri_witnesses_authentications: Vec<Vec<Felt252>> = Vec::new();

    for i in 1..n_fri_layers {
        let prefix = &format!("STARK/FRI/Decommitment/Layer {}", i);
        let leaves = annotations(prefix, "Field Element")?;
        let authentications = annotations(prefix, "Hash")?;
        fri_witnesses_leaves.push(leaves);
        fri_witnesses_authentications.push(authentications);
    }

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

    Ok(ExtractedProofValues {
        original_commitment_hash: *original_commitment_hash,
        interaction_commitment_hash: *interaction_commitment_hash,
        composition_commitment_hash: *composition_commitment_hash,
        oods_values,
        fri_layers_commitments,
        fri_last_layer_coefficients,
        proof_of_work_nonce: *proof_of_work_nonce,
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

/// Retrieves a value from dynamic parameters or constants from identifiers.
///
/// # Arguments
///
/// * `dynamic_params` - An optional reference to a `HashMap` of dynamic parameters.
/// * `name` - The name of the parameter or constant to retrieve.
/// * `identifiers` - A `HashMap` containing the verifier program's identifiers.
/// * `module_name` - The name of the module where the constant might be defined.
///
/// # Returns
///
/// Returns a `Result` containing the `Felt252` value if found.
///
/// # Errors
///
/// Returns a `HintError` if the identifier is not found or if it is not a constant.
fn get_dynamic_or_const_value(
    dynamic_params: Option<&HashMap<String, u128>>,
    name: &str,
    identifiers: &HashMap<String, Identifier>,
    module_name: &str,
) -> Result<Felt252, HintError> {
    let name_lower = name.to_lowercase();

    if let Some(dynamic_params) = dynamic_params {
        if let Some(value) = dynamic_params.get(&name_lower) {
            return Ok((*value).into());
        }
    }

    let full_name = format!("{}.{}", module_name, name);

    if let Some(identifier) = identifiers.get(&full_name) {
        // Check if the identifier is a constant
        if let Some(type_) = &identifier.type_ {
            if type_ != "const" {
                return Err(HintError::CustomHint(
                    format!("Identifier '{}' is not a constant.", full_name).into(),
                ));
            }
        }

        if let Some(felt_value) = &identifier.value {
            return Ok(*felt_value);
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

/// Extracts values from IDs and public input required for proof verification.
///
/// # Arguments
///
/// * `public_input` - A reference to `OwnedPublicInput`, containing the public input data of the
///   prover.
/// * `identifiers` - A `HashMap` containing the verifier program's identifiers.
/// * `extracted_values` - A reference to `ExtractedProofValues` containing previously extracted
///   values.
///
/// # Returns
///
/// Returns a `Result` containing an `ExtractedIDsAndInputValues` struct with extracted values.
///
/// # Errors
///
/// Returns a `HintError` if required identifiers or values are missing or cannot be computed.
pub fn extract_from_ids_and_public_input(
    public_input: &OwnedPublicInput,
    identifiers: &HashMap<String, Identifier>,
    extracted_values: &ExtractedProofValues,
) -> Result<ExtractedIDsAndInputValues, HintError> {
    let module_name = format!(
        "starkware.cairo.stark_verifier.air.layouts.{}.autogenerated",
        public_input.layout
    );

    let dynamic_params = public_input.dynamic_params.as_ref();

    let cpu_component_step = get_dynamic_or_const_value(
        dynamic_params,
        "CPU_COMPONENT_STEP",
        identifiers,
        &module_name,
    )?;

    let effective_component_height = Felt252::from(COMPONENT_HEIGHT) * cpu_component_step;

    let n_steps = Felt252::from(public_input.n_steps);
    let trace_domain_size = effective_component_height * n_steps;
    let trace_domain_size_u64 = trace_domain_size
        .to_u128()
        .ok_or_else(|| HintError::CustomHint("trace_domain_size is too large.".into()))?;
    let log_trace_domain_size = safe_log2(trace_domain_size_u64)?;

    let log_n_cosets = extracted_values.log_n_cosets;

    let log_eval_domain_size = log_trace_domain_size + log_n_cosets as u32;

    let fri_step_list = &extracted_values.fri_step_list;

    let mut layer_log_sizes = vec![log_eval_domain_size];

    for &layer_step in fri_step_list {
        let last_size = *layer_log_sizes
            .last()
            .ok_or_else(|| HintError::CustomHint("layer_log_sizes is empty.".into()))?;
        layer_log_sizes.push(last_size - layer_step as u32);
    }

    let n_fri_layers = extracted_values.n_fri_layers;

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

    let num_columns_first = get_dynamic_or_const_value(
        dynamic_params,
        "NUM_COLUMNS_FIRST",
        identifiers,
        &module_name,
    )?;

    let num_columns_second = get_dynamic_or_const_value(
        dynamic_params,
        "NUM_COLUMNS_SECOND",
        identifiers,
        &module_name,
    )?;

    let constraint_degree =
        get_dynamic_or_const_value(None, "CONSTRAINT_DEGREE", identifiers, &module_name)?;

    Ok(ExtractedIDsAndInputValues {
        log_trace_domain_size: log_trace_domain_size.into(),
        log_eval_domain_size: log_eval_domain_size.into(),
        layer_log_sizes: layer_log_sizes.into_iter().map(|x| x.into()).collect(),
        num_columns_first,
        num_columns_second,
        constraint_degree,
    })
}

/// Constructs a `StarkProof` struct from extracted proof values and public input.
///
/// # Arguments
///
/// * `extracted_proof_vals` - A reference to `ExtractedProofValues`.
/// * `extracted_ids_and_pub_in_vals` - A reference to `ExtractedIDsAndInputValues`.
/// * `public_input` - A reference to `OwnedPublicInput`.
///
/// # Returns
///
/// Returns a `Result` containing the constructed `StarkProof` (this struct corresponds to the cairo
/// struct of the same name).
///
/// # Errors
///
/// Returns a `HintError` if the proof cannot be constructed due to missing data or inconsistencies.
pub fn get_stark_proof_cairo_struct(
    extracted_proof_vals: &ExtractedProofValues,
    extracted_ids_and_pub_in_vals: &ExtractedIDsAndInputValues,
    public_input: &OwnedPublicInput,
) -> Result<StarkProof, HintError> {
    // Instantiate CairoPublicInput based on public_input
    let cairo_public_input = public_input_to_cairo(
        public_input,
        &extracted_proof_vals.z,
        &extracted_proof_vals.alpha,
    )?;
    // Instantiate StarkConfig
    let stark_config = StarkConfig {
        traces: TracesConfig {
            original: TableCommitmentConfig {
                n_columns: extracted_ids_and_pub_in_vals.num_columns_first,
                vector: VectorCommitmentConfig {
                    height: extracted_ids_and_pub_in_vals.log_eval_domain_size,
                    n_verifier_friendly_commitment_layers: extracted_proof_vals
                        .n_verifier_friendly_commitment_layers
                        .into(),
                },
            },
            interaction: TableCommitmentConfig {
                n_columns: extracted_ids_and_pub_in_vals.num_columns_second,
                vector: VectorCommitmentConfig {
                    height: extracted_ids_and_pub_in_vals.log_eval_domain_size,
                    n_verifier_friendly_commitment_layers: extracted_proof_vals
                        .n_verifier_friendly_commitment_layers
                        .into(),
                },
            },
        },
        composition: TableCommitmentConfig {
            n_columns: extracted_ids_and_pub_in_vals.constraint_degree,
            vector: VectorCommitmentConfig {
                height: extracted_ids_and_pub_in_vals.log_eval_domain_size,
                n_verifier_friendly_commitment_layers: extracted_proof_vals
                    .n_verifier_friendly_commitment_layers
                    .into(),
            },
        },
        fri: FriConfig {
            log_input_size: extracted_ids_and_pub_in_vals.layer_log_sizes[0],
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
                            height: layer_log_rows,
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
        log_trace_domain_size: extracted_ids_and_pub_in_vals.log_trace_domain_size,
        n_queries: extracted_proof_vals.n_queries.into(),
        log_n_cosets: extracted_proof_vals.log_n_cosets.into(),
        n_verifier_friendly_commitment_layers: extracted_proof_vals
            .n_verifier_friendly_commitment_layers
            .into(),
    };

    // Instantiate StarkUnsentCommitment
    let stark_unsent_commitment = StarkUnsentCommitment {
        traces: TracesUnsentCommitment {
            original: extracted_proof_vals.original_commitment_hash,
            interaction: extracted_proof_vals.interaction_commitment_hash,
        },
        composition: extracted_proof_vals.composition_commitment_hash,
        oods_values: extracted_proof_vals.oods_values.clone(),
        fri: FriUnsentCommitment {
            inner_layers: extracted_proof_vals.fri_layers_commitments.clone(),
            last_layer_coefficients: extracted_proof_vals.fri_last_layer_coefficients.clone(),
        },
        proof_of_work: ProofOfWorkUnsentCommitment {
            nonce: extracted_proof_vals.proof_of_work_nonce,
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
            leaves: leaves.clone(),
            table_witness: TableCommitmentWitness {
                vector: VectorCommitmentWitness {
                    n_authentications: authentications.len().into(),
                    authentications: authentications.clone(),
                },
            },
        });
    }

    // Instantiate StarkWitness
    let stark_witness = StarkWitness {
        traces_decommitment: TracesDecommitment {
            original: TableDecommitment {
                n_values: extracted_proof_vals.original_witness_leaves.len().into(),
                values: extracted_proof_vals.original_witness_leaves.clone(),
            },
            interaction: TableDecommitment {
                n_values: extracted_proof_vals.interaction_witness_leaves.len().into(),
                values: extracted_proof_vals.interaction_witness_leaves.clone(),
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
                        .clone(),
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
                        .clone(),
                },
            },
        },
        composition_decommitment: TableDecommitment {
            n_values: extracted_proof_vals.composition_witness_leaves.len().into(),
            values: extracted_proof_vals.composition_witness_leaves.clone(),
        },
        composition_witness: TableCommitmentWitness {
            vector: VectorCommitmentWitness {
                n_authentications: extracted_proof_vals
                    .composition_witness_authentications
                    .len()
                    .into(),
                authentications: extracted_proof_vals
                    .composition_witness_authentications
                    .clone(),
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

/// Converts public input data to a `CairoPublicInput` struct. This struct corresponds to the cairo
/// struct `PublicInput`.
///
/// # Arguments
///
/// * `public_input` - A reference to `OwnedPublicInput`.
/// * `z` - A reference to the interaction element `z`.
/// * `alpha` - A reference to the interaction element `alpha`.
///
/// # Returns
///
/// Returns a `Result` containing the `CairoPublicInput` struct.
///
/// # Errors
///
/// Returns a `HintError` if required data is missing or cannot be computed.
pub fn public_input_to_cairo(
    public_input: &OwnedPublicInput,
    z: &Felt252,
    alpha: &Felt252,
) -> Result<CairoPublicInput, HintError> {
    let continuous_page_headers =
        compute_continuous_page_headers(&public_input.public_memory, z, alpha)?;

    let main_page = get_main_page(&public_input.public_memory)?;

    let dynamic_params = if let Some(dynamic_params_map) = &public_input.dynamic_params {
        let mut dynamic_params_vec: Vec<(&String, &u128)> = dynamic_params_map.iter().collect();
        dynamic_params_vec.sort_by(|a, b| a.0.cmp(b.0));
        dynamic_params_vec.iter().map(|(_k, v)| *(*v)).collect()
    } else {
        Vec::new()
    };

    let memory_segments = sort_segments(&public_input.memory_segments)?;

    let log_n_steps: Felt252 = safe_log2(public_input.n_steps as u128)?.into();
    let layout_bytes = public_input.layout.as_bytes();
    let layout = BigUint::from_bytes_be(layout_bytes);

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

    let first_public_memory_entry = public_input.public_memory.first().ok_or_else(|| {
        HintError::CustomHint(
            "Public memory is empty; cannot get padding address and value.".into(),
        )
    })?;

    let main_page_len = main_page.len();

    let main_page_flat: Vec<Felt252> = main_page
        .into_iter()
        .flat_map(|(address, value)| vec![Felt252::from(address), value])
        .collect();
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

    let cairo_public_input = CairoPublicInput {
        log_n_steps,
        range_check_min: public_input.rc_min.into(),
        range_check_max: public_input.rc_max.into(),
        layout: layout.into(),
        dynamic_params: dynamic_params.into_iter().map(Felt252::from).collect(),
        n_segments: public_input.memory_segments.len().into(),
        segments,
        padding_addr: first_public_memory_entry.address.into(),
        padding_value: first_public_memory_entry.value.unwrap_or_default(),
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

/// Computes pages and their cumulative products from the public memory entries.
///
/// # Arguments
///
/// * `public_memory` - A slice of `PublicMemoryEntry` representing public memory accesses.
/// * `z` - The interaction element `z`.
/// * `alpha` - The interaction element `alpha`.
///
/// # Returns
///
/// Returns a `Result` containing a tuple of pages and their corresponding products.
///
/// # Errors
///
/// Returns a `HintError` if values are missing or computations fail.
pub fn get_pages_and_products(
    public_memory: &[PublicMemoryEntry],
    z: &Felt252,
    alpha: &Felt252,
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

        let page = pages.entry(page_id as u32).or_default();
        page.push(addr.into());
        page.push(val);

        let previous_prod = page_prods.entry(page_id as u32).or_insert(Felt252::ONE);

        // Compute term = z - (addr + alpha * val)
        let term = z - (Felt252::from(addr) + (alpha * val));

        *previous_prod *= term;
    }

    Ok((pages, page_prods))
}

/// Computes headers for continuous pages in the public memory. Header contains the start address,
/// size, hash value of the page_data, and cumulative product of the page.
///
/// # Arguments
///
/// * `public_memory` - A slice of `PublicMemoryEntry` representing public memory accesses.
/// * `z` - The interaction element `z`.
/// * `alpha` - The interaction element `alpha`.
///
/// # Returns
///
/// Returns a `Result` containing a vector of tuples representing page headers.
///
/// # Errors
///
/// Returns a `HintError` if there are inconsistencies in the page data.
pub fn compute_continuous_page_headers(
    public_memory: &[PublicMemoryEntry],
    z: &Felt252,
    alpha: &Felt252,
) -> Result<Vec<(usize, usize, Felt252, Felt252)>, HintError> {
    let mut start_address: HashMap<u32, usize> = HashMap::new();
    let mut size: HashMap<u32, usize> = HashMap::new();
    let mut data: HashMap<u32, Vec<Felt252>> = HashMap::new();

    let (_pages, page_prods) = get_pages_and_products(public_memory, z, alpha)?;

    for access in public_memory.iter() {
        let page_id = access.page;
        let address = access.address;
        let value = access.value;

        start_address.entry(page_id as u32).or_insert(address);

        if page_id == 0 {
            continue;
        }

        let page_data = data.entry(page_id as u32).or_default();

        let expected_address = start_address[&(page_id as u32)] + page_data.len();

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

/// Retrieves the main page entries from the public memory (page 0).
///
/// # Arguments
///
/// * `public_memory` - A slice of `PublicMemoryEntry` representing public memory accesses.
///
/// # Returns
///
/// Returns a `Result` containing a vector of tuples with addresses and values of the main page.
///
/// # Errors
///
/// Returns a `HintError` if values are missing for any address on the main page.
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

/// Sorts memory segments in a predefined order - first the program and execution segments, then the
/// builtins with their predefined order.
///
/// # Arguments
///
/// * `memory_segments` - A `HashMap` of segment names to their corresponding addresses.
///
/// # Returns
///
/// Returns a `Result` containing a sorted `HashMap` of memory segments.
///
/// # Errors
///
/// Returns a `HintError` if expected segments are missing or if there is a mismatch.
pub fn sort_segments(
    memory_segments: &HashMap<String, MemorySegmentAddresses>,
) -> Result<HashMap<String, &MemorySegmentAddresses>, HintError> {
    let mut segment_names = vec!["program".to_string(), "execution".to_string()];

    // TODO: centralize this list (also in cairo_vm)
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
    segment_names.extend(builtin_ordered_list.iter().filter_map(|builtin| {
        let name = format!("{:?}", builtin);
        if memory_segments.contains_key(&name) {
            Some(name)
        } else {
            None
        }
    }));

    let mut sorted_segments = HashMap::new();
    for name in &segment_names {
        if let Some(segment) = memory_segments.get(name) {
            sorted_segments.insert(name.clone(), segment);
        }
    }

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
