use std::collections::HashMap;
use std::path::PathBuf;
use std::str::FromStr;

use cairo_vm::air_public_input::{MemorySegmentAddresses, PublicMemoryEntry};
use cairo_vm::cairo_run::CairoRunConfig;
use cairo_vm::serde::deserialize_program::Identifier;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout::CairoLayoutParams;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::{CairoPie, StrippedProgram};
use cairo_vm::Felt252;
use num_traits::ToPrimitive;
use serde::de::Error as SerdeError;
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::{Number, Value};

use crate::tasks::{create_pie_task, create_program_task};

use super::fact_topologies::FactTopology;

pub type BootloaderVersion = u64;

pub(crate) type ProgramIdentifiers = HashMap<String, Identifier>;

#[derive(Deserialize, Debug, Clone)]
pub struct BootloaderConfig {
    pub simple_bootloader_program_hash: Felt252,
    pub applicative_bootloader_program_hash: Felt252,
    pub supported_cairo_verifier_program_hashes: Vec<Felt252>,
}

pub const BOOTLOADER_CONFIG_SIZE: usize = 3;
#[derive(Deserialize, Debug, Default, Clone)]
/// Represents a composite packed output, which consists of a set of outputs,
/// subtasks (which could be plain or composite themselves), and associated fact topologies of the
/// plain subtasks.
pub struct CompositePackedOutput {
    pub outputs: Vec<Felt252>,
    pub subtasks: Vec<PackedOutput>,
    pub fact_topologies: Vec<FactTopology>,
}

impl CompositePackedOutput {
    pub fn elements_for_hash(&self) -> &Vec<Felt252> {
        &self.outputs
    }

    /// Generates a vector of `FactTopology` objects for plain subtasks, taking into account
    /// the given `applicative_bootloader_program_hash`.
    ///
    /// # Arguments
    ///
    /// * `applicative_bootloader_program_hash` - The hash used to verify if the subtask matches the
    ///   expected bootloader program.
    ///
    /// # Returns
    ///
    /// Returns a `Result` containing a vector of `FactTopology` objects if successful,
    /// or an error message in case of any inconsistency or failure.
    ///
    /// # Errors
    ///
    /// * Returns an error if `outputs` is empty, meaning there are no tasks to process.
    /// * Returns an error if the number of subtasks does not match the expected count.
    /// * Returns an error if a subtask size or program hash is missing from `outputs`.
    /// * Returns an error if the subtask type is unsupported.
    /// * Returns an error if the sum of subtask sizes does not match the length of `outputs`.
    pub fn get_plain_fact_topologies(
        &self,
        applicative_bootloader_program_hash: Felt252,
    ) -> Result<Vec<FactTopology>, String> {
        let mut subtasks_fact_topologies = Vec::new();

        // Retrieve the number of tasks, ensuring that `outputs` is not empty
        let n_tasks = self.outputs.first().ok_or("Outputs list is empty")?;

        // Validate that the number of subtasks matches the number of tasks
        if self.subtasks.len()
            != n_tasks
                .to_usize()
                .ok_or("Failed to convert number of tasks to usize")?
        {
            return Err(format!(
                "Number of subtasks does not match the number of tasks in outputs. \
                Expected: {} in outputs, got: {} in subtasks.",
                n_tasks,
                self.subtasks.len()
            ));
        }

        // Define constants and initial offset for processing subtasks
        let applicative_bootloader_header_size = 1 + BOOTLOADER_CONFIG_SIZE;
        let mut curr_subtask_offset = 1;

        for (index, subtask) in self.subtasks.iter().enumerate() {
            // Retrieve subtask size and program hash from outputs
            let subtask_size = self
                .outputs
                .get(curr_subtask_offset)
                .ok_or("Subtask size not found in outputs")?;
            let program_hash = self
                .outputs
                .get(curr_subtask_offset + 1)
                .ok_or("Program hash not found in outputs")?;

            // Handle subtask if it is of type `PackedOutput::Plain`
            if let PackedOutput::Plain = subtask {
                // If the program hash matches the app. bootloader hash, adjust the page sizes
                if *program_hash == applicative_bootloader_program_hash {
                    let mut page_sizes = self.fact_topologies[index].page_sizes.clone();
                    if let Some(first_page_size) = page_sizes.get_mut(0) {
                        *first_page_size -= applicative_bootloader_header_size;
                    }
                    subtasks_fact_topologies.push(FactTopology {
                        page_sizes,
                        tree_structure: self.fact_topologies[index].tree_structure.clone(),
                    });
                } else {
                    // Otherwise, add the fact topology directly
                    subtasks_fact_topologies.push(self.fact_topologies[index].clone());
                }
            }
            // Handle subtask recursively if it is of type `PackedOutput::Composite`
            else if let PackedOutput::Composite(composite) = subtask {
                subtasks_fact_topologies.extend(
                    composite.get_plain_fact_topologies(applicative_bootloader_program_hash)?,
                );
            } else {
                return Err("Unsupported subtask type".to_string());
            }

            // Increment the subtask offset based on the subtask size
            curr_subtask_offset += subtask_size
                .to_bigint()
                .to_usize()
                .ok_or("Failed to convert subtask size to usize")?;
        }

        // Validate that the total offset matches the length of outputs
        if curr_subtask_offset != self.outputs.len() {
            return Err(format!(
                "The sum of the subtask sizes does not match the size of the outputs. \
                Expected: {}, got: {}.",
                self.outputs.len(),
                curr_subtask_offset
            ));
        }

        Ok(subtasks_fact_topologies)
    }
}

#[derive(Debug, Clone)]
pub enum PackedOutput {
    Plain,
    Composite(CompositePackedOutput),
}

// Helper struct to handle deserialization
#[derive(Deserialize)]
struct PackedOutputHelper {
    #[serde(rename = "type")]
    output_type: String,
    outputs: Option<Vec<Number>>,
    subtasks: Option<Vec<PackedOutput>>,
    fact_topologies: Option<Vec<FactTopology>>,
}

impl<'de> Deserialize<'de> for PackedOutput {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let helper = PackedOutputHelper::deserialize(deserializer)?;

        match helper.output_type.as_str() {
            "CompositePackedOutput" => {
                // Ensure we have all the fields needed for CompositePackedOutput
                let outputs = helper
                    .outputs
                    .ok_or_else(|| D::Error::missing_field("outputs"))?
                    .into_iter()
                    .map(|x| Felt252::from_str(x.to_string().as_str()).unwrap())
                    .collect();
                let subtasks = helper
                    .subtasks
                    .ok_or_else(|| D::Error::missing_field("subtasks"))?;
                let fact_topologies = helper
                    .fact_topologies
                    .ok_or_else(|| D::Error::missing_field("fact_topologies"))?;
                Ok(PackedOutput::Composite(CompositePackedOutput {
                    outputs,
                    subtasks,
                    fact_topologies,
                }))
            }
            "PlainPackedOutput" => Ok(PackedOutput::Plain),
            _ => Err(D::Error::custom(format!(
                "Unsupported type: {}",
                helper.output_type
            ))),
        }
    }
}

#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum Task {
    Program(ProgramWithInput),
    Pie(CairoPie),
}

#[derive(Debug, Clone)]
pub struct ProgramWithInput {
    pub program: Program,
    pub program_input: Option<String>,
}

impl Task {
    pub fn get_program(&self) -> Result<StrippedProgram, ProgramError> {
        // TODO: consider whether declaring a struct similar to StrippedProgram
        //       but that uses a reference to data to avoid copying is worth the effort.
        match self {
            Task::Program(program_with_input) => program_with_input.program.get_stripped_program(),
            Task::Pie(cairo_pie) => Ok(cairo_pie.metadata.program.clone()),
        }
    }
}
#[derive(Deserialize)]
struct TaskSpecHelper {
    #[serde(rename = "type")]
    task_type: String,
    program_hash_function: String,
    path: Option<PathBuf>,
    program: Option<Value>,
    program_input: Option<Value>,
}

#[derive(Debug, Clone)]
pub struct TaskSpec {
    pub task: Task,
    pub program_hash_function: HashFunc,
}

/// A hash function. These can be used e.g. for hashing a program within the bootloader.
#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum HashFunc {
    Pedersen = 0,
    Poseidon = 1,
    Blake = 2,
}

impl TryFrom<String> for HashFunc {
    type Error = String;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        match value.to_lowercase().as_str() {
            "pedersen" => Ok(HashFunc::Pedersen),
            "poseidon" => Ok(HashFunc::Poseidon),
            "blake" => Ok(HashFunc::Blake),
            _ => Err(format!(
                "Invalid program hash function: {value}.
                Expected `pedersen`, `poseidon`, or `blake`."
            )),
        }
    }
}

impl<'de> Deserialize<'de> for TaskSpec {
    /// Custom deserialization for `TaskSpec`, which constructs a task based on its type
    /// (either "CairoPiePath" or "RunProgramTask") and a file path.
    ///
    /// # Arguments
    /// - `deserializer`: The deserializer used to parse the JSON into a `TaskSpec`.
    ///
    /// # Returns
    /// - `Ok(TaskSpec)`: If successful, returns a `TaskSpec` with the appropriate task and Poseidon
    ///   option.
    /// - `Err(D::Error)`: If deserialization fails or the task type is unsupported.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let helper = TaskSpecHelper::deserialize(deserializer)?;

        // Parse program, if provided
        let task = match helper.task_type.as_str() {
            "CairoPiePath" => {
                if let Some(path) = &helper.path {
                    create_pie_task(path).map_err(|e| {
                        D::Error::custom(format!("Error creating PIE task: {:?}", e))
                    })?
                } else {
                    return Err(D::Error::custom("CairoPiePath requires a path"));
                }
            }
            "RunProgramTask" => {
                // Parse program_input, if provided
                let program_input = if let Some(program_input_data) = &helper.program_input {
                    let program_input_json =
                        serde_json::to_string(program_input_data).map_err(|e| {
                            D::Error::custom(format!("Failed to serialize program input: {:?}", e))
                        })?;
                    Some(program_input_json)
                } else {
                    None
                };
                // Deserialize program if present
                if let Some(program_data) = &helper.program {
                    let program_bytes = serde_json::to_vec(program_data).map_err(|e| {
                        D::Error::custom(format!("Failed to serialize program: {:?}", e))
                    })?;
                    let program =
                        Program::from_bytes(&program_bytes, Some("main")).map_err(|e| {
                            D::Error::custom(format!("Failed to deserialize program: {:?}", e))
                        })?;
                    Task::Program(ProgramWithInput {
                        program,
                        program_input,
                    })
                } else if let Some(path) = &helper.path {
                    create_program_task(path, program_input).map_err(|e| {
                        D::Error::custom(format!("Error creating Program task: {:?}", e))
                    })?
                } else {
                    return Err(D::Error::custom(
                        "RunProgramTask requires either a program or path",
                    ));
                }
            }
            _ => {
                return Err(D::Error::custom(format!(
                    "Unsupported type: {}",
                    helper.task_type
                )))
            }
        };

        Ok(TaskSpec {
            task,
            program_hash_function: HashFunc::try_from(helper.program_hash_function)
                .map_err(|e| D::Error::custom(format!("Invalid program hash function: {e:?}")))?,
        })
    }
}

impl TaskSpec {
    /// Retrieves a reference to the `Task` within the `TaskSpec`.
    ///
    /// # Returns
    /// A reference to the `task` field, which is either a `Program` or `CairoPie`.
    pub fn load_task(&self) -> &Task {
        &self.task
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct SimpleBootloaderInput {
    pub fact_topologies_path: Option<PathBuf>,
    pub single_page: bool,
    pub tasks: Vec<TaskSpec>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BootloaderInput {
    #[serde(flatten)]
    pub simple_bootloader_input: SimpleBootloaderInput,
    pub bootloader_config: BootloaderConfig,
    pub packed_outputs: Vec<PackedOutput>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ApplicativeBootloaderInput {
    #[serde(flatten)]
    pub bootloader_input: BootloaderInput,
    pub aggregator_task: TaskSpec,
}

#[derive(Deserialize, Debug)]
pub struct CairoVerifierInput {
    pub proof: HashMap<String, serde_json::Value>,
}

pub struct ExtractedProofValues {
    pub original_commitment_hash: Felt252,
    pub interaction_commitment_hash: Felt252,
    pub composition_commitment_hash: Felt252,
    pub oods_values: Vec<Felt252>,
    pub fri_layers_commitments: Vec<Felt252>,
    pub fri_last_layer_coefficients: Vec<Felt252>,
    pub proof_of_work_nonce: Felt252,
    pub original_witness_leaves: Vec<Felt252>,
    pub original_witness_authentications: Vec<Felt252>,
    pub interaction_witness_leaves: Vec<Felt252>,
    pub interaction_witness_authentications: Vec<Felt252>,
    pub composition_witness_leaves: Vec<Felt252>,
    pub composition_witness_authentications: Vec<Felt252>,
    pub fri_step_list: Vec<u64>,
    pub n_fri_layers: usize,
    pub log_n_cosets: u64,
    pub log_last_layer_degree_bound: u32,
    pub n_verifier_friendly_commitment_layers: u64,
    pub z: Felt252,
    pub alpha: Felt252,
    pub proof_of_work_bits: u64,
    pub n_queries: u64,
    pub fri_witnesses_leaves: Vec<Vec<Felt252>>,
    pub fri_witnesses_authentications: Vec<Vec<Felt252>>,
}

#[derive(Debug)]
pub struct ExtractedIDsAndInputValues {
    pub log_trace_domain_size: Felt252,
    pub log_eval_domain_size: Felt252,
    pub layer_log_sizes: Vec<Felt252>,
    pub num_columns_first: Felt252,
    pub num_columns_second: Felt252,
    pub constraint_degree: Felt252,
}

// Struct needed for deserialization of the public input. Owned version of PublicInput.
#[derive(Serialize, Deserialize, Debug)]
pub struct OwnedPublicInput {
    pub layout: String,
    pub rc_min: isize,
    pub rc_max: isize,
    pub n_steps: usize,
    pub memory_segments: HashMap<String, MemorySegmentAddresses>,
    pub public_memory: Vec<PublicMemoryEntry>,
    pub dynamic_params: Option<HashMap<String, u128>>,
}

pub enum RunMode {
    Proof {
        layout: LayoutName,
        dynamic_layout_params: Option<CairoLayoutParams>,
        disable_trace_padding: bool,
    },
    Validation {
        layout: LayoutName,
        allow_missing_builtins: bool,
    },
}

impl RunMode {
    pub fn create_config(self) -> CairoRunConfig<'static> {
        match self {
            RunMode::Proof {
                layout,
                dynamic_layout_params,
                disable_trace_padding,
            } => CairoRunConfig {
                entrypoint: "main",
                trace_enabled: true,
                relocate_mem: true,
                layout,
                proof_mode: true,
                secure_run: None,
                disable_trace_padding,
                allow_missing_builtins: None,
                dynamic_layout_params,
            },
            RunMode::Validation {
                layout,
                allow_missing_builtins,
            } => CairoRunConfig {
                entrypoint: "main",
                trace_enabled: false,
                relocate_mem: false,
                layout,
                proof_mode: false,
                secure_run: None,
                disable_trace_padding: false,
                allow_missing_builtins: Some(allow_missing_builtins),
                dynamic_layout_params: None,
            },
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct SimpleOutputInput {
    pub output: Vec<Number>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ConcatAggregatorInput {
    pub bootloader_output: Vec<Number>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MockCairoVerifierInput {
    pub n_steps: u128,
    pub program_hash: Felt252,
    pub program_output: Vec<Felt252>,
}
