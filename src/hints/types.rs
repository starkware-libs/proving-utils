use std::collections::HashMap;
use std::path::PathBuf;

use cairo_vm::serde::deserialize_program::Identifier;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::program::Program;
use cairo_vm::vm::runners::cairo_pie::{CairoPie, StrippedProgram};
use cairo_vm::Felt252;
use serde::de::Error as SerdeError;
use serde::{Deserialize, Deserializer};

use crate::tasks::{create_pie_task_spec, create_program_task_spec};

pub type BootloaderVersion = u64;

pub(crate) type ProgramIdentifiers = HashMap<String, Identifier>;

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct BootloaderConfig {
    pub simple_bootloader_program_hash: Felt252,
    pub supported_cairo_verifier_program_hashes: Vec<Felt252>,
}

#[derive(Deserialize, Debug, Default, Clone, PartialEq)]
pub struct CompositePackedOutput {
    pub outputs: Vec<Felt252>,
    pub subtasks: Vec<PackedOutput>,
}

impl CompositePackedOutput {
    pub fn elements_for_hash(&self) -> &Vec<Felt252> {
        &self.outputs
    }
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub enum PackedOutput {
    Plain(Vec<Felt252>),
    Composite(CompositePackedOutput),
}

#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::large_enum_variant)]
pub enum Task {
    Program(Program),
    Pie(CairoPie),
}

impl Task {
    pub fn get_program(&self) -> Result<StrippedProgram, ProgramError> {
        // TODO: consider whether declaring a struct similar to StrippedProgram
        //       but that uses a reference to data to avoid copying is worth the effort.
        match self {
            Task::Program(program) => program.get_stripped_program(),
            Task::Pie(cairo_pie) => Ok(cairo_pie.metadata.program.clone()),
        }
    }
}

// For now will support only CairoPiePath tasks and RunProgramTask task without program_input.
// In the future, we may want to support for RunProgramTask with program_input.
#[derive(Deserialize)]
struct TaskSpecHelper {
    #[serde(rename = "type")]
    task_type: String,
    use_poseidon: bool,
    path: PathBuf,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TaskSpec {
    pub task: Task,
    pub use_poseidon: bool,
}

impl<'de> Deserialize<'de> for TaskSpec {
    /// Custom deserialization for `TaskSpec`, which constructs a task based on its type
    /// (either "CairoPiePath" or "RunProgramTask") and a file path.
    ///
    /// # Arguments
    /// - `deserializer`: The deserializer used to parse the JSON into a `TaskSpec`.
    ///
    /// # Returns
    /// - `Ok(TaskSpec)`: If successful, returns a `TaskSpec` with the appropriate task and Poseidon option.
    /// - `Err(D::Error)`: If deserialization fails or the task type is unsupported.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let helper = TaskSpecHelper::deserialize(deserializer)?;

        let task_spec = match helper.task_type.as_str() {
            "CairoPiePath" => create_pie_task_spec(&helper.path, helper.use_poseidon)
                .map_err(|e| D::Error::custom(format!("Error creating TaskSpec: {:?}", e))),
            "RunProgramTask" => create_program_task_spec(&helper.path, helper.use_poseidon)
                .map_err(|e| D::Error::custom(format!("Error creating TaskSpec: {:?}", e))),
            _ => {
                return Err(D::Error::custom(format!(
                    "Unsupported type: {}",
                    helper.task_type
                )))
            }
        };

        task_spec
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

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct SimpleBootloaderInput {
    pub fact_topologies_path: Option<PathBuf>,
    pub single_page: bool,
    pub tasks: Vec<TaskSpec>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BootloaderInput {
    pub simple_bootloader_input: SimpleBootloaderInput,
    pub bootloader_config: BootloaderConfig,
    pub packed_outputs: Vec<PackedOutput>,
}
