/// Deserialized bootloader input.
pub const PROGRAM_INPUT: &str = "program_input";

/// Deserialized bootloader input.
pub const PROGRAM_OBJECT: &str = "program_object";

/// Deserialized bootloader input.
pub const BOOTLOADER_INPUT: &str = "bootloader_input";

/// Saved state of the output builtin.
pub const OUTPUT_BUILTIN_STATE: &str = "output_builtin_state";

/// Saved state of the output builtin for an applicative bootloader run.
pub const APPLICATIVE_OUTPUT_BUILTIN_STATE: &str = "applicative_output_builtin_state";

/// Output builtin segment start.
pub const OUTPUT_START: &str = "output_start";

/// Deserialized simple bootloader input.
pub const SIMPLE_BOOTLOADER_INPUT: &str = "simple_bootloader_input";

/// Deserialized applicative bootloader input.
pub const APPLICATIVE_BOOTLOADER_INPUT: &str = "applicative_bootloader_input";

/// Packed outputs.
pub const PACKED_OUTPUTS: &str = "packed_outputs";

/// Packed output for the current task.
pub const PACKED_OUTPUT: &str = "packed_output";

/// Fact topologies.
pub const FACT_TOPOLOGIES: &str = "fact_topologies";

/// Aggregator fact topologies for an applicative bootloader run.
pub const AGGREGATOR_FACT_TOPOLOGIES: &str = "aggregator_fact_topologies";

/// Simple bootloader tasks.
pub const TASKS: &str = "tasks";

/// Current simple bootloader task.
pub const TASK: &str = "task";

/// Current simple bootloader use_poseidon.
pub const USE_POSEIDON: &str = "use_poseidon";

/// Program data segment. Used in `execute_task()`.
pub const PROGRAM_DATA_BASE: &str = "program_data_base";

/// Address of current program.
pub const PROGRAM_ADDRESS: &str = "program_address";

/// Output builtin additional data.
pub const OUTPUT_RUNNER_DATA: &str = "output_runner_data";

/// Number of builtins used by the program.
pub const N_BUILTINS: &str = "n_builtins";

/// Number of selected builtins for the current program.
pub const N_SELECTED_BUILTINS: &str = "n_selected_builtins";

/// "pre_execution_builtin_ptrs"
pub const PRE_EXECUTION_BUILTIN_PTRS: &str = "pre_execution_builtin_ptrs";

// component height const from the py file
pub const COMPONENT_HEIGHT: u64 = 16;
