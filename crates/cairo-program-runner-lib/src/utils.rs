use std::{
    any::Any,
    io,
    path::{Path, PathBuf},
};

use cairo_vm::{
    cairo_run::CairoRunConfig,
    types::{
        builtin_name::BuiltinName, errors::program_errors::ProgramError, layout::CairoLayoutParams,
        layout_name::LayoutName, program::Program, relocatable::MaybeRelocatable,
    },
    vm::runners::cairo_runner::{CairoArg, CairoRunner},
    Felt252,
};

use crate::types::RunMode;

#[derive(Debug)]
pub enum ProgramInput {
    Path(PathBuf),
    Json(String),
    Value(Box<dyn Any>),
}

impl ProgramInput {
    pub fn from_value<T: Any>(value: T) -> Self {
        Self::Value(Box::new(value))
    }
}

/// Loads a Cairo program from a file.
///
/// This function reads a Cairo program from the specified file path, expecting
/// an entry point named `"main"`. It returns a `Program` instance on success or a
/// `ProgramError` if the file cannot be read or parsed as a valid Cairo program.
///
/// # Arguments
///
/// * `program` - A reference to the file path containing the Cairo program.
///
/// # Errors
///
/// Returns a `ProgramError` if the program file cannot be read or is invalid.
pub fn get_program(program: &Path) -> Result<Program, ProgramError> {
    Program::from_file(program, Some("main"))
}

/// Wraps the input for a Cairo program.
///
/// This function checks if an input file is provided. If so, it returns the path wrapped
/// as `ProgramInput::Path`. If no input file is provided, it returns `Ok(None)`.
///
/// # Arguments
///
/// * `program_input` - An optional file path to the input file.
///
/// # Errors
///
/// Returns an `io::Error` only for API consistency.
pub fn get_program_input_from_path(
    program_input: &Option<PathBuf>,
) -> io::Result<Option<ProgramInput>> {
    Ok(program_input
        .as_ref()
        .map(|input_path| ProgramInput::Path(input_path.to_path_buf())))
}

/// Creates a Cairo run configuration based on the provided parameters.
///
/// Depending on the `proof_mode` flag, this function creates a run configuration
/// for either proof or validation. If a dynamic parameters file is provided,
/// the layout must be `LayoutName::dynamic`, and the dynamic layout parameters are read
/// from the file.
///
/// # Arguments
///
/// * `dynamic_params_file` - An optional file path containing dynamic layout parameters.
/// * `layout` - The layout name to use for the run configuration.
/// * `proof_mode` - A boolean flag indicating whether to generate a proof (true) or run in
///   validation mode (false).
/// * `disable_trace_padding` - A boolean flag to disable trace padding (used in proof mode).
/// * `allow_missing_builtins` - A boolean flag to allow missing built-ins (used in validation
///   mode).
/// * `relocate_mem` - A boolean flag indicating whether to relocate memory in the VM (used in proof
///   mode).
///
/// # Returns
///
/// Returns a `CairoRunConfig` instance configured according to the provided parameters.
///
/// # Errors
///
/// Returns an `io::Error` if there is an issue reading the dynamic layout parameters file.
///
/// # Panics
///
/// Panics if `dynamic_params_file` is provided but `layout` is not `LayoutName::dynamic`.
pub fn get_cairo_run_config(
    dynamic_params_file: &Option<PathBuf>,
    layout: LayoutName,
    proof_mode: bool,
    disable_trace_padding: bool,
    allow_missing_builtins: bool,
    relocate_mem: bool,
) -> std::io::Result<CairoRunConfig<'static>> {
    let dynamic_layout_params = match dynamic_params_file {
        Some(file) => {
            assert!(
                layout == LayoutName::dynamic,
                "dynamic_params_file should not be provided for layout {layout}."
            );
            Some(CairoLayoutParams::from_file(file)?)
        }
        None => None,
    };

    Ok(if proof_mode {
        RunMode::Proof {
            layout,
            dynamic_layout_params,
            disable_trace_padding,
            relocate_mem,
        }
        .create_config()
    } else {
        RunMode::Validation {
            layout,
            allow_missing_builtins,
        }
        .create_config()
    })
}

/// Write the program output to the specified output path as Felt252 values.
pub fn write_output_to_file(runner: &mut CairoRunner, output_path: PathBuf) -> anyhow::Result<()> {
    let mut output_buffer = String::new();
    runner.vm.write_output(&mut output_buffer)?;
    let output_lines = output_buffer
        .lines()
        .map(|line| {
            Felt252::from_dec_str(line)
                .map_err(|_| anyhow::anyhow!("Failed to parse output line as Felt decimal: {line}"))
        })
        .collect::<Result<Vec<Felt252>, anyhow::Error>>()?;
    std::fs::write(&output_path, sonic_rs::to_string_pretty(&output_lines)?)?;
    Ok(())
}

// Builds the implicit arguments (builtin pointers, syscall_ptr) for a specific Cairo function
/// by reading the function's ImplicitArgs from the program metadata.
///
/// # Arguments
///
/// * `program` - The compiled Cairo program
/// * `function_name` - The name of the function to get implicit args for
/// * `runner` - The CairoRunner instance (to access builtin runners and add segments)
///
/// # Returns
///
/// A vector of `CairoArg` containing the builtin pointers in the correct order,
/// or empty vector if the function's ImplicitArgs cannot be found or empty.
///
/// # Example
///
/// For a function `func foo{range_check_ptr, pedersen_ptr}(x: felt)`,
/// this returns a vector with [range_check_ptr_value, pedersen_ptr_value].
pub fn build_function_implicit_args(
    program: &Program,
    func_name: &str,
    runner: &mut CairoRunner,
) -> Result<Vec<CairoArg>, anyhow::Error> {
    let implicit_args_key = format!("__main__.{func_name}.ImplicitArgs");
    // Get the ImplicitArgs identifier from program metadata
    let Some(implicit_args_identifier) = program.get_identifier(&implicit_args_key) else {
        return Ok(vec![]);
    };
    // Check if members exist
    let Some(members) = &implicit_args_identifier.members else {
        return Ok(vec![]);
    };
    // Sort members by offset to get correct stack order
    let mut sorted_members: Vec<_> = members.iter().collect();
    sorted_members.sort_by_key(|(_, member)| member.offset);

    let mut args = Vec::new();

    for (member_name, _member_info) in sorted_members {
        // Special case: syscall_ptr (for StarkNet contracts)
        if member_name == "syscall_ptr" {
            let syscall_segment = runner.vm.add_memory_segment();
            args.push(CairoArg::Single(MaybeRelocatable::from(syscall_segment)));
        } else {
            let builtin_name_str = member_name
                .strip_suffix("_ptr")
                .or_else(|| member_name.strip_suffix("Ptr"))
                .unwrap_or(member_name);

            // Convert string to BuiltinName enum
            let Some(builtin_name) = BuiltinName::from_str(builtin_name_str) else {
                return Err(anyhow::anyhow!("Unknown builtin name '{builtin_name_str}'"));
            };

            // Find the builtin runner by name from runner.vm.builtin_runners
            let builtin_runner = runner
                .vm
                .builtin_runners
                .iter()
                .find(|b| b.name() == builtin_name)
                .ok_or_else(|| anyhow::anyhow!("Builtin '{builtin_name_str}' not found in VM"))?;

            for val in builtin_runner.initial_stack() {
                args.push(CairoArg::Single(val));
            }
        }
    }
    Ok(args)
}
