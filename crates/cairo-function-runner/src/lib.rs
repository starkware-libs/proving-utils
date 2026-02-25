use anyhow::{anyhow, Result};
use cairo_program_runner_lib::hints::vars::{PROGRAM_INPUT, PROGRAM_OBJECT};
use cairo_program_runner_lib::hints::BootloaderHintProcessor;
use cairo_program_runner_lib::utils::ProgramInput;
use cairo_vm::types::builtin_name::BuiltinName;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::vm::errors::memory_errors::MemoryError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use cairo_vm::vm::runners::cairo_runner::{CairoArg, CairoRunner};

/// A Cairo function runner that mimics the behavior of the Python VM's CairoFunctionRunner.
///
/// This struct provides a high-level interface for running individual Cairo functions with
/// automatic builtin initialization, similar to the Python implementation.
pub struct CairoFunctionRunner<'a> {
    /// The compiled Cairo program to execute.
    pub program: &'a Program,
    /// The Cairo runner instance that manages VM execution.
    pub runner: CairoRunner,
}

impl<'a> CairoFunctionRunner<'a> {
    /// Creates a new CairoFunctionRunner with manually initialized builtin runners
    /// similar to the Python VM's CairoFunctionRunner.
    ///
    /// This constructor initializes the Cairo runner with the `all_cairo` layout and proof mode
    /// enabled, which ensures all builtins are available regardless of what the program declares.
    ///
    /// # Arguments
    ///
    /// * `program` - A reference to the compiled Cairo program to execute.
    ///
    /// # Returns
    ///
    /// Returns `Ok(CairoFunctionRunner)` if initialization succeeds, or `Err(RunnerError)` if
    /// there's an error creating or initializing the runner.
    ///
    /// # Errors
    ///
    /// Returns `RunnerError` if the runner cannot be created or builtins cannot be initialized.
    pub fn new(program: &'a Program) -> Result<Self, RunnerError> {
        // Create the CairoRunner with all_cairo layout and proof mode enabled
        // This ensures all builtins are initialized even if not declared in the program
        let mut runner = CairoRunner::new(
            program,
            LayoutName::all_cairo,
            None,  // dynamic_layout_params
            true,  // proof_mode: enables initialization of all layout builtins
            false, // trace_enabled
            false, // disable_trace_padding
        )?;

        // Initialize builtins from the layout (all builtins in proof mode)
        runner.initialize_builtins(true)?;

        // Initialize all segments at once (program_base, execution_base, and all builtins)
        runner.initialize_segments(None);

        Ok(Self { program, runner })
    }

    /// Runs a Cairo function from the specified entrypoint with the given arguments.
    ///
    /// This method executes a Cairo function by finding its program counter, setting up the
    /// execution environment (including program input if provided), and running the function
    /// using the Cairo VM.
    ///
    /// # Arguments
    ///
    /// * `entrypoint` - The name of the function to execute (e.g., "sqrt", "main").
    /// * `verify_secure` - If `true`, runs additional security verifications after execution.
    /// * `program_segment_size` - Optional size limit for the program segment (used in security
    ///   verification).
    /// * `program_input` - Optional program input to inject into the execution scopes.
    /// * `args` - A slice of `CairoArg` references representing the function arguments.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if execution succeeds, or `Err` if there's an error during execution.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The entrypoint function is not found in the program
    /// - Execution fails (VM errors, hint errors, etc.)
    /// - Security verification fails (if `verify_secure` is true)
    pub fn run(
        &mut self,
        entrypoint: &str,
        verify_secure: bool,
        program_segment_size: Option<usize>,
        program_input: Option<ProgramInput>,
        args: &[&CairoArg],
    ) -> Result<()> {
        // Get the program counter for the entrypoint function
        let entrypoint_pc = self.get_function_pc(entrypoint)?;

        // Create a bootloader hint processor for handling hints during execution
        let mut hint_processor = BootloaderHintProcessor::new(None);

        // Insert program input into execution scopes if provided
        if let Some(program_input) = program_input {
            self.runner
                .exec_scopes
                .insert_value(PROGRAM_INPUT, program_input);
        }

        // Insert the program object into execution scopes (required by some hints)
        self.runner
            .exec_scopes
            .insert_value(PROGRAM_OBJECT, self.program.clone());

        // Execute the function from the entrypoint
        self.runner.run_from_entrypoint(
            entrypoint_pc,
            args,
            verify_secure,
            program_segment_size,
            &mut hint_processor,
        )?;

        Ok(())
    }

    /// Retrieves return values from the VM's memory after function execution.
    ///
    /// This function reads the last `n_return_values` values from the allocation pointer (AP),
    /// which is where Cairo functions store their return values.
    ///
    /// # Arguments
    ///
    /// * `n_return_values` - The number of return values to retrieve.
    ///
    /// # Returns
    ///
    /// Returns `Ok(Vec<MaybeRelocatable>)` containing the return values, or `Err(MemoryError)`
    /// if there's an error reading from memory.
    ///
    /// # Errors
    ///
    /// Returns `MemoryError` if the memory cannot be read or if the address calculation fails.
    pub fn get_return_values(
        &self,
        n_return_values: usize,
    ) -> Result<Vec<MaybeRelocatable>, MemoryError> {
        self.runner.vm.get_return_values(n_return_values)
    }

    /// Gets the base pointer (starting address) for a specific builtin.
    ///
    /// This is useful for passing builtin pointers as arguments to Cairo functions that require
    /// them (e.g., `range_check_ptr` for range check operations).
    ///
    /// # Arguments
    ///
    /// * `builtin_name` - The name of the builtin to get the base pointer for.
    ///
    /// # Returns
    ///
    /// Returns `Some(MaybeRelocatable)` containing the base pointer if the builtin is found,
    /// or `None` if the builtin is not initialized.
    pub fn get_builtin_base(&self, builtin_name: BuiltinName) -> Option<MaybeRelocatable> {
        self.runner
            .vm
            .builtin_runners
            .iter()
            .find(|builint_runner| builint_runner.name() == builtin_name)
            .map(|builtin_runner| MaybeRelocatable::from((builtin_runner.base() as isize, 0)))
    }

    /// Gets the program counter (PC) for a function entrypoint.
    ///
    /// This function looks up the function in the program's identifiers and returns its PC,
    /// which is needed to execute the function.
    ///
    /// # Arguments
    ///
    /// * `entrypoint` - The name of the function (e.g., "sqrt", "main").
    ///
    /// # Returns
    ///
    /// Returns `Ok(usize)` containing the program counter if the function is found, or an error
    /// if the function doesn't exist or has no PC.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The function is not found in the program identifiers
    /// - The function identifier has no PC value
    fn get_function_pc(&self, entrypoint: &str) -> Result<usize> {
        // Format the full identifier name (Cairo 0 uses __main__.<function_name>)
        let full_name = format!("__main__.{entrypoint}");
        // Look up the identifier in the program
        let identifier = self
            .program
            .get_identifier(&full_name)
            .ok_or_else(|| anyhow!("Function '{entrypoint}' not found"))?;

        // Extract the program counter from the identifier
        let pc = identifier.pc.ok_or(RunnerError::NoPC)?;

        Ok(pc)
    }
}
