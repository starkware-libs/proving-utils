//! A Cairo function runner for testing purposes.
//!
//! This module provides [`CairoFunctionRunner`], a high-level interface for running individual
//! Cairo functions with automatic builtin initialization. It allows direct invocation of specific
//! entrypoints with custom arguments.

use cairo_program_runner_lib::hints::vars::{PROGRAM_INPUT, PROGRAM_OBJECT};
use cairo_program_runner_lib::hints::BootloaderHintProcessor;
use cairo_program_runner_lib::utils::ProgramInput;
use cairo_vm::types::builtin_name::BuiltinName;
use cairo_vm::types::errors::program_errors::ProgramError;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::errors::memory_errors::MemoryError;
use cairo_vm::vm::errors::runner_errors::RunnerError;
use cairo_vm::vm::runners::cairo_runner::{CairoArg, CairoRunner};

/// A runner for executing individual Cairo functions.
/// Used for testing purposes only.
pub struct CairoFunctionRunner<'a> {
    /// The compiled Cairo program to execute.
    pub program: &'a Program,
    /// The Cairo runner instance that manages VM execution.
    pub runner: CairoRunner,
}

impl<'a> CairoFunctionRunner<'a> {
    /// Creates a new `CairoFunctionRunner`.
    ///
    /// Initializes the Cairo runner with the `all_cairo` layout and proof mode enabled, ensuring
    /// all builtins are available regardless of what the program declares.
    ///
    /// # Arguments
    /// - `program`: The compiled Cairo program to execute.
    ///
    /// # Returns
    /// - `Ok(CairoFunctionRunner)`: On successful initialization.
    /// - `Err(CairoRunError)`: If the runner cannot be created or builtins cannot be initialized.
    #[allow(clippy::result_large_err)]
    pub fn new(program: &'a Program) -> std::result::Result<Self, CairoRunError> {
        let mut runner = CairoRunner::new(
            program,
            LayoutName::all_cairo,
            None,  // dynamic_layout_params
            true,  // proof_mode
            false, // trace_enabled
            false, // disable_trace_padding
        )?;

        runner.initialize_builtins(true)?;
        runner.initialize_segments(None);

        Ok(Self { program, runner })
    }

    /// Runs a Cairo function from the specified entrypoint.
    ///
    /// # Arguments
    /// - `entrypoint`: The function name to execute (e.g., "sqrt", "main").
    /// - `verify_secure`: If `true`, runs additional security verifications after execution.
    /// - `program_segment_size`: Optional size limit for the program segment.
    /// - `program_input`: Optional program input to inject into the execution scopes.
    /// - `args`: The function arguments.
    ///
    /// # Returns
    /// - `Ok(())`: On successful execution.
    /// - `Err(CairoRunError)`: If the entrypoint is not found, execution fails, or security
    ///   verification fails.
    #[allow(clippy::result_large_err)]
    pub fn run(
        &mut self,
        entrypoint: &str,
        verify_secure: bool,
        program_segment_size: Option<usize>,
        program_input: Option<ProgramInput>,
        args: &[CairoArg],
    ) -> std::result::Result<(), CairoRunError> {
        let entrypoint_pc = self.get_function_pc(entrypoint)?;

        let mut hint_processor = BootloaderHintProcessor::new(None);

        if let Some(program_input) = program_input {
            self.runner
                .exec_scopes
                .insert_value(PROGRAM_INPUT, program_input);
        }

        self.runner
            .exec_scopes
            .insert_value(PROGRAM_OBJECT, self.program.clone());

        let cairo_args: Vec<&CairoArg> = args.iter().collect();

        self.runner.run_from_entrypoint(
            entrypoint_pc,
            &cairo_args,
            verify_secure,
            program_segment_size,
            &mut hint_processor,
        )?;

        Ok(())
    }

    /// Runs a Cairo function with default settings (no security verification, no program input).
    #[allow(clippy::result_large_err)]
    pub fn run_default(
        &mut self,
        entrypoint: &str,
        args: &[CairoArg],
    ) -> std::result::Result<(), CairoRunError> {
        self.run(entrypoint, false, None, None, args)
    }

    /// Retrieves return values from the VM's memory after function execution.
    ///
    /// Reads the last `n_return_values` values from the allocation pointer (AP).
    pub fn get_return_values(
        &self,
        n_return_values: usize,
    ) -> Result<Vec<MaybeRelocatable>, MemoryError> {
        self.runner.vm.get_return_values(n_return_values)
    }

    /// Gets the base pointer for a specific builtin.
    ///
    /// Useful for passing builtin pointers as arguments to Cairo functions (e.g., `range_check_ptr`
    /// for range check operations).
    pub fn get_builtin_base(&self, builtin_name: BuiltinName) -> Option<MaybeRelocatable> {
        self.runner
            .vm
            .builtin_runners
            .iter()
            .find(|builint_runner| builint_runner.name() == builtin_name)
            .map(|builtin_runner| MaybeRelocatable::from((builtin_runner.base() as isize, 0)))
    }

    /// Gets the program counter (PC) for a function entrypoint.
    #[allow(clippy::result_large_err)]
    fn get_function_pc(&self, entrypoint: &str) -> std::result::Result<usize, CairoRunError> {
        let full_name = format!("__main__.{entrypoint}");
        let identifier = self
            .program
            .get_identifier(&full_name)
            .ok_or_else(|| ProgramError::EntrypointNotFound(entrypoint.to_string()))?;

        let pc = identifier.pc.ok_or(RunnerError::NoPC)?;

        Ok(pc)
    }
}
