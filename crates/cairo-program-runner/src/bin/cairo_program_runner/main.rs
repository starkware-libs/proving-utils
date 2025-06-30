use std::env;
use std::error::Error;
use std::io::{self, Write};
use std::path::PathBuf;

use bincode::enc::write::Writer;
use cairo_program_runner_lib::utils::{get_cairo_run_config, get_program, get_program_input};
use cairo_vm::types::layout_name::LayoutName;

use cairo_program_runner_lib::cairo_run_program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::{cairo_run, Felt252};
use clap::Parser;
use tempfile::NamedTempFile;

fn parse_bool(s: &str) -> Result<bool, String> {
    match s.to_lowercase().as_str() {
        "true" | "1" => Ok(true),
        "false" | "0" => Ok(false),
        _ => Err(format!("invalid boolean value: {s}")),
    }
}

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "program", help = "Path to the compiled program")]
    program: PathBuf,
    #[clap(long = "program_input", help = "Path to the program input file.")]
    program_input: Option<PathBuf>,
    #[clap(
        long = "cairo_pie_output",
        help = "Path to the Cairo PIE output file. Cannot be used in proof_mode.",
        conflicts_with_all = &["air_public_input", "air_private_input", "proof_mode"]
    )]
    cairo_pie_output: Option<PathBuf>,
    #[clap(
        long = "air_public_input",
        conflicts_with = "cairo_pie_output",
        requires_all = &["proof_mode", "air_private_input"],
        help = "Path to the AIR public input file. Can only be used in proof_mode."
    )]
    air_public_input: Option<PathBuf>,
    #[clap(
        long = "air_private_input",
        conflicts_with = "cairo_pie_output",
        requires_all = &["proof_mode", "air_public_input"],
        help = "Path to the AIR private input file. Can only be used in proof_mode."
    )]
    air_private_input: Option<PathBuf>,
    #[clap(long = "trace_file", help = "Path to the trace output file.")]
    trace_file: Option<PathBuf>,
    #[clap(long = "memory_file", help = "Path to the memory output file.")]
    memory_file: Option<PathBuf>,
    #[clap(long = "layout", default_value =  LayoutName::plain.to_str(), value_enum)]
    layout: LayoutName,
    // Required when using with dynamic layout. Ignored otherwise.
    #[clap(
        long = "dynamic_params_file",
        required_if_eq("layout", LayoutName::dynamic.to_str())
    )]
    dynamic_params_file: Option<PathBuf>,
    #[clap(
        long = "proof_mode",
        help = "Enable proof mode config.",
        conflicts_with = "cairo_pie_output",
        requires_all = &["air_public_input", "air_private_input"]
    )]
    proof_mode: bool,
    #[clap(
        long = "disable_trace_padding",
        help = "Disable padding of the execution trace at the end of the run. Requires proof_mode.",
        requires = "proof_mode"
    )]
    disable_trace_padding: bool,
    #[clap(
        long = "merge_extra_segments",
        help = "Merge extra memory segments into one before creating the PIE of the run."
    )]
    merge_extra_segments: bool,
    #[clap(
        long = "allow_missing_builtins",
        value_parser = parse_bool,
        num_args = 0..=1,
        default_missing_value = "true",
        help = "Allow initializing the runner with builtins in the program that are not present in
        the layout."
    )]
    allow_missing_builtins: bool,
    #[clap(
        long = "outputs_file",
        help = "Write the program's output segment content after the run to this file."
    )]
    outputs_file: Option<PathBuf>,
    #[clap(
        long = "execution_resources_file",
        help = "Write the program's execution resources after the run to this file."
    )]
    execution_resources_file: Option<PathBuf>,
    #[clap(
        long = "relocate_mem",
        help = "Relocate memory in the VM run. Should be false in case of using the stwo adapter,
        because it includes relocation.",
        default_value = "true",
        requires = "proof_mode"
    )]
    relocate_mem: bool,
}

struct FileWriter {
    buf_writer: io::BufWriter<std::fs::File>,
    bytes_written: usize,
}

impl Writer for FileWriter {
    fn write(&mut self, bytes: &[u8]) -> Result<(), bincode::error::EncodeError> {
        self.buf_writer
            .write_all(bytes)
            .map_err(|e| bincode::error::EncodeError::Io {
                inner: e,
                index: self.bytes_written,
            })?;

        self.bytes_written += bytes.len();

        Ok(())
    }
}

impl FileWriter {
    fn new(buf_writer: io::BufWriter<std::fs::File>) -> Self {
        Self {
            buf_writer,
            bytes_written: 0,
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.buf_writer.flush()
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = match Args::try_parse_from(env::args()) {
        Ok(args) => args,
        Err(err) => err.exit(),
    };

    let program = get_program(args.program.as_path())?;
    let program_input_contents = get_program_input(&args.program_input)?;
    let cairo_run_config = get_cairo_run_config(
        &args.dynamic_params_file,
        args.layout,
        args.proof_mode,
        args.disable_trace_padding,
        args.allow_missing_builtins,
        args.relocate_mem, // will affect only if proof_mode is true
    )?;

    let mut runner = cairo_run_program(&program, program_input_contents, cairo_run_config)?;

    // Handle program output file if specified
    if let Some(outputs_file) = args.outputs_file {
        let mut output_buffer = String::new();
        runner.vm.write_output(&mut output_buffer)?;
        let output_lines = output_buffer
            .lines()
            .map(|line| {
                Felt252::from_dec_str(line)
                    .map_err(|_| format!("Failed to parse output line as Felt decimal: {line}"))
            })
            .collect::<Result<Vec<Felt252>, _>>()?;
        std::fs::write(outputs_file, serde_json::to_string_pretty(&output_lines)?)?;
    }

    // Handle execution resources file if specified
    if let Some(execution_resources_file) = args.execution_resources_file {
        let execution_resources = runner.get_execution_resources()?;
        std::fs::write(
            execution_resources_file,
            serde_json::to_string_pretty(&execution_resources)?,
        )?;
    }

    // Handle Cairo PIE output if specified
    if let Some(pie_output_path) = args.cairo_pie_output {
        runner
            .get_cairo_pie()
            .map_err(CairoRunError::Runner)?
            .write_zip_file(pie_output_path.as_ref(), args.merge_extra_segments)?;
    }

    if !args.proof_mode {
        // Return early if not in proof mode
        return Ok(());
    }

    if let Some(ref air_public_input_file) = args.air_public_input {
        std::fs::write(
            air_public_input_file,
            runner.get_air_public_input()?.serialize_json()?,
        )?;
    }

    let relocated_trace = runner
        .relocated_trace
        .as_ref()
        .expect("trace not relocated");

    let (trace_file, trace_file_path) = if let Some(ref path) = args.trace_file {
        let file = std::fs::File::create(path)?;
        let path = path.clone();
        (file, path)
    } else {
        NamedTempFile::new()?.keep()?
    };

    let mut trace_writer =
        FileWriter::new(io::BufWriter::with_capacity(3 * 1024 * 1024, trace_file));

    cairo_run::write_encoded_trace(relocated_trace, &mut trace_writer)?;
    trace_writer.flush()?;

    let (memory_file, memory_file_path) = if let Some(ref path) = args.memory_file {
        let file = std::fs::File::create(path)?;
        let path = path.clone();
        (file, path)
    } else {
        NamedTempFile::new()?.keep()?
    };

    let mut memory_writer =
        FileWriter::new(io::BufWriter::with_capacity(5 * 1024 * 1024, memory_file));

    cairo_run::write_encoded_memory(&runner.relocated_memory, &mut memory_writer)?;
    memory_writer.flush()?;

    if let Some(ref air_private_input_file) = args.air_private_input {
        let json = runner
            .get_air_private_input()
            .to_serializable(
                trace_file_path.to_string_lossy().to_string(),
                memory_file_path.to_string_lossy().to_string(),
            )
            .serialize_json()?;
        std::fs::write(air_private_input_file, json)?;
    }

    Ok(())
}
