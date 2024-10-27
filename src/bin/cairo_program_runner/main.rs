use std::env;
use std::error::Error;
use std::io::{self, Write};
use std::path::PathBuf;

use bincode::enc::write::Writer;
use cairo_vm::types::layout::CairoLayoutParams;
use cairo_vm::types::layout_name::LayoutName;

use cairo_program_runner::cairo_run_program;
use cairo_vm::cairo_run;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use clap::Parser;
use tempfile::NamedTempFile;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "compiled_program_path", help = "Path to the compiled program")]
    compiled_program_path: PathBuf,
    #[clap(long = "program_input", help = "Path to the program input file.")]
    program_input: PathBuf,
    #[clap(
        long = "cairo_pie_output",
        help = "Path to the Cairo PIE output file. Cannot be used in proof_mode.",
        conflicts_with_all = &["air_public_input", "air_private_input"]
    )]
    cairo_pie_output: Option<PathBuf>,
    #[clap(
        long = "air_public_input",
        conflicts_with = "cairo_pie_output",
        help = "Path to the AIR public input file. Can only be used in proof_mode."
    )]
    air_public_input: Option<PathBuf>,
    #[clap(
        long = "air_private_input",
        conflicts_with = "cairo_pie_output",
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
    let program = Program::from_file(args.compiled_program_path.as_path(), Some("main"))?;

    let program_name = args
        .compiled_program_path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap();

    let program_input_contents = std::fs::read_to_string(&args.program_input)?;

    let dynamic_layout_params = match args.dynamic_params_file {
        Some(file) => {
            assert!(
                args.layout == LayoutName::dynamic,
                "dynamic_params_file should not be provided for layout {}.",
                args.layout
            );
            Some(CairoLayoutParams::from_file(&file)?)
        }
        None => None,
    };
    let runner = cairo_run_program(
        &program,
        program_name,
        program_input_contents,
        args.layout,
        dynamic_layout_params,
    )?;

    if let Some(ref file_name) = args.cairo_pie_output {
        runner
            .get_cairo_pie()
            .map_err(CairoRunError::Runner)?
            .write_zip_file(file_name)?
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
