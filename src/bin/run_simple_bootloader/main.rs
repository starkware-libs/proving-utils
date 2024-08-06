use std::env;
use std::error::Error;
use std::io::{self, Write};
use std::path::PathBuf;

use bincode::enc::write::Writer;
use cairo_vm::cairo_run::{self, cairo_run_program_with_initial_scope, CairoRunConfig};
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::layout_name::LayoutName;
use cairo_vm::types::program::Program;
use cairo_vm::vm::errors::cairo_run_errors::CairoRunError;
use cairo_vm::vm::runners::cairo_runner::CairoRunner;

use cairo_bootloader::bootloaders::load_simple_bootloader;
use cairo_bootloader::tasks::make_bootloader_tasks;
use cairo_bootloader::{
    insert_simple_bootloader_input, BootloaderHintProcessor, SimpleBootloaderInput, TaskSpec,
};
use clap::Parser;
use tempfile::NamedTempFile;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(long = "air_public_input")]
    air_public_input: PathBuf,
    #[clap(long = "air_private_input")]
    air_private_input: PathBuf,
    #[clap(long = "cairo_pies", num_args = 1.., value_delimiter = ',')]
    cairo_pies: Vec<PathBuf>,
    #[clap(long = "use_poseidon", num_args = 1.., value_delimiter = ',')]
    use_poseidon: Vec<bool>,
    #[clap(
        long = "fact_topologies_path",
        help = "Path to the fact topologies output file.",
        required = true
    )]
    fact_topologies_path: PathBuf,
    #[clap(long = "layout", default_value = "plain", value_enum)]
    layout: LayoutName,
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

fn cairo_run_simple_bootloader_in_proof_mode(
    simple_bootloader_program: &Program,
    tasks: Vec<TaskSpec>,
    fact_topologies_path: PathBuf,
    layout: LayoutName,
) -> Result<CairoRunner, CairoRunError> {
    let mut hint_processor = BootloaderHintProcessor::new();

    let cairo_run_config = CairoRunConfig {
        entrypoint: "main",
        trace_enabled: true,
        relocate_mem: true,
        layout,
        proof_mode: true,
        secure_run: None,
        disable_trace_padding: false,
        allow_missing_builtins: None,
    };

    // Build the bootloader input
    let simple_bootloader_input = SimpleBootloaderInput {
        fact_topologies_path: Some(fact_topologies_path),
        single_page: true,
        tasks,
    };

    // Note: the method used to set the bootloader input depends on
    // https://github.com/lambdaclass/cairo-vm/pull/1772 and may change depending on review.
    let mut exec_scopes = ExecutionScopes::new();
    insert_simple_bootloader_input(&mut exec_scopes, simple_bootloader_input);
    exec_scopes.insert_value("bootloader_program", simple_bootloader_program.clone());

    // Run the bootloader
    cairo_run_program_with_initial_scope(
        simple_bootloader_program,
        &cairo_run_config,
        &mut hint_processor,
        exec_scopes,
    )
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = match Args::try_parse_from(env::args()) {
        Ok(args) => args,
        Err(err) => err.exit(),
    };

    let simple_bootloader_program = load_simple_bootloader()?;

    let tasks = make_bootloader_tasks(
        &[],
        &args
            .cairo_pies
            .iter()
            .map(std::fs::read)
            .collect::<Result<Vec<_>, _>>()?
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>()[..],
        args.use_poseidon,
    )?;

    let runner = cairo_run_simple_bootloader_in_proof_mode(
        &simple_bootloader_program,
        tasks,
        args.fact_topologies_path,
        args.layout,
    )?;

    std::fs::write(
        args.air_public_input,
        runner.get_air_public_input()?.serialize_json()?,
    )?;

    let relocated_trace = runner
        .relocated_trace
        .as_ref()
        .expect("trace not relocated");

    let (trace_file, trace_file_path) = NamedTempFile::new()?.keep()?;

    let mut trace_writer =
        FileWriter::new(io::BufWriter::with_capacity(3 * 1024 * 1024, trace_file));

    cairo_run::write_encoded_trace(relocated_trace, &mut trace_writer)?;
    trace_writer.flush()?;

    let (memory_file, memory_file_path) = NamedTempFile::new()?.keep()?;
    let mut memory_writer =
        FileWriter::new(io::BufWriter::with_capacity(5 * 1024 * 1024, memory_file));

    cairo_run::write_encoded_memory(&runner.relocated_memory, &mut memory_writer)?;
    memory_writer.flush()?;

    let json = runner
        .get_air_private_input()
        .to_serializable(
            trace_file_path.to_string_lossy().to_string(),
            memory_file_path.to_string_lossy().to_string(),
        )
        .serialize_json()?;
    std::fs::write(args.air_private_input, json)?;

    Ok(())
}
