# stwo-run-and-prove

Runs a compiled Cairo program and generates a Stwo proof for it. Optionally verifies the proof.
Saves the proof to the given path with the requested format, and optionally saves the program output and data for debugging.

Entry point: `crates/stwo_run_and_prove/src/main.rs`


## Build & run

cargo run -p stwo-run-and-prove -- --help


## Basic usage

Required arguments:
- `--program <PathBuf>`: Absolute path to the compiled Cairo program.
- `--proof_path <PathBuf>`: Absolute path where the generated proof will be saved.

Basic Example:
cargo run -p stwo-run-and-prove -- \
 --program path/to/compiled_program.json \
 --proof_path proof.json

Optional arguments:
- `--program_input <PathBuf>`: Absolute path to the program input file.
- `--program_output <PathBuf>`: Absolute path where the program's output will be saved.
- `--prover_params_json <PathBuf>`: Absolute path to the JSON file containing the prover parameters.
- `--proof_format <ProofFormat>`: Proof format (Json or CairoSerde. default: CairoSerde).
- `--verify`: Verifies the generated proof.
- `--save_debug_data`: Saves the ProverInput to a file in `debug_data_dir` for both success and failure.
- `--debug_data_dir <PathBuf>`: Absolute path to the output directory where the ProverInput will be saved in the
                                case of a proving error, or when the save_debug_data flag is enabled.

Example with verification and debug data:
cargo run -p stwo-run-and-prove -- \
 --program path/to/compiled_program.json \
 --program_input path/to/program_input.json \
 --proof_path path/to/proof.json \
 --verify \
 --debug_data_dir path/to/debug_output \
 --save_debug_data


## What it does

1. Runs the given Cairo program with cairo-vm.
2. Calls `stwo_cairo_adapter::adapter::adapt(&cairo_runner)` to produce `ProverInput`.
3. Proves the program, and optionally verifies it.
4. Saves the proof, and optionally the program's output and the debug data, to the given paths.


## Outputs

- Proof (`--proof_path`): Stwo proof file in the specified format.
- Program output (`--program_output`): JSON array of program output felts (if specified).
- Debug data: ProverInput JSON saved to `debug_data_dir` (when `--save_debug_data` is enabled or on proving failure).
