# stwo-vm-runner

Runs a compiled Cairo program in a proof-mode configuration, adapts the run result to a `stwo_cairo_adapter::ProverInput`, using stwo-cairo's adapter implementation and writes execution resources (and optionally the prover input) to disk.

Entry point: `crates/vm_runner/src/main.rs`

## Build & run

cargo run -p stwo-vm-runner -- --help

## Usage

Required flags:

- `--program <PATH>`: absolute path to compiled program
- `--layout <LAYOUT>`: Cairo VM layout
- `--output_execution_resources_path <PATH>`: absolute path to write execution resources JSON

- The options for `--layout` are: `plain`, `small`, `dex`, `recursive`, `starknet`, `starknet_with_keccak`, `recursive_large_output`, `recursive_with_poseidon`, `all_solidity`, `all_cairo`, `dynamic`, `all_cairo_stwo`, `stwo_no_ecop`, `perpetual`, `dex_with_bitwise`. See the `LayoutName` enum definition in `cairo-vm`.

Optional:

- `--program_input <PATH>`: absolute path to program input
- `--output_prover_input_path <PATH>`: absolute path to write prover input JSON
- `--secure_run`: enable Cairo VM secure_run mode

Example:
cargo run -p stwo-vm-runner -- \
 --program /abs/path/to/compiled_program.json \
 --program_input /abs/path/to/program_input.json \
 --layout plain \
 --output_execution_resources_path /abs/path/to/execution_resources.json \
 --output_prover_input_path /abs/path/to/prover_input.json \
 --secure_run

## What it does

1. Runs the Cairo program with:
   - `proof_mode = true`
   - `trace_enabled = true`
   - `fill_holes = true`
   - `disable_trace_padding = true`
   - `relocate_mem = false`, `relocate_trace = false` (adapter handles relocation)
2. Calls `stwo_cairo_adapter::adapter::adapt(&cairo_runner)` to produce `ProverInput`.
3. Writes:
   - `ProverInput` (optional)
   - `ExecutionResources` (always)

## Output files

- Prover input (`--output_prover_input_path`): JSON serialization of `ProverInput`.
- Execution resources (`--output_execution_resources_path`): JSON serialization of `ExecutionResources::from_prover_input(&prover_input)`.
