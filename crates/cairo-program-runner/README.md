# cairo_program_runner

Run a compiled Cairo program, optionally produce a Cairo PIE, and (in proof mode) generate AIR public/private inputs plus encoded trace/memory files.
This runner uses a custom hint processor that supports internal programs used in SHARP, namely bootloaders and cairo verifier hints.
It also uses the hints implemented in lambda-class's `cairo-vm` repo for hints from the cairo common library.

Entry point: `crates/cairo-program-runner/src/bin/cairo_program_runner/main.rs`

## Build & run

cargo run -p cairo-program-runner --bin cairo_program_runner -- --help

## Basic run (no proof mode)

Runs the program. You may also dump:

- program outputs (`--outputs_file`)
- execution resources (`--execution_resources_file`)
- Cairo PIE (`--cairo_pie_output`)

Example:
cargo run -p cairo-program-runner --bin cairo_program_runner -- \
 --program path/to/compiled_program.json \
 --program_input path/to/program_input.json \
 --layout plain \
 --outputs_file outputs.json \
 --execution_resources_file execution_resources.json

- The options for `--layout` are: `plain`, `small`, `dex`, `recursive`, `starknet`, `starknet_with_keccak`, `recursive_large_output`, `recursive_with_poseidon`, `all_solidity`, `all_cairo`, `dynamic`, `all_cairo_stwo`, `perpetual`, `dex_with_bitwise`. See the `LayoutName` enum definition in `cairo-vm`.

### Cairo PIE output

Write a Cairo PIE zip file:
cargo run -p cairo-program-runner --bin cairo_program_runner -- \
 --program path/to/compiled_program.json \
 --program_input path/to/program_input.json \
 --layout plain \
 --cairo_pie_output run.pie.zip

Optional:

- `--merge_extra_segments`: merge extra memory segments before creating the PIE.

Note: `--cairo_pie_output` cannot be used with `--proof_mode`.

## Proof mode

Proof mode enables generation of AIR inputs and encoded trace/memory.

Required flags (must be provided together):

- `--proof_mode`
- `--air_public_input <PATH>`
- `--air_private_input <PATH>`

Optional outputs:

- `--trace_file <PATH>` (if omitted, a temp file is created)
- `--memory_file <PATH>` (if omitted, a temp file is created)

Example:
cargo run -p cairo-program-runner --bin cairo_program_runner -- \
 --program path/to/compiled_program.json \
 --program_input path/to/program_input.json \
 --layout plain \
 --proof_mode \
 --air_public_input air_public_input.json \
 --air_private_input air_private_input.json \
 --trace_file trace.bin \
 --memory_file memory.bin

## Flag notes

- `--disable_trace_padding`: disables padding the trace at end of run. Requires `--proof_mode`.
- `--relocate_mem [true|false]` (default: `true`): only applies in proof mode; set `false` if relocation will be done later (e.g., by an adapter).
- `--allow_missing_builtins[=true|false]`: boolean flag with optional value. Allows running programs that reference builtins not present in the layout (will fail if the run actually uses them).
  - default: `false`
  - `--allow_missing_builtins` (without value) sets it to `true`
  - accepts `true/false/1/0`
- `--dynamic_params_file`: required only when `--layout dynamic`. This is the path to the dynamic layout parameters JSON file.

## Outputs

- `--outputs_file`: JSON array of output segment felts (parsed from VM output as decimal felts).
- `--execution_resources_file`: JSON-serialized execution resources.
- `--cairo_pie_output`: Cairo PIE zip file (non-proof mode only).
- `--air_public_input`: AIR public input JSON (proof mode only).
- `--air_private_input`: AIR private input JSON referencing trace/memory file paths (proof mode only).
- `--trace_file` / `--memory_file`: encoded (binary) trace/memory.

## Notes

If `--trace_file` / `--memory_file` are not provided in proof mode, temporary files are created and kept on disk, and their paths are embedded into the AIR private input.
