# Proving Utils Workspace

This workspace contains multiple CLI binaries. Start here, then follow the links to each binary’s README for full usage.


## Binaries

### `cairo_program_runner` (crate: `cairo-program-runner`)

Runs a compiled Cairo program. Can optionally:

- write a Cairo PIE (non-proof mode), or
- in proof mode, generate AIR public/private inputs plus encoded trace/memory.

Docs: `crates/cairo-program-runner/README.md`

Quick start:
cargo run -p cairo-program-runner --bin cairo_program_runner -- --help


### `stwo-vm-runner`

Runs a compiled Cairo program in proof-mode config and adapts the result to `stwo_cairo_adapter::ProverInput`. Writes execution resources, and optionally prover input.

Docs: `crates/vm_runner/README.md`

Quick start:
cargo run -p stwo-vm-runner -- --help


### `stwo-run-and-prove`

Runs a compiled cairo program and generates a Stwo proof for it. Optionally verifies the proof, and saves the program output and data for debugging.

Docs: `crates/stwo_run_and_prove/README.md`

Quick start:
cargo run -p stwo-run-and-prove -- --help


## Build

cargo build --release
