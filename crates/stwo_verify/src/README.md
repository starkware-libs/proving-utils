# stwo_verify

Verifies a serialized Stwo Cairo proof and optionally extracts the program output and program hash.

Entry point: `crates/stwo_verify/src/main.rs`


## Build & run

cargo run -p stwo_verify -- --help


## Basic usage

Required arguments:
- `--proof_path <PathBuf>`: Absolute path to the serialized proof file.

Basic Example:
cargo run -p stwo_verify -- \
 --proof_path path/to/proof.json

Optional arguments:
- `--proof_format <ProofFormat>`: Proof format (Json, CairoSerde, or Binary. default: CairoSerde).
- `--channel_hash <String>`: Hash variant for the Merkle channel (blake2s or poseidon252. default: blake2s).
- `--program_output <PathBuf>`: Absolute path where the program's output will be saved.
- `--program_hash_output <PathBuf>`: Absolute path where the program hash will be saved.
- `--preprocessed_trace <String>`: Preprocessed trace variant (canonical or canonical_without_pedersen. default: canonical).

Example with output extraction:
cargo run -p stwo_verify -- \
 --proof_path path/to/proof.json \
 --proof_format CairoSerde \
 --channel_hash blake2s \
 --program_output path/to/output.json \
 --program_hash_output path/to/hash.txt


## What it does

1. Deserializes the proof from the given file according to the specified format.
2. Extracts the verification output (program hash and program output) using `get_verification_output`.
3. Optionally saves the program output and program hash to the specified paths.
4. Verifies the proof using `verify_cairo`.
5. Returns exit code 0 if verification succeeds, non-zero otherwise.


## Outputs

- Program output (`--program_output`): JSON array of program output felts as hex strings (if specified).
- Program hash (`--program_hash_output`): Program hash as a hex string (if specified).


## Exit codes

- 0: Proof is valid.
- 1: Proof is invalid or verification failed.


## Usage from Rust

When invoking via `std::process::Command`, check the exit code to determine proof validity:

```rust
use std::process::Command;

let status = Command::new("stwo_verify")
    .arg("--proof_path")
    .arg("path/to/proof.json")
    .status()?;

if status.success() {
    println!("Proof is valid!");
} else {
    println!("Proof is invalid!");
}
```
