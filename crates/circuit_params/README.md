# circuit-params

Computes the per-component sizes of the leaf-prover verifier circuit for a range of verified trace
sizes, using the CANONICAL preprocessed trace config. It reports two circuits:

- the **leaf verifier** circuit, which verifies one Cairo proof (reported for every trace size), and
- the **multiverifier** circuit, which verifies two proofs of the leaf verifier circuit (reported
  once, for the largest trace size).

Entry point: `crates/circuit_params/src/main.rs`

## Build & run

    cargo run -p circuit-params -- --help

## Usage

Required flags:

- `--min-trace-log-size <N>`: smallest verified trace log size to measure (inclusive). A canonical
  Cairo trace commits its preprocessed sequence columns at `MAX_SEQUENCE_LOG_SIZE = 25`, so a real
  canonical leaf proof has `log_trace_size >= 25`.
- `--max-trace-log-size <N>`: largest verified trace log size to measure (inclusive).

Optional:

- `--log_blowup_factor <N>`: log blowup factor of the verified Cairo proof (1, 2, or 3, default 1).
- `--format <FORMAT>`: output format, `info` (default) or `json` (see below).
- `--output-path <PATH>`: file to write the output to. Prints to stdout if omitted.

Example:

    cargo run -p circuit-params -- \
      --min-trace-log-size 25 \
      --max-trace-log-size 25 \
      --format json \
      --output-path /abs/path/to/params.json

## Output formats

### `info`

Human-readable. One line per circuit and trace size, giving each AIR component's padded log size and
its usage percentage (how much of the padded power-of-two component is actually used).

Can be used to choose circuit configurations and to find components whose size can be reduced.

### `json`

The JSON has three top-level fields:

- `circuit_configs`: a registry mapping a config id (a string) to a config — its `log_blowup_factor`
  and padded `component_log_sizes`. Circuits sharing a config produce proofs a common AIR can verify.
- `leaf_verifiers`: the leaf verifier circuits, each referencing its `config` (by id), its
  `trace_log_size`, the verified proof's `log_blowup_factor`, and its `preprocessed_root`.
- `multiverifiers`: the multiverifier circuits, each referencing its own `config` (by id), the
  `input_configs` (by id) of the circuits whose proofs it verifies, and its `preprocessed_root`.
