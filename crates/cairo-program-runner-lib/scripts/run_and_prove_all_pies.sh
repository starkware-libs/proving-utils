#!/bin/bash
# run_and_prove_all_pies.sh
# Runs benchmark_run_and_prove.rs on all PIE files in the pies directory.
# Usage: ./run_and_prove_all_pies.sh [--pie-dir=path/to/pies]

SCRIPT_DIR="$(dirname "$0")"
PIES_DIR="$SCRIPT_DIR/pies"
RESULTS_FILE="$SCRIPT_DIR/run_and_prove_results.txt"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../" && pwd)"

# Parse command line arguments
while [ $# -gt 0 ]; do
    case "$1" in
        --pie-dir=*)
            PIES_DIR="${1#*=}"
            ;;
        *)
            echo "Unknown parameter: $1"
            echo "Usage: $0 [--pie-dir=path]"
            exit 1
            ;;
    esac
    shift
done

mkdir -p "$REPO_ROOT/temp_proofs"

echo "Cairo PIE Prove Benchmark Results" > "$RESULTS_FILE"
date >> "$RESULTS_FILE"
echo "----------------------------------------" >> "$RESULTS_FILE"

# Compile only the required binaries with CPU native optimizations
RUSTFLAGS="-C target-cpu=native" cargo build --release --bin benchmark_run_and_prove --bin stwo_run_and_prove

# Change to the repo root to ensure all relative paths work in the Rust binary
cd "$REPO_ROOT" || exit 1

BIN_PATH="target/release/benchmark_run_and_prove"

for pie_file in "$PIES_DIR"/*.zip; do
    if [ -f "$pie_file" ]; then
        pie_name=$(basename "$pie_file")
        echo "Proving $pie_name..."
        # Use absolute path for pie_file to avoid NotFound errors
        abs_pie_file="$(realpath "$pie_file")"
        output=$("$BIN_PATH" "$abs_pie_file" 2>&1)
        echo "$output"
        echo "$pie_name: $output" >> "$RESULTS_FILE"
        echo "----------------------------------------" >> "$RESULTS_FILE"
    fi
done

echo "Done. Results saved to $RESULTS_FILE"
