#!/bin/bash

# Script Description:
# This script runs benchmarks of the program runner on the simple bootloader wrapping
# Cairo PIE files with different Rust optimization levels.
# It measures program load time, execution time, and execution resources of the run.
# Results are saved to a file.
#
# Usage:
#   ./run_all_pies.sh [--opt-levels=<levels>] [--pie-dir=path/to/pies]
#
# Options:
#   --opt-levels=<levels>  Specify which Rust optimization levels to run (0-3)
#                         Examples: --opt-levels=3 (default, runs only level 3)
#                                  --opt-levels=23 (runs levels 2 and 3)
#                                  --opt-levels=013 (runs levels 0, 1, and 3)
#   --pie-dir=<path>      Path to directory containing PIE files
#                         Default: ./pies
#
# Output:
#   - Shows compilation and execution progress in the terminal
#   - Saves detailed benchmark results to benchmark_results.txt in the scripts directory
#   - For each PIE file and optimization level, captures:
#     * Program load and execution times
#     * Number of steps and memory holes
#     * Detailed builtin instance counter information
#
# Examples:
#   ./run_all_pies.sh                          # Run with default settings (opt-level 3)
#   ./run_all_pies.sh --opt-levels=012        # Run with optimization levels 0, 1, and 2
#   ./run_all_pies.sh --pie-dir=/path/to/pies # Use PIE files from custom directory

# Default values
SCRIPT_DIR="$(dirname "$0")"
PIES_DIR="$SCRIPT_DIR/pies"
RESULTS_FILE="$SCRIPT_DIR/benchmark_results.txt"
OPT_LEVELS="3" # Default to only opt level 3

# Parse command line arguments
while [ $# -gt 0 ]; do
    case "$1" in
        --opt-levels=*)
            OPT_LEVELS="${1#*=}"
            ;;
        --pie-dir=*)
            PIES_DIR="${1#*=}"
            ;;
        *)
            echo "Unknown parameter: $1"
            echo "Usage: $0 [--opt-levels=<levels>] [--pie-dir=path/to/pies]"
            echo "  --opt-levels: Specify which optimization levels to run (0-3)"
            echo "               Examples: --opt-levels=23 (runs levels 2 and 3)"
            echo "                        --opt-levels=013 (runs levels 0, 1, and 3)"
            echo "  --pie-dir:   Path to directory containing PIE files"
            exit 1
            ;;
    esac
    shift
done

# Clear previous results
echo "Cairo PIE Benchmark Results" > "$RESULTS_FILE"
date >> "$RESULTS_FILE"
echo "----------------------------------------" >> "$RESULTS_FILE"

# Function to run cargo with specific opt level
run_with_opt_level() {
    local pie_file="$1"
    local opt_level="$2"
    
    echo "Running ${pie_file} with optimization level ${opt_level}"
    echo "Running ${pie_file} with optimization level ${opt_level}" >> "$RESULTS_FILE"
    
    # Run cargo and show compilation/execution stages, but redirect only benchmark results and resources to file
    if ! RUSTFLAGS="-C opt-level=${opt_level}" cargo run --bin benchmark_runner "${pie_file}" \
        2> >(grep -v "future version of Rust\|future-incompat-report" >&2) | \
        tee >(awk '!/Program (load|execution) time:/ && (/Program (loaded|executed)/ || /Execution Resources:/ || /^n_steps:/ || /^n_memory_holes:/ || /^builtin_instance_counter:/ || /^[[:space:]]*[a-z_]+:/ || /^}/ || /Total time:/)' >> "$RESULTS_FILE"); then
        echo "Error running benchmark" >> "$RESULTS_FILE"
    fi
    echo "----------------------------------------" >> "$RESULTS_FILE"
}

# Find all .zip files in pies directory
for pie_file in "$PIES_DIR"/*.zip; do
    if [ -f "$pie_file" ]; then
        echo "=== Testing $(basename "$pie_file") ==="
        echo
        
        # Run with specified optimization levels
        # Validate opt levels
        for opt_level in $(echo "$OPT_LEVELS" | grep -o .); do
            if [[ ! "$opt_level" =~ ^[0-3]$ ]]; then
                echo "Error: Invalid optimization level '$opt_level'. Must be one of: 0, 1, 2, 3"
                exit 1
            fi
            run_with_opt_level "$pie_file" "$opt_level"
            echo
        done
        
        echo "================================================"
        echo
    fi
done
