#!/bin/bash
cargo +nightly-2026-01-15 clippy "$@" --all-targets --all-features -- -D warnings -D future-incompatible \
    -D nonstandard-style -D rust-2018-idioms -D unused
