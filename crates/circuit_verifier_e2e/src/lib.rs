//! End-to-end driver for the `stwo-cairo` Cairo-circuit verifier.
//!
//! The Cairo circuit verifier (built in `stwo-cairo/stwo_cairo_verifier/crates/circuit_verifier`)
//! takes a recursive circuit proof and verifies it inside Cairo. To run it, we need a real
//! recursive circuit proof + a `CircuitVerifierConfig`, both serialized as a felt252
//! stream that `scarb execute --arguments-file` reads.
//!
//! This crate produces that stream, mirroring the privacy chain in
//! `privacy_prove::privacy_recursive_prove` but extending it with the extra
//! "verify-the-recursive-circuit-proof-IN-CIRCUIT-and-prove-that" step.
//!
//! Pipeline (matches the user-stated flow):
//!   1. compile cairo program (caller-provided `.json` / `.executable.json`)
//!   2. run_and_adapt
//!   3. prove with `cairo_prove` (stwo-cairo-prover)
//!   4. verify with circuit-cairo verifier in circuit (build_fixed_cairo_circuit)
//!   5. prove that with circuit prover -> `circuit_proof_1`
//!   6. verify circuit_proof_1 with circuit-circuit verifier in circuit
//!     (`circuit_air::verify::build_verification_circuit`)
//!   7. prove that with circuit prover -> `circuit_proof_2`
//!   8. dump felts for `stwo-cairo`'s Cairo circuit verifier to consume
//!
//! Steps 1–5 reuse `privacy_prove::privacy_recursive_prove`. This crate adds 6–8.

pub mod recurse;
