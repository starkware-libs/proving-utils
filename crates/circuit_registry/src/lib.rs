//! The circuit registry: the set of verifier circuits the system supports, identified by their
//! preprocessed roots. This crate defines the registry's JSON schema ([`CircuitRegistry`] and
//! friends), shared by the `circuit-params` tool that emits a registry and by the leaf prover that
//! reads its pad target from one.

mod schema;

pub use schema::{CircuitConfig, CircuitRegistry, LeafVerifier, LogSizes, Multiverifier, RootHex};
