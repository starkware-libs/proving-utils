use cairo_air::PreProcessedTraceVariant;
use cairo_vm::cairo_run::CairoRunConfig;
use cairo_vm::types::layout_name::LayoutName;
use privacy_circuit_verify::consts::PCS_CONFIG;
use stwo_cairo_prover::prover::{ChannelHash, ProverParameters};

pub const CAIRO_RUN_CONFIG: CairoRunConfig<'_> = CairoRunConfig {
    trace_enabled: true,
    relocate_trace: false,
    layout: LayoutName::all_cairo_stwo,
    fill_holes: true,
    proof_mode: true,
    disable_trace_padding: true,
    entrypoint: "main",
    relocate_mem: false,
    dynamic_layout_params: None,
    secure_run: Some(false),
    allow_missing_builtins: Some(true),
};

pub const PROVER_PARAMS: ProverParameters = ProverParameters {
    channel_hash: ChannelHash::Blake2sM31,
    pcs_config: PCS_CONFIG,
    preprocessed_trace: PreProcessedTraceVariant::CanonicalSmall,
    channel_salt: 0,
    store_polynomials_coefficients: true,
    include_all_preprocessed_columns: true,
};
