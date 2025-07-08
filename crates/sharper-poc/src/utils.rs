// src/utils.rs



//TODO
pub fn is_add_job_enabled(n: u32) -> bool {
    true
}

pub fn cairo_run() -> Result<(), String> {
    // Placeholder for the actual Cairo run logic
    // This function should implement the logic to run a Cairo program
    // and return an appropriate result.
    Ok(())

    // let program = get_program(args.program.as_path())?;
    // let program_input_contents = get_program_input(&args.program_input)?;
    // let cairo_run_config = get_cairo_run_config(
    //     &args.dynamic_params_file,
    //     args.layout,
    //     args.proof_mode,
    //     args.disable_trace_padding,
    //     args.allow_missing_builtins,
    //     args.relocate_mem, // will affect only if proof_mode is true
    // )?;

    // let mut runner = cairo_run_program(&program, program_input_contents, cairo_run_config)?;
}
use axum::{
    body::to_bytes,
    http::StatusCode,
};

use base64::{engine::general_purpose, Engine as _};

pub async fn decode_cairo_pie_bytes(
    body: axum::body::Body,
) -> Result<Vec<u8>, (StatusCode, &'static str)> {
    let request_body_limit = 104_857_600;
    
    // Read full body bytes
    let bytes = to_bytes(body, request_body_limit).await
        .map_err(|_| (StatusCode::BAD_REQUEST, "Failed to read body"))?;
    
    // Decode base64
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(&bytes)
        .map_err(|_| (StatusCode::BAD_REQUEST, "Invalid base64"))?;
    
    Ok(decoded)
}
