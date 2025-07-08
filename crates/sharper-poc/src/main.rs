use axum::{
    routing::{get, post},
    Router, response::IntoResponse, http::StatusCode,
};

use axum::{
    body::Body,
};

mod utils;
use tokio::net::TcpListener;

#[tokio::main]
async fn main() {
    // Build the app with some routes
    let app = Router::new()
        .route("/is_alive", get(is_alive))
        .route("/get_proof", post(get_proof));

    // Run the server
    println!("Server listening on http://127.0.0.1:3000");
    // bind a listener
    let listener = TcpListener::bind("127.0.0.1:3000")
        .await
        .expect("bind listener");

    // run the server
    axum::serve(listener, app).await.expect("server failed");
}

use axum::{
    extract::{Query, Json},
};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct UriParams {
    customer_id: String,
    cairo_job_key: String,
}

#[derive(Debug, Deserialize)]
struct BodyPayload {
    cairo_pie_encoded: String,
}

// Implemented routes
async fn get_proof(
    Query(params): Query<UriParams>,
    body: axum::body::Body,
) -> impl IntoResponse {
    if !utils::is_add_job_enabled(0) {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            "Job addition is disabled",
        ).into_response();
    }
    let decoded_bytes = match utils::decode_cairo_pie_bytes(body).await {
        Ok(d) => d,
        Err((status, msg)) => return (status, msg).into_response(),
    };

    let message = format!(
        "Received job '{}' from customer {}, decoded {} bytes",
        params.cairo_job_key, params.customer_id, decoded_bytes.len()
    );

    (StatusCode::OK, message).into_response()
}


async fn is_alive() -> impl IntoResponse {
    (StatusCode::OK, "Server is alive")
}
