FROM rust:1.76 as builder
WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:buster-slim
COPY --from=builder /app/target/release/your_app /usr/local/bin/your_app
CMD ["sharper"]
