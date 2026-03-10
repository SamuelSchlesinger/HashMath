# Multi-stage build for hm-net
#
# Build:  docker build -t hm-net .
# Run:    docker run --rm -p 4256:4256 -p 4257:4257 hm-net

# ── Builder ──────────────────────────────────────────────────────
FROM rust:1-bookworm AS builder

WORKDIR /build

# Cache dependency compilation
COPY Cargo.toml Cargo.lock* ./
RUN mkdir src && echo 'fn main() {}' > src/main.rs \
    && cargo build --release \
    && rm -rf src

# Build actual binary
COPY src/ src/
RUN touch src/main.rs && cargo build --release

# ── Runtime ──────────────────────────────────────────────────────
FROM debian:bookworm-slim

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -r -m -s /bin/false hmnet

COPY --from=builder /build/target/release/hm-net /usr/local/bin/hm-net

USER hmnet
VOLUME /data
EXPOSE 4256 4257

ENTRYPOINT ["hm-net"]
CMD ["--data-dir", "/data", "--listen", "/ip4/0.0.0.0/tcp/4256", "--health-port", "4257", "--headless", "--public"]
