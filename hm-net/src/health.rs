//! Minimal TCP-based HTTP health check endpoint.
//!
//! Provides liveness (`/healthz`), readiness (`/readyz`), and status (`/`) endpoints
//! without requiring any HTTP framework dependencies.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tracing::{info, warn};

/// Shared node status counters, updated by the main event loop.
pub struct NodeStatus {
    pub peer_count: AtomicUsize,
    pub record_count: AtomicUsize,
    pub ready: AtomicBool,
}

impl NodeStatus {
    pub fn new() -> Self {
        Self {
            peer_count: AtomicUsize::new(0),
            record_count: AtomicUsize::new(0),
            ready: AtomicBool::new(false),
        }
    }
}

/// Run a minimal HTTP health server on the given port.
///
/// Endpoints:
/// - `/healthz` — liveness probe, always 200
/// - `/readyz` — readiness probe, 200 when listening, 503 otherwise
/// - `/health` or `/` — full status JSON (peer_id, peers, records, ready)
pub async fn run_health_server(port: u16, status: Arc<NodeStatus>, peer_id: String) {
    let addr = format!("0.0.0.0:{}", port);
    let listener = match TcpListener::bind(&addr).await {
        Ok(l) => {
            info!(addr = %addr, "health server listening");
            l
        }
        Err(e) => {
            warn!("failed to start health server on {}: {}", addr, e);
            return;
        }
    };

    loop {
        let (mut stream, _) = match listener.accept().await {
            Ok(conn) => conn,
            Err(_) => continue,
        };

        let status = status.clone();
        let peer_id = peer_id.clone();
        tokio::spawn(async move {
            let mut buf = [0u8; 1024];
            let n = match stream.read(&mut buf).await {
                Ok(n) if n > 0 => n,
                _ => return,
            };

            let request = String::from_utf8_lossy(&buf[..n]);
            let path = request
                .lines()
                .next()
                .and_then(|line| line.split_whitespace().nth(1))
                .unwrap_or("/");
            let (status_code, body) = match path {
                "/healthz" => (200, r#"{"status":"ok"}"#.to_string()),
                "/readyz" => {
                    if status.ready.load(Ordering::Relaxed) {
                        (200, r#"{"status":"ready"}"#.to_string())
                    } else {
                        (503, r#"{"status":"not ready"}"#.to_string())
                    }
                }
                "/health" | "/" => {
                    let peers = status.peer_count.load(Ordering::Relaxed);
                    let records = status.record_count.load(Ordering::Relaxed);
                    let ready = status.ready.load(Ordering::Relaxed);
                    (
                        200,
                        format!(
                            r#"{{"peer_id":"{}","peers":{},"records":{},"ready":{}}}"#,
                            peer_id, peers, records, ready
                        ),
                    )
                }
                _ => (404, r#"{"error":"not found"}"#.to_string()),
            };

            let status_text = if status_code == 200 {
                "OK"
            } else {
                "Service Unavailable"
            };
            let response = format!(
                "HTTP/1.1 {} {}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                status_code, status_text, body.len(), body
            );
            let _ = stream.write_all(response.as_bytes()).await;
        });
    }
}
