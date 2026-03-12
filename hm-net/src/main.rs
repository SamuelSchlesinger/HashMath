//! hm-net: Rust sidecar for HashMath distributed hash table.
//!
//! Communicates with the Lean `hm` process via stdin/stdout IPC.
//! Runs a libp2p node with:
//! - Kademlia DHT for provider discovery (who has hash X?)
//! - Request-response protocol for direct content transfer

mod health;
mod ipc;
mod store;
mod transfer;

use anyhow::{Context, Result};
use libp2p::{
    autonat,
    futures::StreamExt,
    identify,
    kad::{self, store::RecordStore, Mode},
    noise, relay,
    request_response::{self, ResponseChannel},
    swarm::{NetworkBehaviour, SwarmEvent},
    tcp, yamux, Multiaddr, PeerId, StreamProtocol, SwarmBuilder,
};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;
use tokio::io::{self, AsyncRead, AsyncWrite};
use tokio::sync::mpsc;
use tracing::{info, warn};

use crate::health::NodeStatus;
use crate::ipc::{recv_request, send_response, Hash, Request, Response};
use crate::store::{load_or_generate_keypair, FileStore};
use crate::transfer::{TransferCodec, TransferRequest, TransferResponse};

/// Maximum number of addresses to accept per peer from Identify.
const MAX_ADDRS_PER_PEER: usize = 20;

/// Rate limit for background DHT provider announcements (per second).
const PROVIDE_RATE_PER_SEC: u64 = 20;

/// Capacity of the background provide queue.
const PROVIDE_QUEUE_CAPACITY: usize = 1000;

/// Compiled-in fallback bootstrap peers (used when no bootstrap.toml is found).
const DEFAULT_BOOTSTRAP_PEERS: &[&str] = &[
    "/ip4/35.207.40.117/tcp/4256/p2p/12D3KooWHKxXAuWMwZik7CcuteTjfAXL8VWehnM4w1B7DYgnCv1v",
];

/// Load bootstrap peers from a TOML file.
/// Format: peers = ["/ip4/.../tcp/.../p2p/..."]
fn load_bootstrap_file(path: &std::path::Path) -> Result<Vec<String>> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("reading bootstrap file: {}", path.display()))?;
    let mut peers = Vec::new();
    for line in content.lines() {
        let line = line.trim();
        if line.starts_with('#') || line.is_empty() {
            continue;
        }
        // Parse: peers = [ "addr1", "addr2" ] or bare "addr" lines
        if line.starts_with("peers") {
            // Extract the array content between [ and ]
            if let Some(start) = line.find('[') {
                let rest = &content[content.find('[').unwrap_or(0)..];
                if let Some(end) = rest.find(']') {
                    let array_content = &rest[1..end];
                    for entry in array_content.split(',') {
                        let entry = entry.trim().trim_matches('"').trim();
                        if !entry.is_empty() && entry.starts_with('/') {
                            peers.push(entry.to_string());
                        }
                    }
                }
            }
            break;
        } else if line.starts_with('/') {
            // Bare multiaddr line
            peers.push(line.trim_matches('"').to_string());
        }
    }
    Ok(peers)
}

/// Find bootstrap.toml by searching: explicit path > data dir > next to binary > crate dir.
fn find_bootstrap_file(explicit: Option<&str>, data_dir: &std::path::Path) -> Option<PathBuf> {
    if let Some(path) = explicit {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }
    // Check data dir
    let in_data = data_dir.join("bootstrap.toml");
    if in_data.exists() {
        return Some(in_data);
    }
    // Check next to the binary
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let next_to_bin = dir.join("bootstrap.toml");
            if next_to_bin.exists() {
                return Some(next_to_bin);
            }
        }
    }
    None
}

/// Combined libp2p behaviour: Kademlia + Transfer + Identify + AutoNAT + Relay.
#[derive(NetworkBehaviour)]
struct Behaviour {
    kademlia: kad::Behaviour<FileStore>,
    transfer: request_response::Behaviour<TransferCodec>,
    identify: identify::Behaviour,
    autonat: autonat::Behaviour,
    relay_client: relay::client::Behaviour,
}

/// Pending Kademlia queries awaiting IPC responses.
struct PendingQueries {
    fetches: HashMap<kad::QueryId, Hash>,
    publishes: HashMap<kad::QueryId, Hash>,
    /// Provider lookups: query_id → hash (waiting to find who has content)
    provider_lookups: HashMap<kad::QueryId, Hash>,
    /// Transfer requests: request_id → hash (waiting for direct content transfer)
    transfer_requests: HashMap<request_response::OutboundRequestId, Hash>,
}

impl PendingQueries {
    fn new() -> Self {
        Self {
            fetches: HashMap::new(),
            publishes: HashMap::new(),
            provider_lookups: HashMap::new(),
            transfer_requests: HashMap::new(),
        }
    }
}

struct Args {
    listen_addr: Multiaddr,
    bootstrap_peers: Vec<(PeerId, Multiaddr)>,
    data_dir: PathBuf,
    max_records: usize,
    max_record_size: usize,
    public: bool,
    health_port: Option<u16>,
    headless: bool,
    bootstrap_file: Option<String>,
}

fn default_data_dir() -> PathBuf {
    dirs::data_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("hm-net")
}

fn parse_bootstrap_multiaddr(addr_str: &str) -> Result<(PeerId, Multiaddr)> {
    let addr: Multiaddr = addr_str.parse().context("invalid bootstrap address")?;
    if let Some(libp2p::multiaddr::Protocol::P2p(peer_id)) = addr.iter().last() {
        let addr_without_p2p: Multiaddr = addr
            .iter()
            .filter(|p| !matches!(p, libp2p::multiaddr::Protocol::P2p(_)))
            .collect();
        Ok((peer_id, addr_without_p2p))
    } else {
        anyhow::bail!(
            "bootstrap address must end with /p2p/<peer-id>: {}",
            addr_str
        )
    }
}

fn parse_args() -> Result<Args> {
    let mut listen_addr: Multiaddr = "/ip4/127.0.0.1/tcp/4256".parse()?;
    let mut bootstrap_peers = Vec::new();
    let mut data_dir = default_data_dir();
    let mut max_records: usize = 10_000;
    let mut max_record_size: usize = 1_048_576;
    let mut public = false;
    let mut health_port: Option<u16> = Some(4257);
    let mut use_default_bootstrap = true;
    let mut headless = false;
    let mut bootstrap_file: Option<String> = None;

    let args: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--listen" | "-l" => {
                i += 1;
                listen_addr = args
                    .get(i)
                    .context("missing listen address")?
                    .parse()
                    .context("invalid listen address")?;
            }
            "--bootstrap" | "-b" => {
                i += 1;
                let addr_str = args.get(i).context("missing bootstrap address")?;
                let (peer_id, addr) = parse_bootstrap_multiaddr(addr_str)?;
                bootstrap_peers.push((peer_id, addr));
            }
            "--no-default-bootstrap" => {
                use_default_bootstrap = false;
            }
            "--data-dir" | "-d" => {
                i += 1;
                data_dir = PathBuf::from(args.get(i).context("missing data directory")?);
            }
            "--ephemeral" => {
                // Use a temp dir that won't persist — useful for tests
                data_dir = std::env::temp_dir().join(format!("hm-net-{}", std::process::id()));
            }
            "--max-records" => {
                i += 1;
                max_records = args
                    .get(i)
                    .context("missing max-records value")?
                    .parse()
                    .context("invalid max-records value")?;
            }
            "--max-record-size" => {
                i += 1;
                max_record_size = args
                    .get(i)
                    .context("missing max-record-size value")?
                    .parse()
                    .context("invalid max-record-size value")?;
            }
            "--public" => {
                public = true;
            }
            "--health-port" => {
                i += 1;
                health_port = Some(
                    args.get(i)
                        .context("missing health-port value")?
                        .parse()
                        .context("invalid health-port value")?,
                );
            }
            "--no-health" => {
                health_port = None;
            }
            "--headless" => {
                headless = true;
            }
            "--bootstrap-file" => {
                i += 1;
                bootstrap_file = Some(
                    args.get(i)
                        .context("missing bootstrap-file path")?
                        .clone(),
                );
            }
            _ => {}
        }
        i += 1;
    }

    // Load bootstrap peers: explicit --bootstrap args > bootstrap.toml > compiled-in defaults
    if use_default_bootstrap && bootstrap_peers.is_empty() {
        let peer_addrs = if let Some(path) = find_bootstrap_file(
            bootstrap_file.as_deref(),
            &data_dir,
        ) {
            info!(path = %path.display(), "loading bootstrap peers from file");
            load_bootstrap_file(&path).unwrap_or_else(|e| {
                warn!("failed to load bootstrap file: {}", e);
                DEFAULT_BOOTSTRAP_PEERS.iter().map(|s| s.to_string()).collect()
            })
        } else {
            DEFAULT_BOOTSTRAP_PEERS.iter().map(|s| s.to_string()).collect()
        };

        for addr_str in &peer_addrs {
            match parse_bootstrap_multiaddr(addr_str) {
                Ok((peer_id, addr)) => {
                    bootstrap_peers.push((peer_id, addr));
                }
                Err(e) => {
                    warn!("skipping invalid bootstrap peer: {}", e);
                }
            }
        }
    }

    Ok(Args {
        listen_addr,
        bootstrap_peers,
        data_dir,
        max_records,
        max_record_size,
        public,
        health_port,
        headless,
        bootstrap_file,
    })
}

/// Check whether a multiaddr is valid for adding to the routing table.
fn is_valid_addr(addr: &Multiaddr, public_only: bool) -> bool {
    use libp2p::multiaddr::Protocol;

    let mut has_ip = false;
    let mut has_tcp = false;

    for proto in addr.iter() {
        match proto {
            Protocol::Ip4(ip) => {
                has_ip = true;
                if public_only && (ip.is_loopback() || ip.is_private()) {
                    return false;
                }
            }
            Protocol::Ip6(ip) => {
                has_ip = true;
                if public_only && ip.is_loopback() {
                    return false;
                }
            }
            Protocol::Tcp(_) => {
                has_tcp = true;
            }
            _ => {}
        }
    }

    has_ip && has_tcp
}

/// Validate an inbound DHT record before storing.
fn validate_inbound_record(record: &kad::Record, max_record_size: usize) -> bool {
    let key = record.key.as_ref();
    let value = &record.value;

    // Key must be exactly 32 bytes (SHA-256 hash)
    if key.len() != 32 {
        return false;
    }
    // Value must be non-empty
    if value.is_empty() {
        return false;
    }
    // Value must not exceed max record size
    if value.len() > max_record_size {
        return false;
    }
    // First byte must be a valid serialization tag
    let tag = value[0];
    matches!(tag, 0x00..=0x23 | 0x30..=0x32)
}

fn build_behaviour(
    key: &libp2p::identity::Keypair,
    relay_client: relay::client::Behaviour,
    data_dir: PathBuf,
    max_records: usize,
    max_record_size: usize,
) -> std::result::Result<Behaviour, Box<dyn std::error::Error + Send + Sync>> {
    let peer_id = PeerId::from(key.public());
    let store = FileStore::new(data_dir, peer_id)
        .expect("failed to create store")
        .with_limits(max_records, max_record_size);
    let mut kad_config = kad::Config::new(StreamProtocol::new("/hashmath/kad/1.0.0"));
    kad_config.set_record_filtering(kad::StoreInserts::FilterBoth);
    kad_config.set_replication_interval(Some(Duration::from_secs(3600)));
    kad_config.set_publication_interval(Some(Duration::from_secs(86400)));
    kad_config.set_record_ttl(Some(Duration::from_secs(604800)));
    let mut kademlia = kad::Behaviour::with_config(peer_id, store, kad_config);
    kademlia.set_mode(Some(Mode::Server));
    let identify = identify::Behaviour::new(identify::Config::new(
        "/hashmath/id/1.0.0".to_string(),
        key.public(),
    ));
    let autonat = autonat::Behaviour::new(peer_id, Default::default());
    let transfer = transfer::new_behaviour();
    Ok(Behaviour {
        kademlia,
        transfer,
        identify,
        autonat,
        relay_client,
    })
}

async fn run_node<R, W>(mut stdin: R, mut stdout: W, args: Args) -> Result<()>
where
    R: AsyncRead + Unpin,
    W: AsyncWrite + Unpin,
{
    let data_dir = args.data_dir;
    let listen_addr = args.listen_addr;
    let bootstrap_peers = args.bootstrap_peers;
    let max_records = args.max_records;
    let max_record_size = args.max_record_size;
    let public_mode = args.public;
    let health_port = args.health_port;

    // Load or generate persistent keypair
    let local_key = load_or_generate_keypair(&data_dir)?;
    let local_peer_id = PeerId::from(local_key.public());
    info!(%local_peer_id, data_dir = %data_dir.display(), "starting hm-net node");
    eprintln!("PEER_ID={}", local_peer_id);

    // Build swarm
    let mut swarm = SwarmBuilder::with_existing_identity(local_key)
        .with_tokio()
        .with_tcp(
            tcp::Config::default(),
            noise::Config::new,
            yamux::Config::default,
        )?
        .with_relay_client(noise::Config::new, yamux::Config::default)?
        .with_behaviour(|key, relay_client| {
            build_behaviour(key, relay_client, data_dir.clone(), max_records, max_record_size)
        })?
        .with_swarm_config(|cfg| cfg.with_idle_connection_timeout(Duration::from_secs(300)))
        .build();

    // Listen
    swarm
        .listen_on(listen_addr.clone())
        .context("failed to listen")?;
    info!(addr = %listen_addr, "listening");

    // Bootstrap
    for (peer_id, addr) in &bootstrap_peers {
        swarm
            .behaviour_mut()
            .kademlia
            .add_address(peer_id, addr.clone());
        info!(%peer_id, %addr, "added bootstrap peer");
    }
    if !bootstrap_peers.is_empty() {
        swarm.behaviour_mut().kademlia.bootstrap()?;
    }

    // Health status
    let status = Arc::new(NodeStatus::new());

    // Initialize record count from persistent store
    let record_count = swarm
        .behaviour_mut()
        .kademlia
        .store_mut()
        .records()
        .count();
    status.record_count.store(record_count, Ordering::Relaxed);
    if record_count > 0 {
        info!(record_count, "loaded records from persistent store");
    }

    // Start health server
    if let Some(port) = health_port {
        let health_status = status.clone();
        let peer_id_str = local_peer_id.to_string();
        tokio::spawn(health::run_health_server(port, health_status, peer_id_str));
    }

    // Background provider announcement queue
    let (provide_tx, mut provide_rx) = mpsc::channel::<Hash>(PROVIDE_QUEUE_CAPACITY);

    // SIGTERM handler
    #[cfg(unix)]
    let mut sigterm =
        tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;

    // Rate limit timer for provider announcements
    let provide_interval_ms = 1000 / PROVIDE_RATE_PER_SEC;
    let mut provide_ticker = tokio::time::interval(Duration::from_millis(provide_interval_ms));
    provide_ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

    let mut pending = PendingQueries::new();
    loop {
        #[cfg(unix)]
        let sigterm_recv = sigterm.recv();
        #[cfg(not(unix))]
        let sigterm_recv = std::future::pending::<Option<()>>();

        tokio::select! {
            req_result = recv_request(&mut stdin) => {
                match req_result {
                    Ok(req) => {
                        let resp = handle_request(
                            &mut swarm, &mut pending, req, &status, &provide_tx,
                        );
                        match resp {
                            HandleResult::Respond(r) => {
                                send_response(&mut stdout, &r).await?;
                            }
                            HandleResult::Pending => {}
                            HandleResult::Shutdown => {
                                info!("shutdown requested");
                                send_response(&mut stdout, &Response::Pong).await?;
                                return Ok(());
                            }
                        }
                    }
                    Err(e) => {
                        info!("IPC read error (parent likely exited): {}", e);
                        return Ok(());
                    }
                }
            }

            event = swarm.select_next_some() => {
                if let Some(resp) = handle_swarm_event(
                    &mut swarm, &mut pending, event,
                    max_record_size, public_mode, &status,
                ) {
                    send_response(&mut stdout, &resp).await?;
                }
            }

            // Background: drain provider queue at controlled rate
            _ = provide_ticker.tick() => {
                if let Ok(hash) = provide_rx.try_recv() {
                    let key = kad::RecordKey::new(&hash);
                    match swarm.behaviour_mut().kademlia.start_providing(key) {
                        Ok(query_id) => {
                            pending.publishes.insert(query_id, hash);
                        }
                        Err(e) => {
                            info!("start_providing failed: {:?}", e);
                        }
                    }
                }
            }

            _ = sigterm_recv => {
                info!("received SIGTERM, shutting down gracefully");
                break;
            }
        }

        // Update peer count after each loop iteration
        let peer_count = swarm.connected_peers().count();
        status.peer_count.store(peer_count, Ordering::Relaxed);
    }

    Ok(())
}

enum HandleResult {
    Respond(Response),
    Pending,
    Shutdown,
}

fn handle_request(
    swarm: &mut libp2p::Swarm<Behaviour>,
    pending: &mut PendingQueries,
    req: Request,
    status: &Arc<NodeStatus>,
    provide_tx: &mpsc::Sender<Hash>,
) -> HandleResult {
    match req {
        Request::Ping => HandleResult::Respond(Response::Pong),

        Request::Publish { hash, decl_bytes } => {
            publish_one(swarm, status, provide_tx, hash, decl_bytes)
        }

        Request::PublishBatch { records } => {
            let mut count: usize = 0;
            for (hash, decl_bytes) in records {
                let key = kad::RecordKey::new(&hash);
                let record = kad::Record {
                    key,
                    value: decl_bytes,
                    publisher: None,
                    expires: None,
                };
                if swarm
                    .behaviour_mut()
                    .kademlia
                    .store_mut()
                    .put(record)
                    .is_ok()
                {
                    status.record_count.fetch_add(1, Ordering::Relaxed);
                    // Queue provider announcement (best-effort, non-blocking)
                    let _ = provide_tx.try_send(hash);
                    count += 1;
                }
            }
            HandleResult::Respond(Response::BatchPublished { count })
        }

        Request::Fetch { hash } => {
            let key = kad::RecordKey::new(&hash);

            // Check local (disk-backed) store first
            if let Some(record) = swarm.behaviour_mut().kademlia.store_mut().get(&key) {
                return HandleResult::Respond(Response::Found {
                    hash,
                    decl_bytes: record.into_owned().value,
                });
            }

            // Try to find providers via DHT, then fetch directly from them
            let query_id = swarm.behaviour_mut().kademlia.get_providers(key.clone());
            pending.provider_lookups.insert(query_id, hash);

            // Also start a traditional get_record as fallback (for backward compat
            // with nodes that still use put_record)
            let fallback_id = swarm.behaviour_mut().kademlia.get_record(key);
            pending.fetches.insert(fallback_id, hash);

            HandleResult::Pending
        }

        Request::GetPeers => {
            let peers: Vec<String> = swarm.connected_peers().map(|p| p.to_string()).collect();
            HandleResult::Respond(Response::PeerList { peers })
        }

        Request::Shutdown => HandleResult::Shutdown,
    }
}

/// Publish a single record: store locally, queue provider announcement.
fn publish_one(
    swarm: &mut libp2p::Swarm<Behaviour>,
    status: &Arc<NodeStatus>,
    provide_tx: &mpsc::Sender<Hash>,
    hash: Hash,
    decl_bytes: Vec<u8>,
) -> HandleResult {
    let key = kad::RecordKey::new(&hash);
    let record = kad::Record {
        key,
        value: decl_bytes,
        publisher: None,
        expires: None,
    };
    // Store locally (persisted to disk)
    if let Err(e) = swarm
        .behaviour_mut()
        .kademlia
        .store_mut()
        .put(record)
    {
        return HandleResult::Respond(Response::Error {
            msg: format!("local store failed: {:?}", e),
        });
    }
    status.record_count.fetch_add(1, Ordering::Relaxed);
    // Queue provider announcement (rate-limited background task)
    let _ = provide_tx.try_send(hash);
    HandleResult::Respond(Response::Published { hash })
}

fn handle_swarm_event(
    swarm: &mut libp2p::Swarm<Behaviour>,
    pending: &mut PendingQueries,
    event: SwarmEvent<BehaviourEvent>,
    max_record_size: usize,
    public_mode: bool,
    status: &Arc<NodeStatus>,
) -> Option<Response> {
    match event {
        // --- Transfer protocol: serve content directly to requesting peers ---
        SwarmEvent::Behaviour(BehaviourEvent::Transfer(
            request_response::Event::Message {
                message:
                    request_response::Message::Request {
                        request, channel, ..
                    },
                ..
            },
        )) => {
            handle_transfer_request(swarm, request, channel);
            None
        }

        // --- Transfer protocol: received content from a provider ---
        SwarmEvent::Behaviour(BehaviourEvent::Transfer(
            request_response::Event::Message {
                message:
                    request_response::Message::Response {
                        request_id,
                        response,
                    },
                ..
            },
        )) => {
            if let Some(hash) = pending.transfer_requests.remove(&request_id) {
                // Cancel any pending fallback get_record for this hash
                cancel_pending_fetch(pending, &hash);
                match response.data {
                    Some(data) => {
                        // Store locally for future requests
                        let key = kad::RecordKey::new(&hash);
                        let record = kad::Record {
                            key,
                            value: data.clone(),
                            publisher: None,
                            expires: None,
                        };
                        let _ = swarm.behaviour_mut().kademlia.store_mut().put(record);
                        status.record_count.fetch_add(1, Ordering::Relaxed);
                        info!("transfer: received content for hash");
                        Some(Response::Found {
                            hash,
                            decl_bytes: data,
                        })
                    }
                    None => {
                        info!("transfer: provider didn't have content");
                        None // Let fallback get_record continue
                    }
                }
            } else {
                None
            }
        }

        SwarmEvent::Behaviour(BehaviourEvent::Transfer(
            request_response::Event::OutboundFailure {
                request_id, error, ..
            },
        )) => {
            if let Some(hash) = pending.transfer_requests.remove(&request_id) {
                warn!("transfer request failed: {:?}", error);
                // Don't cancel fallback — let get_record try
                let _ = hash;
            }
            None
        }

        // --- Kademlia events ---
        SwarmEvent::Behaviour(BehaviourEvent::Kademlia(kad_event)) => match kad_event {
            // Inbound PUT record validation (FilterBoth mode)
            // Keep for backward compatibility with old nodes
            kad::Event::InboundRequest {
                request: kad::InboundRequest::PutRecord { record, .. },
            } => {
                if let Some(record) = record {
                    if validate_inbound_record(&record, max_record_size) {
                        if let Err(e) = swarm
                            .behaviour_mut()
                            .kademlia
                            .store_mut()
                            .put(record)
                        {
                            warn!("failed to store inbound record: {:?}", e);
                        } else {
                            status.record_count.fetch_add(1, Ordering::Relaxed);
                        }
                    } else {
                        warn!("rejected invalid inbound record");
                    }
                }
                None
            }

            // Provider lookup results: found a peer that has the content
            kad::Event::OutboundQueryProgressed {
                id,
                result: kad::QueryResult::GetProviders(result),
                ..
            } => {
                match result {
                    Ok(kad::GetProvidersOk::FoundProviders { providers, .. }) => {
                        if let Some(hash) = pending.provider_lookups.get(&id) {
                            let hash = *hash;
                            // Request content directly from the first provider
                            for provider in providers {
                                let req_id = swarm
                                    .behaviour_mut()
                                    .transfer
                                    .send_request(&provider, TransferRequest { hash });
                                pending.transfer_requests.insert(req_id, hash);
                                info!(%provider, "requesting content via direct transfer");
                                break; // Try one provider at a time
                            }
                        }
                        None
                    }
                    Ok(kad::GetProvidersOk::FinishedWithNoAdditionalRecord { .. }) => {
                        // Provider lookup done — remove from pending
                        pending.provider_lookups.remove(&id);
                        None
                    }
                    Err(ref e) => {
                        if let Some(_hash) = pending.provider_lookups.remove(&id) {
                            warn!("get_providers failed: {:?}", e);
                        }
                        None
                    }
                }
            }

            // Fallback: traditional get_record results (backward compat)
            kad::Event::OutboundQueryProgressed {
                id,
                result: kad::QueryResult::GetRecord(result),
                ..
            } => match result {
                Ok(kad::GetRecordOk::FoundRecord(peer_record)) => {
                    if let Some(hash) = pending.fetches.remove(&id) {
                        // Check we haven't already resolved this via transfer
                        if !is_hash_resolved(pending, &hash) {
                            info!("GET_RECORD found record (fallback)");
                            // Store locally
                            let key = kad::RecordKey::new(&hash);
                            let record = kad::Record {
                                key,
                                value: peer_record.record.value.clone(),
                                publisher: None,
                                expires: None,
                            };
                            let _ = swarm.behaviour_mut().kademlia.store_mut().put(record);
                            status.record_count.fetch_add(1, Ordering::Relaxed);
                            Some(Response::Found {
                                hash,
                                decl_bytes: peer_record.record.value,
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                Ok(kad::GetRecordOk::FinishedWithNoAdditionalRecord { .. }) => {
                    if let Some(hash) = pending.fetches.remove(&id) {
                        // Only return NotFound if no transfer is pending either
                        if !has_pending_transfer(pending, &hash) {
                            info!("GET_RECORD finished with no record");
                            Some(Response::NotFound { hash })
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                Err(ref e) => {
                    if let Some(hash) = pending.fetches.remove(&id) {
                        if !has_pending_transfer(pending, &hash) {
                            warn!("GET_RECORD error: {:?}", e);
                            Some(Response::NotFound { hash })
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            },
            kad::Event::OutboundQueryProgressed {
                id,
                result: kad::QueryResult::PutRecord(result),
                ..
            } => {
                if let Some(_hash) = pending.publishes.remove(&id) {
                    if let Err(e) = result {
                        warn!("DHT put failed: {:?}", e);
                    }
                }
                None
            }
            kad::Event::OutboundQueryProgressed {
                id,
                result: kad::QueryResult::StartProviding(result),
                ..
            } => {
                if let Some(_hash) = pending.publishes.remove(&id) {
                    match result {
                        Ok(_) => info!("start_providing succeeded"),
                        Err(e) => warn!("start_providing failed: {:?}", e),
                    }
                }
                None
            }
            kad::Event::RoutingUpdated { peer, .. } => {
                info!(%peer, "routing table updated");
                None
            }
            _ => None,
        },

        SwarmEvent::Behaviour(BehaviourEvent::Identify(identify::Event::Received {
            peer_id,
            info: identify_info,
            ..
        })) => {
            let mut added = 0;
            for addr in identify_info.listen_addrs {
                if added >= MAX_ADDRS_PER_PEER {
                    warn!(
                        %peer_id,
                        "dropped addresses beyond limit of {}",
                        MAX_ADDRS_PER_PEER
                    );
                    break;
                }
                if is_valid_addr(&addr, public_mode) {
                    swarm
                        .behaviour_mut()
                        .kademlia
                        .add_address(&peer_id, addr);
                    added += 1;
                }
            }
            None
        }

        SwarmEvent::Behaviour(BehaviourEvent::Autonat(autonat::Event::StatusChanged {
            new: new_status,
            ..
        })) => {
            info!(?new_status, "NAT status changed");
            None
        }

        SwarmEvent::NewListenAddr { address, .. } => {
            info!(%address, "new listen address");
            status.ready.store(true, Ordering::Relaxed);
            None
        }

        _ => None,
    }
}

/// Handle an incoming transfer request: serve content from local store.
fn handle_transfer_request(
    swarm: &mut libp2p::Swarm<Behaviour>,
    request: TransferRequest,
    channel: ResponseChannel<TransferResponse>,
) {
    let key = kad::RecordKey::new(&request.hash);
    let response = match swarm.behaviour_mut().kademlia.store_mut().get(&key) {
        Some(record) => TransferResponse {
            data: Some(record.into_owned().value),
        },
        None => TransferResponse { data: None },
    };
    if swarm
        .behaviour_mut()
        .transfer
        .send_response(channel, response)
        .is_err()
    {
        warn!("failed to send transfer response (channel closed)");
    }
}

/// Check if a hash still has a pending transfer request.
fn has_pending_transfer(pending: &PendingQueries, hash: &Hash) -> bool {
    pending
        .transfer_requests
        .values()
        .any(|h| h == hash)
}

/// Check if a hash has already been resolved (no longer in any pending map).
fn is_hash_resolved(pending: &PendingQueries, hash: &Hash) -> bool {
    // If we already sent an IPC response for this hash via transfer,
    // the transfer_requests entry will have been removed
    !pending.transfer_requests.values().any(|h| h == hash)
        && !pending.fetches.values().any(|h| h == hash)
}

/// Cancel pending fallback fetch for a hash (already resolved via transfer).
fn cancel_pending_fetch(pending: &mut PendingQueries, hash: &Hash) {
    pending.fetches.retain(|_, h| h != hash);
    pending.provider_lookups.retain(|_, h| h != hash);
}

/// Run a headless DHT node (no IPC). Used for standalone seed nodes.
async fn run_node_headless(args: Args) -> Result<()> {
    let data_dir = args.data_dir;
    let listen_addr = args.listen_addr;
    let bootstrap_peers = args.bootstrap_peers;
    let max_records = args.max_records;
    let max_record_size = args.max_record_size;
    let public_mode = args.public;
    let health_port = args.health_port;

    let local_key = load_or_generate_keypair(&data_dir)?;
    let local_peer_id = PeerId::from(local_key.public());
    info!(%local_peer_id, data_dir = %data_dir.display(), "starting headless hm-net node");
    eprintln!("PEER_ID={}", local_peer_id);

    let mut swarm = SwarmBuilder::with_existing_identity(local_key)
        .with_tokio()
        .with_tcp(
            tcp::Config::default(),
            noise::Config::new,
            yamux::Config::default,
        )?
        .with_relay_client(noise::Config::new, yamux::Config::default)?
        .with_behaviour(|key, relay_client| {
            build_behaviour(key, relay_client, data_dir.clone(), max_records, max_record_size)
        })?
        .with_swarm_config(|cfg| cfg.with_idle_connection_timeout(Duration::from_secs(300)))
        .build();

    swarm
        .listen_on(listen_addr.clone())
        .context("failed to listen")?;
    info!(addr = %listen_addr, "listening");

    for (peer_id, addr) in &bootstrap_peers {
        swarm
            .behaviour_mut()
            .kademlia
            .add_address(peer_id, addr.clone());
        info!(%peer_id, %addr, "added bootstrap peer");
    }
    if !bootstrap_peers.is_empty() {
        swarm.behaviour_mut().kademlia.bootstrap()?;
    }

    let status = Arc::new(NodeStatus::new());

    let record_count = swarm
        .behaviour_mut()
        .kademlia
        .store_mut()
        .records()
        .count();
    status.record_count.store(record_count, Ordering::Relaxed);
    if record_count > 0 {
        info!(record_count, "loaded records from persistent store");
    }

    if let Some(port) = health_port {
        let health_status = status.clone();
        let peer_id_str = local_peer_id.to_string();
        tokio::spawn(health::run_health_server(port, health_status, peer_id_str));
    }

    #[cfg(unix)]
    let mut sigterm =
        tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;

    loop {
        #[cfg(unix)]
        let sigterm_recv = sigterm.recv();
        #[cfg(not(unix))]
        let sigterm_recv = std::future::pending::<Option<()>>();

        tokio::select! {
            event = swarm.select_next_some() => {
                handle_swarm_event(
                    &mut swarm, &mut PendingQueries::new(), event,
                    max_record_size, public_mode, &status,
                );
            }
            _ = sigterm_recv => {
                info!("received SIGTERM, shutting down gracefully");
                break;
            }
        }

        let peer_count = swarm.connected_peers().count();
        status.peer_count.store(peer_count, Ordering::Relaxed);
    }

    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with_writer(std::io::stderr)
        .init();

    let args = parse_args()?;

    if args.headless {
        run_node_headless(args).await
    } else {
        let stdin = io::stdin();
        let stdout = io::stdout();
        run_node(stdin, stdout, args).await
    }
}
