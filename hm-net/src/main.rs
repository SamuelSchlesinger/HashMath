//! hm-net: Rust sidecar for HashMath distributed hash table.
//!
//! Communicates with the Lean `hm` process via stdin/stdout IPC.
//! Runs a libp2p Kademlia DHT node to store/retrieve content-addressed declarations.

mod health;
mod ipc;
mod store;

use anyhow::{Context, Result};
use libp2p::{
    autonat,
    futures::StreamExt,
    identify,
    kad::{self, store::RecordStore, Mode},
    noise, relay,
    swarm::{NetworkBehaviour, SwarmEvent},
    tcp, yamux, Multiaddr, PeerId, StreamProtocol, SwarmBuilder,
};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;
use tokio::io::{self, AsyncRead, AsyncWrite};
use tracing::{info, warn};

use crate::health::NodeStatus;
use crate::ipc::{recv_request, send_response, Hash, Request, Response};
use crate::store::{load_or_generate_keypair, FileStore};

/// Maximum number of addresses to accept per peer from Identify.
const MAX_ADDRS_PER_PEER: usize = 20;

/// Default bootstrap peers for the HashMath network.
///
/// These are well-known seed nodes that new nodes connect to automatically.
/// Override with `--bootstrap` or disable with `--no-default-bootstrap`.
/// To add a seed node, append its full multiaddr here:
///   "/ip4/<IP>/tcp/4256/p2p/<PeerId>"
const DEFAULT_BOOTSTRAP_PEERS: &[&str] = &[
    "/ip4/35.207.40.117/tcp/4256/p2p/12D3KooWHKxXAuWMwZik7CcuteTjfAXL8VWehnM4w1B7DYgnCv1v",
];

/// Combined libp2p behaviour: Kademlia + Identify + AutoNAT + Relay client.
#[derive(NetworkBehaviour)]
struct Behaviour {
    kademlia: kad::Behaviour<FileStore>,
    identify: identify::Behaviour,
    autonat: autonat::Behaviour,
    relay_client: relay::client::Behaviour,
}

/// Pending Kademlia queries awaiting IPC responses.
struct PendingQueries {
    fetches: HashMap<kad::QueryId, Hash>,
    publishes: HashMap<kad::QueryId, Hash>,
}

impl PendingQueries {
    fn new() -> Self {
        Self {
            fetches: HashMap::new(),
            publishes: HashMap::new(),
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
            _ => {}
        }
        i += 1;
    }

    // Add default bootstrap peers unless disabled or explicit peers were given
    if use_default_bootstrap && bootstrap_peers.is_empty() {
        for addr_str in DEFAULT_BOOTSTRAP_PEERS {
            match parse_bootstrap_multiaddr(addr_str) {
                Ok((peer_id, addr)) => {
                    bootstrap_peers.push((peer_id, addr));
                }
                Err(e) => {
                    warn!("skipping invalid default bootstrap peer: {}", e);
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
            let peer_id = PeerId::from(key.public());
            let store = FileStore::new(data_dir.clone(), peer_id)
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
            Ok(Behaviour {
                kademlia,
                identify,
                autonat,
                relay_client,
            })
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

    // SIGTERM handler
    #[cfg(unix)]
    let mut sigterm =
        tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;

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
                        let resp = handle_request(&mut swarm, &mut pending, req, &status);
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
) -> HandleResult {
    match req {
        Request::Ping => HandleResult::Respond(Response::Pong),

        Request::Publish { hash, decl_bytes } => {
            let key = kad::RecordKey::new(&hash);
            let record = kad::Record {
                key: key.clone(),
                value: decl_bytes,
                publisher: None,
                expires: None,
            };
            // Store locally (persisted to disk)
            if let Err(e) = swarm
                .behaviour_mut()
                .kademlia
                .store_mut()
                .put(record.clone())
            {
                return HandleResult::Respond(Response::Error {
                    msg: format!("local store failed: {:?}", e),
                });
            }
            status.record_count.fetch_add(1, Ordering::Relaxed);
            // Best-effort DHT replication
            match swarm
                .behaviour_mut()
                .kademlia
                .put_record(record, kad::Quorum::One)
            {
                Ok(query_id) => {
                    pending.publishes.insert(query_id, hash);
                }
                Err(_) => {
                    info!("DHT replication skipped (no peers?), stored locally");
                }
            }
            HandleResult::Respond(Response::Published { hash })
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

            // Query the DHT
            let query_id = swarm.behaviour_mut().kademlia.get_record(key);
            pending.fetches.insert(query_id, hash);
            HandleResult::Pending
        }

        Request::GetPeers => {
            let peers: Vec<String> = swarm.connected_peers().map(|p| p.to_string()).collect();
            HandleResult::Respond(Response::PeerList { peers })
        }

        Request::Shutdown => HandleResult::Shutdown,
    }
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
        SwarmEvent::Behaviour(BehaviourEvent::Kademlia(kad_event)) => match kad_event {
            // Inbound PUT record validation (FilterBoth mode)
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

            kad::Event::OutboundQueryProgressed {
                id,
                result: kad::QueryResult::GetRecord(result),
                ..
            } => match result {
                Ok(kad::GetRecordOk::FoundRecord(peer_record)) => {
                    if let Some(hash) = pending.fetches.remove(&id) {
                        info!("GET_RECORD found record for query {:?}", id);
                        Some(Response::Found {
                            hash,
                            decl_bytes: peer_record.record.value,
                        })
                    } else {
                        None
                    }
                }
                Ok(kad::GetRecordOk::FinishedWithNoAdditionalRecord { .. }) => {
                    if let Some(hash) = pending.fetches.remove(&id) {
                        info!("GET_RECORD finished with no record for query {:?}", id);
                        Some(Response::NotFound { hash })
                    } else {
                        None
                    }
                }
                Err(ref e) => {
                    if let Some(hash) = pending.fetches.remove(&id) {
                        warn!("GET_RECORD error for query {:?}: {:?}", id, e);
                        Some(Response::NotFound { hash })
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
            let peer_id = PeerId::from(key.public());
            let store = FileStore::new(data_dir.clone(), peer_id)
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
            Ok(Behaviour {
                kademlia,
                identify,
                autonat,
                relay_client,
            })
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
