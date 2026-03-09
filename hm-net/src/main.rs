//! hm-net: Rust sidecar for HashMath distributed hash table.
//!
//! Communicates with the Lean `hm` process via stdin/stdout IPC.
//! Runs a libp2p Kademlia DHT node to store/retrieve content-addressed declarations.

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
use tokio::io::{self, AsyncRead, AsyncWrite};
use tracing::{info, warn};

use crate::ipc::{recv_request, send_response, Hash, Request, Response};
use crate::store::{load_or_generate_keypair, FileStore};

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
}

fn default_data_dir() -> PathBuf {
    dirs::data_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("hm-net")
}

fn parse_args() -> Result<Args> {
    let mut listen_addr: Multiaddr = "/ip4/0.0.0.0/tcp/4256".parse()?;
    let mut bootstrap_peers = Vec::new();
    let mut data_dir = default_data_dir();

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
                let addr: Multiaddr = addr_str.parse().context("invalid bootstrap address")?;
                if let Some(libp2p::multiaddr::Protocol::P2p(peer_id)) = addr.iter().last() {
                    let addr_without_p2p: Multiaddr = addr
                        .iter()
                        .filter(|p| !matches!(p, libp2p::multiaddr::Protocol::P2p(_)))
                        .collect();
                    bootstrap_peers.push((peer_id, addr_without_p2p));
                } else {
                    anyhow::bail!(
                        "bootstrap address must end with /p2p/<peer-id>: {}",
                        addr_str
                    );
                }
            }
            "--data-dir" | "-d" => {
                i += 1;
                data_dir = PathBuf::from(
                    args.get(i).context("missing data directory")?,
                );
            }
            "--ephemeral" => {
                // Use a temp dir that won't persist — useful for tests
                data_dir = std::env::temp_dir().join(format!("hm-net-{}", std::process::id()));
            }
            _ => {}
        }
        i += 1;
    }

    Ok(Args {
        listen_addr,
        bootstrap_peers,
        data_dir,
    })
}

async fn run_node<R, W>(mut stdin: R, mut stdout: W, args: Args) -> Result<()>
where
    R: AsyncRead + Unpin,
    W: AsyncWrite + Unpin,
{
    // Load or generate persistent keypair
    let local_key = load_or_generate_keypair(&args.data_dir)?;
    let local_peer_id = PeerId::from(local_key.public());
    info!(%local_peer_id, data_dir = %args.data_dir.display(), "starting hm-net node");
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
            let store =
                FileStore::new(args.data_dir.clone(), peer_id).expect("failed to create store");
            let kad_config = kad::Config::new(StreamProtocol::new("/hashmath/kad/1.0.0"));
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
        .with_swarm_config(|cfg| {
            cfg.with_idle_connection_timeout(std::time::Duration::from_secs(300))
        })
        .build();

    // Listen
    swarm
        .listen_on(args.listen_addr.clone())
        .context("failed to listen")?;
    info!(addr = %args.listen_addr, "listening");

    // Bootstrap
    for (peer_id, addr) in &args.bootstrap_peers {
        swarm
            .behaviour_mut()
            .kademlia
            .add_address(peer_id, addr.clone());
        info!(%peer_id, %addr, "added bootstrap peer");
    }
    if !args.bootstrap_peers.is_empty() {
        swarm.behaviour_mut().kademlia.bootstrap()?;
    }

    // Log record count from persistent store
    let record_count = swarm.behaviour_mut().kademlia.store_mut().records().count();
    if record_count > 0 {
        info!(record_count, "loaded records from persistent store");
    }

    let mut pending = PendingQueries::new();

    loop {
        tokio::select! {
            req_result = recv_request(&mut stdin) => {
                match req_result {
                    Ok(req) => {
                        let resp = handle_request(&mut swarm, &mut pending, req);
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
                if let Some(resp) = handle_swarm_event(&mut swarm, &mut pending, event) {
                    send_response(&mut stdout, &resp).await?;
                }
            }
        }
    }
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
) -> Option<Response> {
    match event {
        SwarmEvent::Behaviour(BehaviourEvent::Kademlia(kad_event)) => match kad_event {
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
            for addr in identify_info.listen_addrs {
                swarm
                    .behaviour_mut()
                    .kademlia
                    .add_address(&peer_id, addr);
            }
            None
        }

        SwarmEvent::Behaviour(BehaviourEvent::Autonat(autonat::Event::StatusChanged {
            new: status,
            ..
        })) => {
            info!(?status, "NAT status changed");
            None
        }

        SwarmEvent::NewListenAddr { address, .. } => {
            info!(%address, "new listen address");
            None
        }

        _ => None,
    }
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
    let stdin = io::stdin();
    let stdout = io::stdout();

    run_node(stdin, stdout, args).await
}
