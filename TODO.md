# HashMath Distributed Hash Table — TODO

## Architecture
- Rust sidecar process handles all networking (Kademlia DHT via libp2p)
- Lean `hm` process communicates with sidecar via stdin/stdout pipes
- Lean handles all typechecking/verification; Rust handles discovery & transport
- Project layout: `lean/` (Lean project), `hm-net/` (Rust sidecar), `whitepaper/` (LaTeX)

## Phase 1: IPC Protocol (Lean <-> Rust) — DONE
- [x] Define IPC message types in Lean (`lean/HashMath/Net/IPC.lean`)
- [x] Implement IPC serialization in Lean (length-prefixed binary over stdin/stdout)
- [x] Scaffold Rust sidecar project (`hm-net/`) with `cargo init`
- [x] Implement IPC deserialization in Rust (mirror the Lean format)
- [x] Basic IPC integration test (`hm --test-ipc`)

## Phase 2: Rust Sidecar with libp2p Kademlia — DONE
- [x] Add libp2p dependencies (libp2p, tokio)
- [x] Implement Kademlia DHT node (bootstrap, routing table, peer discovery)
- [x] STORE: accept declaration bytes from Lean, publish to DHT
- [x] FIND_VALUE: look up hash in DHT, return declaration bytes to Lean
- [x] Peer management (connect to bootstrap nodes, maintain routing table)
- [x] Configurable listen address and bootstrap peers (CLI flags)

## Phase 3: Lean CLI Integration — DONE
- [x] `hm serve` — spawn Rust sidecar, keep running as DHT node
- [x] `hm publish <file.hm>` — typecheck file, send all decl hashes to sidecar
- [x] `hm fetch <hash>` — fetch with recursive dependency resolution + re-typecheck
- [x] `hm peers` — query sidecar for connected peer info
- [x] Lean-side client wrapper (`lean/HashMath/Net/Client.lean`)
- [x] Deserialization (`deserializeDecl` in Serialize.lean) + hash verification
- [x] Dependency resolution (`fetchWithDeps` — recursive fetch + typecheck)

## Phase 4: Manifest Files & Bulk Sync — DONE
- [x] `.hmm` manifest format: one `name hexhash` per line
- [x] `hm manifest --generate <file.hm> [...]` — generate manifest to stdout
- [x] `hm publish --manifest lib.hmm` — check all manifest entries exist in DHT
- [x] `hm fetch --manifest lib.hmm` — fetch and verify an entire library

## Phase 5: Hardening & Testing
- [x] Graceful shutdown (Shutdown IPC message → sidecar exits, Lean waits)
- [ ] Connection limits and rate limiting
- [x] Persistent storage for sidecar (file-backed RecordStore + persistent keypair)
- [x] NAT traversal (libp2p AutoNAT + Relay client)
- [x] Logging (tracing to stderr, configurable via RUST_LOG)
- [x] Integration test: multi-node DHT propagation (`test-dht.sh`)
- [x] Documentation (README, MANUAL.md, whitepaper networking section)
