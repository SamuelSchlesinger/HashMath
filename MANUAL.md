# HashMath User Manual

## Installation

HashMath has two components: the Lean CLI (`hm`) and the Rust networking
sidecar (`hm-net`).

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0+)
- [Rust](https://rustup.rs/) (stable toolchain)

### Build and install

```sh
make && make install
```

This builds both components and copies the binaries to `~/.local/bin/`.
Make sure `~/.local/bin` is on your `PATH`:

```sh
# Add to your shell profile (~/.zshrc, ~/.bashrc, etc.) if not already present
export PATH="$HOME/.local/bin:$PATH"
```

To install elsewhere, set `PREFIX`:

```sh
make install PREFIX=/usr/local    # installs to /usr/local/bin
```

### Building without installing

```sh
make          # or: make build
```

The binaries are at `lean/.lake/build/bin/hm` and `hm-net/target/release/hm-net`.

### Uninstall

```sh
make uninstall
```

## Getting started

### REPL mode

Run `hm` with no arguments to enter the interactive REPL:

```
$ hm
HashMath v0.1.0 — Content-addressed proof assistant
Type :help for commands, :q to quit.
hm> axiom A : Type
✓ A
hm> axiom f : A → A
✓ f
hm> #check f
  : A → A
hm> :q
```

### Processing files

Write declarations in `.hm` files and process them:

```
$ cat basics.hm
axiom Nat : Type
axiom zero : Nat
axiom succ : Nat → Nat

$ hm basics.hm
✓ Nat
✓ zero
✓ succ
Processed 1 file(s) successfully.
```

### REPL commands

| Command | Description |
|---------|-------------|
| `axiom <name> : <type>` | Declare an axiom |
| `def <name> : <type> := <value>` | Define a term |
| `inductive <name> : <type> where \| ctor : type ...` | Define an inductive type |
| `#check <expr>` | Infer and display the type of an expression |
| `#eval <expr>` | Normalize an expression |
| `#print <name>` | Show information about a declaration |
| `:env` | List all names in the environment |
| `:help` | Show help |
| `:q` | Quit |

## Networking

HashMath uses a peer-to-peer network to share content-addressed declarations
across machines. The architecture separates **discovery** from **transfer**
(like BitTorrent/IPFS):

- **`hm-net`** — A Rust sidecar running a libp2p node with Kademlia (provider
  discovery) and a direct transfer protocol (content serving)
- **`hm`** — The Lean CLI, which spawns and communicates with `hm-net` via IPC

The DHT stores only lightweight provider records (~40 bytes) announcing which
peers have which hashes. Actual content is transferred directly between peers
via the `/hashmath/transfer/1.0.0` request-response protocol.

### Configuration

After `make install`, both `hm` and `hm-net` are on your PATH and no extra
configuration is needed. If you need to use a different sidecar binary
(e.g., a debug build), set the `HM_NET_PATH` environment variable:

```sh
export HM_NET_PATH=/path/to/hm-net
```

### Starting a node

```sh
# Start a DHT node with an interactive REPL
hm serve

# Listen on a specific address
hm serve --listen /ip4/0.0.0.0/tcp/4256
```

The sidecar starts automatically, listens for peer connections, and shuts down
when you exit the REPL.

### Publishing declarations

Publish all declarations from one or more `.hm` files to the network:

```sh
hm publish basics.hm logic.hm
```

This type-checks each file, then:
1. **Shatters** each declaration into subterm fragments — large subterms
   (>33 bytes serialized) are replaced by hash references (`href` nodes).
2. **Batch-publishes** all fragments to the sidecar in a single IPC call.
   The sidecar stores them locally to disk and returns immediately.
3. In the background, the sidecar announces provider records to the DHT
   at a rate-limited 20/sec, so the network learns which peer has which hashes.

Publishing is fast because no DHT round-trips block the user — content is
stored locally and provider announcements happen asynchronously.

### Fetching declarations

Fetch a declaration by its 64-character hex hash:

```sh
hm fetch 5a1fc2...deadbeef
```

The sidecar first checks its local store. If the content isn't local, it
discovers providers via the DHT (`GET_PROVIDERS`) and transfers the content
directly from a provider peer. It then recursively resolves all dependencies
(including subterm fragments referenced by `href` nodes), reassembles full
expressions, verifies each hash, type-checks each declaration, and reports
the results. A fallback `GET_RECORD` path provides backward compatibility
with older nodes that stored full records in the DHT.

### Checking peers

```sh
hm peers
```

Shows all currently connected DHT peers.

### Manifest files

Manifest files (`.hmm`) list declarations by name and hash for bulk
operations:

```sh
# Generate a manifest from source files
hm manifest --generate basics.hm logic.hm > lib.hmm

# Check that all manifest entries are available in the DHT
hm publish --manifest lib.hmm

# Fetch and verify an entire library from the DHT
hm fetch --manifest lib.hmm
```

A manifest file contains one entry per line in the format `name hexhash`:

```
Nat 5a1fc2...
zero 8b3de7...
succ a912f0...
```

## Sidecar options

The `hm-net` binary accepts the following flags:

| Flag | Description |
|------|-------------|
| `--listen <multiaddr>` | Listen address (default: `/ip4/127.0.0.1/tcp/4256`) |
| `--bootstrap <multiaddr/p2p/peerid>` | Bootstrap peer (repeatable) |
| `--bootstrap-file <path>` | Path to a `bootstrap.toml` file |
| `--no-default-bootstrap` | Disable compiled-in and file-based bootstrap peers |
| `--data-dir <path>` | Data directory for records and keypair |
| `--ephemeral` | Use a temporary data directory (for testing) |
| `--public` | Filter to only use public (non-private) addresses |
| `--headless` | Run without IPC (for seed nodes) |
| `--no-health` | Disable the HTTP health endpoint |
| `--health-port <port>` | Health endpoint port (default: 4257) |
| `--max-records <n>` | Maximum DHT records to store (default: 10000) |
| `--max-record-size <n>` | Maximum size per record in bytes (default: 1048576) |

### Bootstrap configuration

Bootstrap peers are loaded from (in priority order):
1. `--bootstrap` CLI flags
2. `--bootstrap-file` path (or auto-discovered `bootstrap.toml`)
3. Compiled-in fallback peers

The `bootstrap.toml` file is searched at: explicit path > data directory >
next to the binary. Use `--no-default-bootstrap` for isolated testing.

### Data persistence

By default, `hm-net` stores data in the platform data directory:

| Platform | Default path |
|----------|-------------|
| macOS | `~/Library/Application Support/hm-net/` |
| Linux | `~/.local/share/hm-net/` |

The data directory contains:

- `keypair` — Ed25519 identity (stable PeerId across restarts)
- `records/` — DHT records stored as individual files

### Connecting nodes

To connect two nodes, start one and note its peer ID (printed to stderr),
then start the second with a `--bootstrap` flag:

```sh
# Terminal 1: start node A
hm-net --listen /ip4/0.0.0.0/tcp/4256
# Prints: PEER_ID=12D3KooW...

# Terminal 2: start node B, bootstrapped from A
hm-net --listen /ip4/0.0.0.0/tcp/4257 \
  --bootstrap /ip4/127.0.0.1/tcp/4256/p2p/12D3KooW...
```

### Logging

`hm-net` logs to stderr using the `RUST_LOG` environment variable:

```sh
RUST_LOG=debug hm-net
```

## Running tests

```sh
make test       # type-checker tests (examples/ pass, wrong/ rejected)
make test-dht   # DHT integration test (IPC + two-node propagation)
```

## IPC protocol

The IPC protocol uses length-prefixed binary frames over stdin/stdout:

```
[4-byte big-endian length] [tag byte] [payload...]
```

### Request tags (Lean -> Rust)

| Tag | Name | Payload |
|-----|------|---------|
| `0x50` | Ping | (none) |
| `0x51` | Publish | 32-byte hash + LEB128-length-prefixed data |
| `0x52` | Fetch | 32-byte hash |
| `0x53` | GetPeers | (none) |
| `0x54` | Shutdown | (none) |
| `0x55` | PublishBatch | LEB128 count + count × (32-byte hash + LEB128-length-prefixed data) |

### Response tags (Rust -> Lean)

| Tag | Name | Payload |
|-----|------|---------|
| `0x60` | Pong | (none) |
| `0x61` | Published | 32-byte hash |
| `0x62` | Found | 32-byte hash + LEB128-length-prefixed data |
| `0x63` | NotFound | 32-byte hash |
| `0x64` | PeerList | LEB128 count + LEB128-prefixed strings |
| `0x65` | Error | LEB128-prefixed error message |
| `0x66` | BatchPublished | LEB128 count |
