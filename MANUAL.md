# HashMath User Manual

## Building

HashMath has two components: the Lean CLI (`hm`) and the Rust networking
sidecar (`hm-net`).

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.28.0+)
- [Rust](https://rustup.rs/) (stable toolchain)

### Build

```sh
# Build the Lean CLI
cd lean && lake build hm

# Build the Rust sidecar
cd hm-net && cargo build --release
```

The `hm` binary is at `lean/.lake/build/bin/hm`.
The `hm-net` binary is at `hm-net/target/release/hm-net`.

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

HashMath uses a distributed hash table (DHT) to share content-addressed
declarations across machines. The networking layer consists of:

- **`hm-net`** — A Rust sidecar process running a libp2p Kademlia DHT node
- **`hm`** — The Lean CLI, which spawns and communicates with `hm-net` via IPC

### Configuration

Tell `hm` where to find the sidecar binary:

```sh
# Option 1: environment variable
export HM_NET_PATH=/path/to/hm-net

# Option 2: place hm-net on your PATH
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

Publish all declarations from one or more `.hm` files to the DHT:

```sh
hm publish basics.hm logic.hm
```

This type-checks each file, then for each declaration:
1. **Shatters** the declaration into subterm fragments — large subterms
   (>33 bytes serialized) are replaced by hash references (`href` nodes)
   and stored as separate DHT entries.
2. **Publishes** each subterm entry to the DHT.
3. **Publishes** the top-level declaration (now containing `href` pointers
   instead of repeated subterms) to the DHT.

The result is global subterm deduplication: shared subterms across all
declarations in the network are stored exactly once.

### Fetching declarations

Fetch a declaration by its 64-character hex hash:

```sh
hm fetch 5a1fc2...deadbeef
```

This recursively resolves all dependencies (including subterm fragments
referenced by `href` nodes), downloads them from the DHT, reassembles
full expressions, verifies each hash, type-checks each declaration, and
reports the results. The format is backward-compatible: declarations
published before subterm hash-consing was added are fetched correctly.

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
| `--listen <multiaddr>` | Listen address (default: `/ip4/0.0.0.0/tcp/4256`) |
| `--bootstrap <multiaddr/p2p/peerid>` | Bootstrap peer (repeatable) |
| `--data-dir <path>` | Data directory for records and keypair |
| `--ephemeral` | Use a temporary data directory (for testing) |

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
# Lean type-checker tests (47 tests)
cd lean && bash test.sh

# DHT integration test (IPC + two-node propagation)
bash test-dht.sh
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

### Response tags (Rust -> Lean)

| Tag | Name | Payload |
|-----|------|---------|
| `0x60` | Pong | (none) |
| `0x61` | Published | 32-byte hash |
| `0x62` | Found | 32-byte hash + LEB128-length-prefixed data |
| `0x63` | NotFound | 32-byte hash |
| `0x64` | PeerList | LEB128 count + LEB128-prefixed strings |
| `0x65` | Error | LEB128-prefixed error message |
