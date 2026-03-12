/-
  HashMath.Net.Client — Lean-side client for communicating with the hm-net sidecar.

  Spawns the Rust sidecar process and provides high-level operations
  (publish, fetch, peers) over the IPC protocol.
-/

import HashMath.Net.IPC

namespace HashMath.Net

/-- A handle to the running hm-net sidecar process. -/
structure SidecarHandle where
  process : IO.Process.Child ⟨.piped, .piped, .inherit⟩
  -- stdin of child = our write end; stdout of child = our read end

namespace SidecarHandle

/-- Spawn the hm-net sidecar process.
    `hmNetPath` is the path to the hm-net binary.
    `args` are additional CLI arguments (e.g., --listen, --bootstrap). -/
def spawn (hmNetPath : String) (args : Array String := #[]) : IO SidecarHandle := do
  let child ← IO.Process.spawn {
    cmd := hmNetPath
    args := args
    stdin := .piped
    stdout := .piped
    stderr := .inherit  -- sidecar logs go to terminal
  }
  return ⟨child⟩

/-- Send a request and receive a response. -/
def request (h : SidecarHandle) (req : Request) : IO Response := do
  let stdinStream := IO.FS.Stream.ofHandle h.process.stdin
  let stdoutStream := IO.FS.Stream.ofHandle h.process.stdout
  sendRequest stdinStream req
  recvResponse stdoutStream

/-- Ping the sidecar. Returns true if it responds with Pong. -/
def ping (h : SidecarHandle) : IO Bool := do
  let resp ← h.request .ping
  match resp with
  | .pong => return true
  | _ => return false

/-- Publish a declaration (hash + serialized bytes) to the DHT. -/
def publish (h : SidecarHandle) (hash : Hash) (declBytes : ByteArray) : IO Response :=
  h.request (.publish hash declBytes)

/-- Publish a batch of records in a single IPC call.
    Returns the number of records successfully stored. -/
def publishBatch (h : SidecarHandle) (records : Array (Hash × ByteArray)) : IO Nat := do
  let resp ← h.request (.publishBatch records)
  match resp with
  | .batchPublished count => return count
  | .error msg => throw (IO.Error.userError s!"batch publish failed: {msg}")
  | _ => throw (IO.Error.userError "unexpected response to publishBatch")

/-- Fetch a declaration by hash from the DHT. -/
def fetch (h : SidecarHandle) (hash : Hash) : IO Response :=
  h.request (.fetch hash)

/-- Get the list of connected peers. -/
def getPeers (h : SidecarHandle) : IO (List String) := do
  let resp ← h.request .getPeers
  match resp with
  | .peerList peers => return peers
  | _ => return []

/-- Gracefully shut down the sidecar. -/
def shutdown (h : SidecarHandle) : IO Unit := do
  let _ ← h.request .shutdown
  let _ ← h.process.wait
  return ()

end SidecarHandle

end HashMath.Net
