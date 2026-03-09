/-
  HashMath CLI — Command-line interface for the HashMath proof assistant
-/

import HashMath.Elab
import HashMath.Subterm
import HashMath.Net.Client

open HashMath
open HashMath.Net

/-- Format an ElabResult for display. -/
def formatResult (cb : Codebase) : ElabResult → String
  | .declared name _h => s!"✓ {name}"
  | .checked _e ty => s!"  : {cb.ppExpr [] [] ty}"
  | .evaluated _e result => s!"  = {cb.ppExpr [] [] result}"
  | .printed name info => s!"{name} : {info}"

/-- Run a REPL session. -/
partial def repl (cb : Codebase) : IO Unit := do
  IO.print "hm> "
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAsciiEnd.toString
  if line == ":q" || line == ":quit" then return
  if line == ":env" then
    for (name, _) in cb.names.toList do
      IO.println s!"  {name}"
    repl cb
    return
  if line == ":help" then
    IO.println "Commands:"
    IO.println "  axiom <name> : <type>"
    IO.println "  def <name> : <type> := <value>"
    IO.println "  inductive <name> : <type> where | ctor : type ..."
    IO.println "  #check <expr>"
    IO.println "  #eval <expr>"
    IO.println "  #print <name>"
    IO.println "  :env       — list all names"
    IO.println "  :q         — quit"
    repl cb
    return
  -- Try to parse and process the command
  match cb.processSource line with
  | .ok (cb', results) =>
    for r in results do
      IO.println (formatResult cb' r)
    repl cb'
  | .error e =>
    IO.println s!"error: {e}"
    repl cb

/-- Format a single byte as two hex characters. -/
private def byteToHex (b : UInt8) : String :=
  let hexChars := "0123456789abcdef"
  let hi := String.singleton (hexChars.get ⟨b.toNat / 16⟩)
  let lo := String.singleton (hexChars.get ⟨b.toNat % 16⟩)
  hi ++ lo

/-- Format a Hash as a hex string. -/
def hashToHex (h : Hash) : String :=
  (List.range 32).foldl (fun acc i => acc ++ byteToHex (h.bytes.get! i)) ""

/-- Parse a single hex character to its value (0-15). -/
private def hexVal (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- Parse a hex string to a Hash. -/
def hexToHash (s : String) : Option Hash := do
  if s.length != 64 then none
  else
    let bytes ← (List.range 32).foldlM (init := ByteArray.empty) fun acc i => do
      let hi ← hexVal (s.get ⟨i * 2⟩)
      let lo ← hexVal (s.get ⟨i * 2 + 1⟩)
      return acc.push (hi * 16 + lo)
    if h : bytes.size = 32 then
      some ⟨bytes, h⟩
    else none

/-- Try to find the hm-net binary. Checks HM_NET_PATH env var, then looks next to the executable. -/
def findHmNet : IO String := do
  -- Check environment variable first
  match (← IO.getEnv "HM_NET_PATH") with
  | some path => return path
  | none =>
    -- Default: assume hm-net is in the same directory or on PATH
    return "hm-net"

/-- Recursively fetch a declaration and all its dependencies from the DHT.
    Supports stored-format declarations with href subterm references:
    1. Fetches the declaration bytes (may contain href tags)
    2. Collects href hashes and fetches each subterm from the DHT
    3. Reassembles the full declaration (resolving all hrefs)
    4. Verifies hash, fetches const dependencies, typechecks, and adds to env
    Backward-compatible: canonical-format bytes (no hrefs) also work. -/
partial def fetchWithDeps (handle : SidecarHandle) (env : Environment) (hash : Hash)
    (visited : Std.HashMap Hash Bool := {}) : IO (Environment × Std.HashMap Hash Bool) := do
  -- Skip if already in the environment or already visited
  if env.contains hash || visited.contains hash then
    return (env, visited)
  let visited := visited.insert hash true
  let resp ← handle.fetch hash
  match resp with
  | .found _ storedBytes => do
    -- Step 1: Collect href hashes from the stored-format bytes
    let hrefHashes := collectStoredDeclHRefs storedBytes
    -- Step 2: Fetch each subterm from the DHT
    let mut store : SubtermStore := {}
    for subHash in hrefHashes do
      let subResp ← handle.fetch subHash
      match subResp with
      | .found _ subBytes =>
        store := store.insert subHash subBytes
      | .notFound _ =>
        IO.eprintln s!"  WARNING: subterm not found: {hashToHex subHash}"
      | _ => pure ()
    -- Step 3: Reassemble the declaration (resolve all hrefs)
    match reassembleStoredDecl storedBytes store with
    | none =>
      IO.eprintln s!"  WARNING: failed to reassemble {hashToHex hash}"
      return (env, visited)
    | some decl => do
      -- Verify hash: reassembled decl → hashDecl → compare
      let computedHash := hashDecl decl
      if computedHash != hash then
        IO.eprintln s!"  WARNING: hash mismatch for {hashToHex hash}, skipping"
        return (env, visited)
      -- Step 4: Recursively fetch const dependencies (other declarations)
      let deps := decl.constHashes
      let mut env' := env
      let mut vis := visited
      for dep in deps do
        let (e, v) ← fetchWithDeps handle env' dep vis
        env' := e
        vis := v
      -- Typecheck and add to environment
      match checkDecl env' decl with
      | .ok (h, env'') =>
        let subInfo := if hrefHashes.isEmpty then "" else s!" ({hrefHashes.length} subterms resolved)"
        IO.println s!"  fetched & verified {hashToHex h}{subInfo}"
        return (env'', vis)
      | .error e =>
        IO.eprintln s!"  WARNING: typecheck failed for {hashToHex hash}: {e}"
        return (env', vis)
  | .notFound _ =>
    IO.eprintln s!"  not found in DHT: {hashToHex hash}"
    return (env, visited)
  | .error msg =>
    IO.eprintln s!"  DHT error for {hashToHex hash}: {msg}"
    return (env, visited)
  | _ =>
    return (env, visited)

/-- Publish all declarations from a codebase to the DHT.
    Uses subterm hash-consing: large subexpressions are published separately
    as content-addressed entries, and the declaration is stored in shattered
    form with href references to the subterms. -/
def publishCodebase (handle : SidecarHandle) (cb : Codebase) : IO Nat := do
  let mut count := 0
  let mut subtermCount := 0
  for (name, hash) in cb.names.toList do
    match cb.env.lookup hash with
    | some di =>
      -- Shatter the declaration: produces stored-format bytes + subterm store
      let (storedBytes, store) := shatterDecl di.decl
      -- Publish each subterm first
      for (subHash, subBytes) in store.toList do
        let resp ← handle.publish subHash subBytes
        match resp with
        | .published _ => subtermCount := subtermCount + 1
        | _ => pure ()
      -- Publish the stored-format declaration
      let resp ← handle.publish hash storedBytes
      match resp with
      | .published _ =>
        let storeInfo := if store.isEmpty then "" else s!" ({store.size} subterms)"
        IO.println s!"  published {name} ({hashToHex hash}){storeInfo}"
        count := count + 1
      | .error msg =>
        IO.eprintln s!"  error publishing {name}: {msg}"
      | _ =>
        IO.eprintln s!"  unexpected response for {name}"
    | none => pure ()  -- skip derived entities (ctors, recs) that don't have direct decls
  if subtermCount > 0 then
    IO.println s!"  ({subtermCount} shared subterms published)"
  return count

/-- Generate a manifest string from a codebase: one "name hexhash" per line. -/
def generateManifest (cb : Codebase) : String :=
  let entries := cb.names.toList.map fun (name, hash) => s!"{name} {hashToHex hash}"
  String.intercalate "\n" entries ++ "\n"

/-- Parse a manifest file into a list of (name, hash) pairs. -/
def parseManifest (content : String) : List (String × Hash) :=
  let lines := content.splitOn "\n" |>.filter (fun s => !s.isEmpty)
  lines.filterMap fun line =>
    let parts := line.splitOn " "
    match parts with
    | [name, hexHash] => (hexToHash hexHash).map fun h => (name, h)
    | _ => none

def main (args : List String) : IO Unit := do
  match args with
  | ["--test"] =>
    let stdout ← IO.getStdout
    stdout.putStrLn "Test 1: axiom"
    stdout.flush
    let src1 := "axiom A : Type"
    let cmds ← match HashMath.parseCommands src1 with
      | .ok c => pure c
      | .error e => do stdout.putStrLn s!"  Parse error: {e}"; pure []
    stdout.putStrLn s!"  Parsed: {cmds.length}"
    stdout.flush
    match Codebase.empty.processSource src1 with
    | .error e => stdout.putStrLn s!"  Elab error: {e}"
    | .ok (_, results) => stdout.putStrLn s!"  Elab OK: {results.length}"
    stdout.flush

    -- Build the block directly in kernel terms, bypassing the parser/elab
    stdout.putStrLn "Test 2: checkDecl on MyUnit"
    stdout.flush
    let myUnitBlock : HashMath.InductiveBlock := {
      numUnivParams := 0
      numParams := 0
      types := [{
        type := .sort (.succ .zero)   -- Type = Sort 1
        ctors := [.iref 0 []]        -- unit : MyUnit (iref 0)
      }]
    }
    stdout.putStrLn "  Block created, calling checkDecl..."
    stdout.flush
    match HashMath.checkDecl HashMath.Environment.empty (HashMath.Decl.inductive myUnitBlock) with
    | .error e => do stdout.putStrLn s!"  checkDecl error: {e}"; stdout.flush
    | .ok (_h, _) => do stdout.putStrLn s!"  checkDecl OK"; stdout.flush

    stdout.putStrLn "Test 3a: parse just 'inductive'"
    stdout.flush
    let s3a : HashMath.PState := ⟨"inductive MyUnit : Type where\n  | unit : MyUnit", ⟨0⟩⟩
    match HashMath.parseCommand s3a with
    | .error e => do stdout.putStrLn s!"  Error: {e}"; stdout.flush
    | .ok (_, _) => do stdout.putStrLn s!"  OK"; stdout.flush

  | ["--test-ipc"] => do
    let hmNet ← findHmNet
    IO.println "IPC integration test: spawning hm-net sidecar..."
    let handle ← SidecarHandle.spawn hmNet #["--ephemeral"]
    IO.println "  Sending ping..."
    let ok ← handle.ping
    if ok then
      IO.println "  PASS: got pong"
    else
      IO.eprintln "  FAIL: no pong"
      return
    IO.println "  Sending shutdown..."
    handle.shutdown
    IO.println "  PASS: sidecar exited cleanly"
    IO.println "IPC integration test passed."

  | ["serve"] => do
    let hmNet ← findHmNet
    IO.println "Starting hm-net sidecar..."
    let handle ← SidecarHandle.spawn hmNet
    let ok ← handle.ping
    if ok then
      IO.println "Sidecar is running. Entering REPL with network support."
      IO.println "Type :help for commands, :q to quit."
      repl Codebase.empty
    else
      IO.eprintln "Failed to ping sidecar."
    handle.shutdown

  | ["serve", "--listen", addr] => do
    let hmNet ← findHmNet
    IO.println s!"Starting hm-net sidecar on {addr}..."
    let handle ← SidecarHandle.spawn hmNet #["--listen", addr]
    let ok ← handle.ping
    if ok then
      IO.println "Sidecar is running."
      IO.println "Type :help for commands, :q to quit."
      repl Codebase.empty
    else
      IO.eprintln "Failed to ping sidecar."
    handle.shutdown

  | ["publish", "--manifest", manifestPath] => do
    let hmNet ← findHmNet
    let handle ← SidecarHandle.spawn hmNet
    let ok ← handle.ping
    if !ok then
      IO.eprintln "Failed to connect to sidecar."
      return
    let content ← IO.FS.readFile manifestPath
    let entries := parseManifest content
    if entries.isEmpty then
      IO.eprintln "No valid entries in manifest."
      handle.shutdown
      return
    let mut count : Nat := 0
    for (name, hash) in entries do
      let resp ← handle.fetch hash
      match resp with
      | .found _ _ =>
        IO.println s!"  already in DHT: {name}"
        count := count + 1
      | _ =>
        IO.eprintln s!"  not found locally for publish: {name} ({hashToHex hash})"
    IO.println s!"Checked {count}/{entries.length} entries in manifest."
    handle.shutdown

  | "publish" :: files => do
    if files.isEmpty then
      IO.eprintln "Usage: hm publish <file.hm> [file2.hm ...]"
      return
    let hmNet ← findHmNet
    let handle ← SidecarHandle.spawn hmNet
    let ok ← handle.ping
    if !ok then
      IO.eprintln "Failed to connect to sidecar."
      return
    let mut cb := Codebase.empty
    for file in files do
      let source ← IO.FS.readFile file
      match cb.processSource source with
      | .ok (cb', results) =>
        cb := cb'
        for r in results do
          IO.println (formatResult cb' r)
      | .error e =>
        IO.eprintln s!"error in {file}: {e}"
        handle.shutdown
        return
    let count ← publishCodebase handle cb
    IO.println s!"Published {count} declaration(s) to the DHT."
    handle.shutdown

  | ["fetch", "--manifest", manifestPath] => do
    let hmNet ← findHmNet
    let handle ← SidecarHandle.spawn hmNet
    let ok ← handle.ping
    if !ok then
      IO.eprintln "Failed to connect to sidecar."
      return
    let content ← IO.FS.readFile manifestPath
    let entries := parseManifest content
    if entries.isEmpty then
      IO.eprintln "No valid entries in manifest."
      handle.shutdown
      return
    IO.println s!"Fetching {entries.length} declarations from manifest..."
    let mut env := Environment.empty
    let mut visited : Std.HashMap Hash Bool := {}
    for (_name, hash) in entries do
      let (env', vis') ← fetchWithDeps handle env hash visited
      env := env'
      visited := vis'
    IO.println s!"Done. Environment has {env.decls.size} verified declaration(s)."
    handle.shutdown

  | ["fetch", hashStr] => do
    match hexToHash hashStr with
    | none =>
      IO.eprintln "Invalid hash. Expected 64-character hex string."
    | some hash => do
      let hmNet ← findHmNet
      let handle ← SidecarHandle.spawn hmNet
      IO.println s!"Fetching {hashToHex hash} (with dependencies)..."
      let (env, _) ← fetchWithDeps handle Environment.empty hash
      let nDecls := env.decls.size
      IO.println s!"Done. Environment has {nDecls} verified declaration(s)."
      handle.shutdown

  | ["manifest", "--generate"] => do
    IO.eprintln "Usage: hm manifest --generate <file.hm> [file2.hm ...] > lib.hmm"

  | "manifest" :: "--generate" :: files => do
    let mut cb := Codebase.empty
    for file in files do
      let source ← IO.FS.readFile file
      match cb.processSource source with
      | .ok (cb', _) => cb := cb'
      | .error e =>
        IO.eprintln s!"error in {file}: {e}"
        return
    IO.print (generateManifest cb)

  | ["peers"] => do
    let hmNet ← findHmNet
    let handle ← SidecarHandle.spawn hmNet
    let peers ← handle.getPeers
    if peers.isEmpty then
      IO.println "No connected peers."
    else
      IO.println s!"{peers.length} connected peer(s):"
      for p in peers do
        IO.println s!"  {p}"
    handle.shutdown

  | [] =>
    IO.println "HashMath v0.1.0 — Content-addressed proof assistant"
    IO.println "Type :help for commands, :q to quit."
    repl Codebase.empty
  | files =>
    -- Filter out flags that might reach here
    let hmFiles := files.filter (fun f => !f.startsWith "--")
    if hmFiles.isEmpty then
      IO.eprintln "Unknown command. Use --test, serve, publish, fetch, or peers."
      IO.eprintln "Or provide .hm files to process."
      return
    let mut cb := Codebase.empty
    for file in hmFiles do
      let source ← IO.FS.readFile file
      match cb.processSource source with
      | .ok (cb', results) =>
        cb := cb'
        for r in results do
          IO.println (formatResult cb' r)
      | .error e =>
        IO.eprintln s!"error in {file}: {e}"
        return
    IO.println s!"Processed {hmFiles.length} file(s) successfully."
