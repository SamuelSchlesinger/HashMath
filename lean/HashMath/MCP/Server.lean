/-
  HashMath.MCP.Server — MCP (Model Context Protocol) server for HashMath

  Implements the MCP stdio transport, exposing HashMath type-checking,
  evaluation, and environment inspection as tools that AI agents can call.

  Usage: `hm mcp` starts the server, reading JSON-RPC from stdin and
  writing responses to stdout. The server maintains a persistent Codebase
  across tool calls, allowing incremental proof development.
-/

import HashMath.Elab
import HashMath.MCP.Json

namespace HashMath.MCP

open HashMath

-- ═══════════════════════════════════════════════
-- Helpers
-- ═══════════════════════════════════════════════

private def stringContains (haystack : String) (needle : String) : Bool :=
  let rec go (i : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if i + needle.length > haystack.length then false
      else if (haystack.drop i).startsWith needle then true
      else go (i + 1) fuel
  if needle.isEmpty then true
  else go 0 (haystack.length + 1)

/-- Validate that an expression input contains no newlines or control characters.
    Prevents command injection via string interpolation into source code. -/
private def validateExprInput (s : String) : Except String String :=
  if s.any (fun c => c == '\n' || c == '\r' || c.toNat < 32) then
    .error "input contains invalid characters"
  else .ok s

/-- Validate that a file path contains no path traversal components.
    Rejects absolute paths and paths containing `..`. -/
private def validatePath (path : String) : IO Unit := do
  if stringContains path ".." then
    throw (IO.userError "path traversal not allowed")
  if path.startsWith "/" then
    throw (IO.userError "absolute paths not allowed")

-- ═══════════════════════════════════════════════
-- File loading (self-contained version of processFileIO)
-- ═══════════════════════════════════════════════

private partial def loadFileIO (cb : Codebase) (filePath : System.FilePath)
    (imported : IO.Ref (Std.HashMap String Bool)) : IO (Codebase × List ElabResult) := do
  let key := filePath.toString
  let map ← imported.get
  if map.contains key then return (cb, [])
  imported.set (map.insert key true)
  let source ← try
    IO.FS.readFile filePath
  catch _ =>
    throw (IO.userError s!"import error: file not found '{filePath}'")
  let cmds ← match parseCommands source with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"parse error in {filePath}: {e}")
  let dir := filePath.parent.getD ⟨"."⟩
  let mut cb := cb
  let mut results : List ElabResult := []
  for cmd in cmds do
    match cmd with
    | .import_ path =>
      if stringContains path ".." || path.startsWith "/" then
        throw (IO.userError s!"import error: path '{path}' contains disallowed components")
      let fullPath := dir / path
      let (cb', _) ← loadFileIO cb fullPath imported
      cb := cb'
    | _ =>
      match cb.processCommand cmd with
      | .ok (cb', result) =>
        cb := cb'
        results := result :: results
      | .error e => throw (IO.userError s!"{filePath}: {e}")
  return (cb, results.reverse)

-- ═══════════════════════════════════════════════
-- Server state
-- ═══════════════════════════════════════════════

structure MCPState where
  codebase : Codebase
  imported : Std.HashMap String Bool
  deriving Inhabited

-- ═══════════════════════════════════════════════
-- Tool definitions
-- ═══════════════════════════════════════════════

private def mkInputSchema (props : List (String × Json)) (required : List String) : Json :=
  .obj [
    ("type", .str "object"),
    ("properties", .obj (props.map fun (k, v) => (k, v))),
    ("required", .arr (required.map .str))
  ]

private def mkProp (ty : String) (desc : String) : Json :=
  .obj [("type", .str ty), ("description", .str desc)]

private def toolDefinitions : List Json := [
  .obj [
    ("name", .str "hm_process"),
    ("description", .str "Type-check and process HashMath (.hm) source code. Declarations are added to the persistent environment. Returns results for each declaration (name and hash on success, or error message). Use this to define axioms, definitions, and inductive types."),
    ("inputSchema", mkInputSchema
      [("source", mkProp "string" "HashMath source code to type-check and process")]
      ["source"])
  ],
  .obj [
    ("name", .str "hm_load_file"),
    ("description", .str "Load and type-check a .hm file, resolving any `import` directives. All declarations are added to the persistent environment. Use this to load stdlib modules (e.g., 'lean/stdlib/Prelude.hm') before writing proofs."),
    ("inputSchema", mkInputSchema
      [("path", mkProp "string" "Path to the .hm file (absolute or relative to working directory)")]
      ["path"])
  ],
  .obj [
    ("name", .str "hm_check"),
    ("description", .str "Infer and display the type of a HashMath expression in the current environment. Equivalent to the `#check` REPL command. The expression must be valid in the current environment."),
    ("inputSchema", mkInputSchema
      [("expr", mkProp "string" "HashMath expression to type-check")]
      ["expr"])
  ],
  .obj [
    ("name", .str "hm_eval"),
    ("description", .str "Normalize a HashMath expression to weak head normal form in the current environment. Equivalent to the `#eval` REPL command. Useful for testing computation rules."),
    ("inputSchema", mkInputSchema
      [("expr", mkProp "string" "HashMath expression to normalize")]
      ["expr"])
  ],
  .obj [
    ("name", .str "hm_print"),
    ("description", .str "Display information about a declaration by name, including its internal representation. Equivalent to the `#print` REPL command."),
    ("inputSchema", mkInputSchema
      [("name", mkProp "string" "Name of the declaration to inspect")]
      ["name"])
  ],
  .obj [
    ("name", .str "hm_env"),
    ("description", .str "List all declaration names in the current environment. Optionally filter by a substring pattern."),
    ("inputSchema", mkInputSchema
      [("pattern", mkProp "string" "Optional substring to filter names by")]
      [])
  ],
  .obj [
    ("name", .str "hm_reset"),
    ("description", .str "Reset the environment to empty. Use this to start fresh."),
    ("inputSchema", mkInputSchema [] [])
  ],
  .obj [
    ("name", .str "hm_read_source"),
    ("description", .str "Read the source code of a .hm file. Useful for examining stdlib modules to understand available types, definitions, and proof techniques."),
    ("inputSchema", mkInputSchema
      [("path", mkProp "string" "Path to the .hm file to read")]
      ["path"])
  ]
]

-- ═══════════════════════════════════════════════
-- Tool handlers
-- ═══════════════════════════════════════════════

private def formatResultJson (cb : Codebase) : ElabResult → Json
  | .declared name _h => .obj [("status", .str "ok"), ("name", .str name)]
  | .checked _e ty => .obj [("status", .str "ok"), ("type", .str (cb.ppExpr [] [] ty))]
  | .evaluated _e result => .obj [("status", .str "ok"), ("value", .str (cb.ppExpr [] [] result))]
  | .printed name info => .obj [("status", .str "ok"), ("name", .str name), ("info", .str info)]

private def formatResultSummary (cb : Codebase) : ElabResult → String
  | .declared name _ => s!"✓ {name}"
  | .checked _ ty => s!"  : {cb.ppExpr [] [] ty}"
  | .evaluated _ result => s!"  = {cb.ppExpr [] [] result}"
  | .printed name info => s!"{name} : {info}"

private def handleProcess (state : MCPState) (args : Json) : IO (MCPState × Json) := do
  let source := args.fieldStr "source"
  if source.isEmpty then
    return (state, .obj [("error", .str "missing 'source' argument")])
  match state.codebase.processSource source with
  | .ok (cb', results) =>
    let resultJsons := results.map (formatResultJson cb')
    let summary := results.map (formatResultSummary cb')
    return ({ state with codebase := cb' },
      .obj [("results", .arr resultJsons),
            ("summary", .str (String.intercalate "\n" summary))])
  | .error e =>
    return (state, .obj [("error", .str e)])

private partial def handleLoadFile (state : MCPState) (args : Json) : IO (MCPState × Json) := do
  let path := args.fieldStr "path"
  if path.isEmpty then
    return (state, .obj [("error", .str "missing 'path' argument")])
  let importedRef ← IO.mkRef state.imported
  try
    validatePath path
    let (cb', results) ← loadFileIO state.codebase ⟨path⟩ importedRef
    let imported' ← importedRef.get
    let summary := results.map (formatResultSummary cb')
    let nDecls := results.length
    return ({ codebase := cb', imported := imported' },
      .obj [("status", .str "ok"),
            ("declarations", .num (Int.ofNat nDecls)),
            ("summary", .str (String.intercalate "\n" summary))])
  catch e =>
    return (state, .obj [("error", .str (toString e))])

private def handleCheck (state : MCPState) (args : Json) : IO (MCPState × Json) := do
  let expr := args.fieldStr "expr"
  if expr.isEmpty then
    return (state, .obj [("error", .str "missing 'expr' argument")])
  match validateExprInput expr with
  | .error e => return (state, .obj [("error", .str e)])
  | .ok _ => pure ()
  let source := s!"#check {expr}"
  match state.codebase.processSource source with
  | .ok (_, results) =>
    match results with
    | [.checked _ ty] =>
      return (state, .obj [("type", .str (state.codebase.ppExpr [] [] ty))])
    | _ => return (state, .obj [("error", .str "unexpected result")])
  | .error e =>
    return (state, .obj [("error", .str e)])

private def handleEval (state : MCPState) (args : Json) : IO (MCPState × Json) := do
  let expr := args.fieldStr "expr"
  if expr.isEmpty then
    return (state, .obj [("error", .str "missing 'expr' argument")])
  match validateExprInput expr with
  | .error e => return (state, .obj [("error", .str e)])
  | .ok _ => pure ()
  let source := s!"#eval {expr}"
  match state.codebase.processSource source with
  | .ok (_, results) =>
    match results with
    | [.evaluated _ result] =>
      return (state, .obj [("value", .str (state.codebase.ppExpr [] [] result))])
    | _ => return (state, .obj [("error", .str "unexpected result")])
  | .error e =>
    return (state, .obj [("error", .str e)])

private def handlePrint (state : MCPState) (args : Json) : IO (MCPState × Json) := do
  let name := args.fieldStr "name"
  if name.isEmpty then
    return (state, .obj [("error", .str "missing 'name' argument")])
  match validateExprInput name with
  | .error e => return (state, .obj [("error", .str e)])
  | .ok _ => pure ()
  let source := s!"#print {name}"
  match state.codebase.processSource source with
  | .ok (_, results) =>
    match results with
    | [.printed _ info] =>
      return (state, .obj [("name", .str name), ("info", .str info)])
    | _ => return (state, .obj [("error", .str "unexpected result")])
  | .error e =>
    return (state, .obj [("error", .str e)])

private def handleEnv (state : MCPState) (args : Json) : IO (MCPState × Json) := do
  let pattern := args.fieldStr "pattern"
  let names := state.codebase.names.toList.map (·.1)
  let filtered := if pattern.isEmpty then names
    else names.filter fun n => stringContains n pattern
  let sorted := filtered.mergeSort (· < ·)
  let nNames := sorted.length
  return (state,
    .obj [("names", .arr (sorted.map .str)),
          ("count", .num (Int.ofNat nNames))])

private def handleReset (_state : MCPState) (_args : Json) : IO (MCPState × Json) := do
  return ({ codebase := Codebase.empty, imported := {} },
    .obj [("status", .str "ok"), ("message", .str "environment reset to empty")])

private def handleReadSource (state : MCPState) (args : Json) : IO (MCPState × Json) := do
  let path := args.fieldStr "path"
  if path.isEmpty then
    return (state, .obj [("error", .str "missing 'path' argument")])
  try
    validatePath path
    let content ← IO.FS.readFile ⟨path⟩
    return (state, .obj [("path", .str path), ("source", .str content)])
  catch e =>
    return (state, .obj [("error", .str (toString e))])

private partial def handleToolCall (state : MCPState) (name : String) (args : Json) :
    IO (MCPState × Json) :=
  match name with
  | "hm_process" => handleProcess state args
  | "hm_load_file" => handleLoadFile state args
  | "hm_check" => handleCheck state args
  | "hm_eval" => handleEval state args
  | "hm_print" => handlePrint state args
  | "hm_env" => handleEnv state args
  | "hm_reset" => handleReset state args
  | "hm_read_source" => handleReadSource state args
  | _ => return (state, .obj [("error", .str s!"unknown tool '{name}'")])

-- ═══════════════════════════════════════════════
-- MCP Protocol handler
-- ═══════════════════════════════════════════════

private def handleInitialize (id : Json) : Json :=
  Json.rpcResult id (.obj [
    ("protocolVersion", .str "2024-11-05"),
    ("capabilities", .obj [("tools", .obj [])]),
    ("serverInfo", .obj [
      ("name", .str "hm-mcp"),
      ("version", .str "0.1.0")
    ])
  ])

private def handleToolsList (id : Json) : Json :=
  Json.rpcResult id (.obj [("tools", .arr toolDefinitions)])

private partial def handleMessage (state : MCPState) (msg : Json) :
    IO (MCPState × Option Json) := do
  let method := msg.fieldStr "method"
  let id := msg.field? "id" |>.getD .null
  let params := msg.field? "params" |>.getD (.obj [])
  match method with
  | "initialize" =>
    return (state, some (handleInitialize id))
  | "notifications/initialized" =>
    return (state, none)
  | "tools/list" =>
    return (state, some (handleToolsList id))
  | "tools/call" =>
    let toolName := params.fieldStr "name"
    let toolArgs := params.field? "arguments" |>.getD (.obj [])
    let (state', result) ← handleToolCall state toolName toolArgs
    let response := Json.rpcResult id (.obj [
      ("content", .arr [.obj [
        ("type", .str "text"),
        ("text", .str result.render)
      ]])
    ])
    return (state', some response)
  | "ping" =>
    return (state, some (Json.rpcResult id (.obj [])))
  | _ =>
    let err := Json.rpcError id (-32601) s!"method not found: {method}"
    return (state, some err)

-- ═══════════════════════════════════════════════
-- Main server loop
-- ═══════════════════════════════════════════════

/-- Run the MCP server, reading JSON-RPC messages from stdin and writing
    responses to stdout. Maintains a persistent Codebase across calls. -/
partial def mcpServer : IO Unit := do
  IO.eprintln "hm-mcp: HashMath MCP server starting (stdio transport)"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stateRef ← IO.mkRef ({ codebase := Codebase.empty, imported := {} } : MCPState)
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return  -- EOF
    let line := line.trimAsciiEnd.toString
    if line.isEmpty then
      loop
      return
    match Json.parse line with
    | .error e =>
      let err := Json.rpcError .null (-32700) s!"parse error: {e}"
      stdout.putStrLn err.render
      stdout.flush
      loop
    | .ok msg => do
      let state ← stateRef.get
      let (state', response) ← handleMessage state msg
      stateRef.set state'
      match response with
      | some resp =>
        stdout.putStrLn resp.render
        stdout.flush
      | none => pure ()
      loop
  loop

end HashMath.MCP
