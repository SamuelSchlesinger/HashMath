/-
  HashMath CLI — Command-line interface for the HashMath proof assistant
-/

import HashMath.Elab

open HashMath

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
  | [] =>
    IO.println "HashMath v0.1.0 — Content-addressed proof assistant"
    IO.println "Type :help for commands, :q to quit."
    repl Codebase.empty
  | files =>
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
        return
    IO.println s!"Processed {files.length} file(s) successfully."
