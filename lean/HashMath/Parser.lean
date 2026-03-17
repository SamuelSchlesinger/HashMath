/-
  HashMath.Parser — Recursive descent parser for HashMath surface syntax
-/

import HashMath.Syntax

namespace HashMath

private def strEndPos (s : String) : String.Pos.Raw := ⟨s.utf8ByteSize⟩

structure PState where
  input : String
  pos : String.Pos.Raw
  deriving Repr

abbrev P (α : Type) := PState → Except String (α × PState)

namespace P

def run (p : P α) (input : String) : Except String α :=
  match p ⟨input, ⟨0⟩⟩ with
  | .ok (a, _) => .ok a
  | .error e => .error e

def pure (a : α) : P α := fun s => .ok (a, s)

def bind (p : P α) (f : α → P β) : P β := fun s =>
  match p s with
  | .ok (a, s') => f a s'
  | .error e => .error e

def fail (msg : String) : P α := fun _s => .error msg

def peek : P (Option Char) := fun s =>
  if s.pos < strEndPos s.input then
    .ok (some (String.Pos.Raw.get s.input s.pos), s)
  else
    .ok (none, s)

def atEnd : P Bool := fun s =>
  .ok (s.pos >= strEndPos s.input, s)

def next : P Char := fun s =>
  if s.pos < strEndPos s.input then
    let c := String.Pos.Raw.get s.input s.pos
    .ok (c, ⟨s.input, String.Pos.Raw.next s.input s.pos⟩)
  else
    .error "unexpected end of input"

def tryP (p : P α) : P (Option α) := fun s =>
  match p s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

end P

instance : Monad P where
  pure := P.pure
  bind := P.bind

private partial def skipWs (input : String) (pos : String.Pos.Raw) : String.Pos.Raw :=
  if pos >= strEndPos input then pos
  else
    let c := String.Pos.Raw.get input pos
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      skipWs input (String.Pos.Raw.next input pos)
    else if c == '-' then
      let pos2 := String.Pos.Raw.next input pos
      if pos2 < strEndPos input && String.Pos.Raw.get input pos2 == '-' then
        skipComment input (String.Pos.Raw.next input pos2)
      else pos
    else pos
where
  skipComment (input : String) (pos : String.Pos.Raw) : String.Pos.Raw :=
    if pos >= strEndPos input then pos
    else if String.Pos.Raw.get input pos == '\n' then skipWs input (String.Pos.Raw.next input pos)
    else skipComment input (String.Pos.Raw.next input pos)

private def ws : P Unit := fun s =>
  .ok ((), ⟨s.input, skipWs s.input s.pos⟩)

private def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\'' || c == '.'

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def checkChars : List Char → String → String.Pos.Raw → Option String.Pos.Raw
  | [], _, pos => some pos
  | c :: cs, input, pos =>
    if pos < strEndPos input && String.Pos.Raw.get input pos == c then
      checkChars cs input (String.Pos.Raw.next input pos)
    else none

private def keyword (kw : String) : P Unit := fun s =>
  let pos := skipWs s.input s.pos
  match checkChars kw.toList s.input pos with
  | none => .error s!"expected '{kw}'"
  | some pos' =>
    if pos' < strEndPos s.input && isIdentChar (String.Pos.Raw.get s.input pos') then
      .error s!"expected '{kw}'"
    else
      .ok ((), ⟨s.input, pos'⟩)

private def symbol (sym : String) : P Unit := fun s =>
  let pos := skipWs s.input s.pos
  match checkChars sym.toList s.input pos with
  | none => .error s!"expected '{sym}'"
  | some pos' => .ok ((), ⟨s.input, pos'⟩)

private partial def collectIdent (input : String) (pos : String.Pos.Raw) (acc : List Char) : String × String.Pos.Raw :=
  if pos >= strEndPos input then (String.ofList acc.reverse, pos)
  else
    let c := String.Pos.Raw.get input pos
    if isIdentChar c then collectIdent input (String.Pos.Raw.next input pos) (c :: acc)
    else (String.ofList acc.reverse, pos)

private def ident : P String := fun s =>
  let pos := skipWs s.input s.pos
  if pos >= strEndPos s.input then .error "expected identifier"
  else
    let c := String.Pos.Raw.get s.input pos
    if !isIdentStart c then .error s!"expected identifier, got '{c}'"
    else
      let (name, pos') := collectIdent s.input (String.Pos.Raw.next s.input pos) [c]
      .ok (name, ⟨s.input, pos'⟩)

private partial def collectDigits (input : String) (pos : String.Pos.Raw) (acc : Nat) : Nat × String.Pos.Raw :=
  if pos >= strEndPos input then (acc, pos)
  else
    let c := String.Pos.Raw.get input pos
    if c.isDigit then collectDigits input (String.Pos.Raw.next input pos) (acc * 10 + c.toNat - '0'.toNat)
    else (acc, pos)

private def natLit : P Nat := fun s =>
  let pos := skipWs s.input s.pos
  if pos >= strEndPos s.input then .error "expected number"
  else
    let c := String.Pos.Raw.get s.input pos
    if !c.isDigit then .error s!"expected number, got '{c}'"
    else
      let (n, pos') := collectDigits s.input (String.Pos.Raw.next s.input pos) (c.toNat - '0'.toNat)
      .ok (n, ⟨s.input, pos'⟩)

private partial def many (p : P α) : P (List α) := fun s =>
  match p s with
  | .ok (a, s') =>
    match many p s' with
    | .ok (as, s'') => .ok (a :: as, s'')
    | .error _ => .ok ([a], s')
  | .error _ => .ok ([], s)

private def many1 (p : P α) : P (List α) :=
  P.bind p (fun first => P.bind (many p) (fun rest => P.pure (first :: rest)))

private partial def sepBy (p : P α) (sep : P Unit) : P (List α) := fun s =>
  match p s with
  | .error _ => .ok ([], s)
  | .ok (a, s') =>
    match sep s' with
    | .error _ => .ok ([a], s')
    | .ok ((), s'') =>
      match sepBy p sep s'' with
      | .ok (as, s''') => .ok (a :: as, s''')
      | .error _ => .ok ([a], s')

private def reservedWords : List String :=
  ["fun", "Sort", "Prop", "Type", "let", "in", "axiom", "def", "inductive",
   "where", "mutual", "end", "variable", "import", "match", "return"]

private def identNonReserved : P String :=
  P.bind ident fun name =>
    if reservedWords.any (· == name) then
      P.fail s!"'{name}' is a reserved word"
    else
      P.pure name

/-- Check if a parsed identifier ends with '.' and the next char is '{'.
    If so, strip the trailing dot and return true (the '{' has been consumed). -/
private def checkTrailingDotBrace (name : String) : P (String × Bool) := fun s =>
  if name.endsWith "." then
    let pos := skipWs s.input s.pos
    if pos < strEndPos s.input && String.Pos.Raw.get s.input pos == '{' then
      let trimmed := (name.dropEnd 1).toString
      .ok ((trimmed, true), ⟨s.input, String.Pos.Raw.next s.input pos⟩)
    else
      .ok ((name, false), s)
  else
    .ok ((name, false), s)

private partial def collectStringChars (input : String) (pos : String.Pos.Raw) (acc : List Char)
    : Except String (String × String.Pos.Raw) :=
  if pos >= strEndPos input then .error "unterminated string literal"
  else
    let c := String.Pos.Raw.get input pos
    if c == '"' then .ok (String.ofList acc.reverse, String.Pos.Raw.next input pos)
    else collectStringChars input (String.Pos.Raw.next input pos) (c :: acc)

private def stringLit : P String := fun s =>
  let pos := skipWs s.input s.pos
  if pos >= strEndPos s.input || String.Pos.Raw.get s.input pos != '"' then
    .error "expected string literal"
  else
    match collectStringChars s.input (String.Pos.Raw.next s.input pos) [] with
    | .ok (str, pos') => .ok (str, ⟨s.input, pos'⟩)
    | .error e => .error e

-- All parsing functions use explicit state-passing and P.bind.

mutual

private partial def parseLevel : P SLevel := do
  let () ← ws
  let c? ← P.peek
  match c? with
  | some c =>
    if c.isDigit then
      let n ← natLit
      return .num n
    else
      let name ← ident
      if name == "max" then
        let l1 ← parseLevel
        let l2 ← parseLevel
        return .max l1 l2
      else if name == "imax" then
        let l1 ← parseLevel
        let l2 ← parseLevel
        return .imax l1 l2
      else
        return .param name
  | none => P.fail "expected universe level"

/-- Parse expression-level universe arguments: `.{level, level, ...}` -/
private partial def parseExprUnivArgs : P (List SLevel) := do
  let r? ← P.tryP (symbol ".{")
  match r? with
  | some () =>
    let levels ← sepBy parseLevel (symbol ",")
    let () ← symbol "}"
    return levels
  | none => return []

private partial def parseAtom : P SExpr := do
  let () ← ws
  let c? ← P.peek
  match c? with
  | none => P.fail "expected expression"
  | some '(' =>
    let () ← symbol "("
    let e ← parseExpr
    let () ← symbol ")"
    return e
  | some c =>
    if c.isDigit then
      P.fail "numeric literals not supported; use zero/succ"
    else if c.isAlpha || c == '_' then
      let name ← ident
      if name == "Sort" then
        let l ← parseLevel
        return .sort l
      else if name == "Prop" then
        return .sort (.num 0)
      else if name == "Type" then
        let n? ← P.tryP natLit
        match n? with
        | some n => return .sort (.num (n + 1))
        | none => return .sort (.num 1)
      else if reservedWords.any (· == name) then
        P.fail s!"unexpected keyword '{name}'"
      else
        -- Handle Name.{level, ...}: ident parser consumes trailing dot,
        -- so check if name ends with '.' and next char is '{'
        let (name', hasTrailingDotBrace) ← checkTrailingDotBrace name
        if hasTrailingDotBrace then
          let levels ← sepBy parseLevel (symbol ",")
          let () ← symbol "}"
          return .var name' levels
        else
          -- Also try .{ without trailing dot (e.g., if name has no dot)
          let univArgs ← parseExprUnivArgs
          return .var name' univArgs
    else
      P.fail s!"unexpected character '{c}'"

private partial def parseAppExpr : P SExpr := do
  let head ← parseAtom
  let args ← many parseAtom
  return args.foldl SExpr.app head

private partial def parseArrowExpr : P SExpr := do
  let lhs ← parseAppExpr
  let arrow? ← P.tryP (symbol "→")
  match arrow? with
  | some () =>
    let rhs ← parseExpr
    return .arrow lhs rhs
  | none => return lhs

private partial def parseBinder : P (List (String × SExpr)) := do
  let () ← symbol "("
  let names ← many1 identNonReserved
  let () ← symbol ":"
  let ty ← parseExpr
  let () ← symbol ")"
  return names.map (·, ty)

private partial def parseExpr : P SExpr := do
  let () ← ws
  let match_? ← P.tryP (keyword "match")
  match match_? with
  | some () => parseMatch
  | none =>
  let lam? ← P.tryP (keyword "fun")
  match lam? with
  | some () => parseLambda
  | none =>
    let fa? ← P.tryP (symbol "∀")
    match fa? with
    | some () => parseForallE
    | none =>
      let fa2? ← P.tryP (keyword "forall")
      match fa2? with
      | some () => parseForallE
      | none =>
        let lam2? ← P.tryP (symbol "λ")
        match lam2? with
        | some () => parseLambda
        | none =>
          let let_? ← P.tryP (keyword "let")
          match let_? with
          | some () => parseLetE
          | none => parseArrowExpr

private partial def parseLambda : P SExpr := do
  let binders ← many1 parseBinder
  let allBinders := binders.foldl (· ++ ·) []
  let () ← symbol "=>"
  let body ← parseExpr
  return SExpr.mkLam allBinders body

private partial def parseForallE : P SExpr := do
  let binders ← many1 parseBinder
  let allBinders := binders.foldl (· ++ ·) []
  let () ← symbol ","
  let body ← parseExpr
  return SExpr.mkPi allBinders body

private partial def parseLetE : P SExpr := do
  let name ← identNonReserved
  let () ← symbol ":"
  let ty ← parseExpr
  let () ← symbol ":="
  let val ← parseExpr
  let () ← keyword "in"
  let body ← parseExpr
  return .letE name ty val body

private partial def parseMatchArm : P (String × List String × SExpr) := do
  let () ← symbol "|"
  let ctorName ← ident
  let vars ← many identNonReserved
  let () ← symbol "=>"
  let body ← parseExpr
  return (ctorName, vars, body)

private partial def parseMatch : P SExpr := do
  let univs ← parseExprUnivArgs
  let scrut ← parseAtom
  let asResult ← P.tryP (keyword "as")
  let asVars ← match asResult with
    | some () => many1 identNonReserved
    | none => P.pure []
  let () ← symbol ":"
  let typeE ← parseAppExpr
  let () ← keyword "return"
  let retE ← parseExpr
  let () ← symbol "{"
  let arms ← many parseMatchArm
  let () ← symbol "}"
  let ctors := arms.map (fun (c, _, _) => c)
  let varss := arms.map (fun (_, v, _) => v)
  let bodies := arms.map (fun (_, _, b) => b)
  return .match_ univs scrut asVars typeE retE ctors varss bodies

end -- mutual

private def parseConstructor : P SConstructor := do
  let () ← symbol "|"
  let name ← identNonReserved
  let () ← symbol ":"
  let ty ← parseExpr
  return { name, type := ty }

private def parseUnivParams : P (List String) := do
  let r? ← P.tryP (symbol ".{")
  match r? with
  | some () =>
    let params ← sepBy identNonReserved (symbol ",")
    let () ← symbol "}"
    return params
  | none => return []

/-- Parse an identifier that may have `.{u, v, ...}` universe parameters attached.
    Handles both `name .{u}` (space before dot) and `name.{u}` (no space, dot consumed by ident). -/
private def identWithUnivParams : P (String × List String) := do
  let name ← identNonReserved
  let (name', hasDotBrace) ← checkTrailingDotBrace name
  if hasDotBrace then
    let params ← sepBy identNonReserved (symbol ",")
    let () ← symbol "}"
    return (name', params)
  else
    let univParams ← parseUnivParams
    return (name', univParams)

private def parseInductive : P SDecl := do
  let (name, univParams) ← identWithUnivParams
  let paramBinders ← many parseBinder
  let allParams := paramBinders.foldl (· ++ ·) []
  let () ← symbol ":"
  let ty ← parseExpr
  let () ← keyword "where"
  let ctors ← many parseConstructor
  -- Wrap type and constructor types with parameter binders
  let wrappedTy := SExpr.mkPi allParams ty
  let wrappedCtors := ctors.map fun c =>
    { c with type := SExpr.mkPi allParams c.type }
  return .inductive_ univParams (List.length allParams)
    [{ name, type := wrappedTy, ctors := wrappedCtors }]

private partial def parseMutualType : P SInductiveType := do
  let () ← keyword "inductive"
  let name ← identNonReserved
  let () ← symbol ":"
  let ty ← parseExpr
  let () ← keyword "where"
  let ctors ← many parseConstructor
  return { name, type := ty, ctors }

private def parseMutual : P SDecl := do
  let univParams ← parseUnivParams
  let types ← many1 parseMutualType
  let () ← keyword "end"
  return .inductive_ univParams 0 types

def parseCommand : P Command := do
  let () ← ws
  let done ← P.atEnd
  if done then P.fail "empty input"
  else
    -- Try #check
    match ← P.tryP (symbol "#check") with
    | some () =>
      let e ← parseExpr
      return .check e
    | none =>
    -- Try #eval
    match ← P.tryP (symbol "#eval") with
    | some () =>
      let e ← parseExpr
      return .eval e
    | none =>
    -- Try #print
    match ← P.tryP (symbol "#print") with
    | some () =>
      let name ← ident
      return .print name
    | none =>
    -- Try import
    match ← P.tryP (keyword "import") with
    | some () =>
      let path ← stringLit
      return .import_ path
    | none =>
    -- Try axiom
    match ← P.tryP (keyword "axiom") with
    | some () =>
      let (name, univParams) ← identWithUnivParams
      let () ← symbol ":"
      let ty ← parseExpr
      return .decl (.axiom_ name univParams ty)
    | none =>
    -- Try def
    match ← P.tryP (keyword "def") with
    | some () =>
      let (name, univParams) ← identWithUnivParams
      let () ← symbol ":"
      let ty ← parseExpr
      let () ← symbol ":="
      let val ← parseExpr
      return .decl (.def_ name univParams ty val)
    | none =>
    -- Try inductive
    match ← P.tryP (keyword "inductive") with
    | some () =>
      let d ← parseInductive
      return .decl d
    | none =>
    -- Try mutual
    match ← P.tryP (keyword "mutual") with
    | some () =>
      let d ← parseMutual
      return .decl d
    | none =>
    P.fail "expected command (import, axiom, def, inductive, mutual, #check, #eval, #print)"

private partial def parseCommandsGo (input : String) (posBytes : Nat) (acc : List Command)
    : Except String (List Command) :=
  let pos' := skipWs input ⟨posBytes⟩
  if pos' >= strEndPos input then .ok acc.reverse
  else match parseCommand ⟨input, pos'⟩ with
  | .ok (cmd, s'') => parseCommandsGo s''.input s''.pos.byteIdx (cmd :: acc)
  | .error e => .error s!"parse error at position {pos'.byteIdx}: {e}"

def parseCommands (input : String) : Except String (List Command) :=
  parseCommandsGo input 0 []

end HashMath
