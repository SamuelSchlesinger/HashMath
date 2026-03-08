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
    .ok (some (s.input.get s.pos), s)
  else
    .ok (none, s)

def atEnd : P Bool := fun s =>
  .ok (s.pos >= strEndPos s.input, s)

def next : P Char := fun s =>
  if s.pos < strEndPos s.input then
    let c := s.input.get s.pos
    .ok (c, ⟨s.input, s.input.next s.pos⟩)
  else
    .error "unexpected end of input"

def tryP (p : P α) : P (Option α) := fun s =>
  match p s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

end P

private partial def skipWs (input : String) (pos : String.Pos.Raw) : String.Pos.Raw :=
  if pos >= strEndPos input then pos
  else
    let c := input.get pos
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      skipWs input (input.next pos)
    else if c == '-' then
      let pos2 := input.next pos
      if pos2 < strEndPos input && input.get pos2 == '-' then
        skipComment input (input.next pos2)
      else pos
    else pos
where
  skipComment (input : String) (pos : String.Pos.Raw) : String.Pos.Raw :=
    if pos >= strEndPos input then pos
    else if input.get pos == '\n' then skipWs input (input.next pos)
    else skipComment input (input.next pos)

private def ws : P Unit := fun s =>
  .ok ((), ⟨s.input, skipWs s.input s.pos⟩)

private def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\'' || c == '.'

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def checkChars : List Char → String → String.Pos.Raw → Option String.Pos.Raw
  | [], _, pos => some pos
  | c :: cs, input, pos =>
    if pos < strEndPos input && input.get pos == c then
      checkChars cs input (input.next pos)
    else none

private def keyword (kw : String) : P Unit := fun s =>
  let pos := skipWs s.input s.pos
  match checkChars kw.toList s.input pos with
  | none => .error s!"expected '{kw}'"
  | some pos' =>
    if pos' < strEndPos s.input && isIdentChar (s.input.get pos') then
      .error s!"expected '{kw}'"
    else
      .ok ((), ⟨s.input, pos'⟩)

private def symbol (sym : String) : P Unit := fun s =>
  let pos := skipWs s.input s.pos
  match checkChars sym.toList s.input pos with
  | none => .error s!"expected '{sym}'"
  | some pos' => .ok ((), ⟨s.input, pos'⟩)

private partial def collectIdent (input : String) (pos : String.Pos.Raw) (acc : List Char) : String × String.Pos.Raw :=
  if pos >= strEndPos input then (String.mk acc.reverse, pos)
  else
    let c := input.get pos
    if isIdentChar c then collectIdent input (input.next pos) (c :: acc)
    else (String.mk acc.reverse, pos)

private def ident : P String := fun s =>
  let pos := skipWs s.input s.pos
  if pos >= strEndPos s.input then .error "expected identifier"
  else
    let c := s.input.get pos
    if !isIdentStart c then .error s!"expected identifier, got '{c}'"
    else
      let (name, pos') := collectIdent s.input (s.input.next pos) [c]
      .ok (name, ⟨s.input, pos'⟩)

private partial def collectDigits (input : String) (pos : String.Pos.Raw) (acc : Nat) : Nat × String.Pos.Raw :=
  if pos >= strEndPos input then (acc, pos)
  else
    let c := input.get pos
    if c.isDigit then collectDigits input (input.next pos) (acc * 10 + c.toNat - '0'.toNat)
    else (acc, pos)

private def natLit : P Nat := fun s =>
  let pos := skipWs s.input s.pos
  if pos >= strEndPos s.input then .error "expected number"
  else
    let c := s.input.get pos
    if !c.isDigit then .error s!"expected number, got '{c}'"
    else
      let (n, pos') := collectDigits s.input (s.input.next pos) (c.toNat - '0'.toNat)
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
   "where", "mutual", "end", "variable"]

private def identNonReserved : P String :=
  P.bind ident fun name =>
    if reservedWords.any (· == name) then
      P.fail s!"'{name}' is a reserved word"
    else
      P.pure name

-- All parsing functions use explicit state-passing and P.bind.

mutual

private partial def parseLevel (s : PState) : Except String (SLevel × PState) :=
  match ws s with
  | .error e => .error e
  | .ok ((), s) =>
    match P.peek s with
    | .error e => .error e
    | .ok (c?, s) =>
      match c? with
      | some c =>
        if c.isDigit then
          match natLit s with
          | .error e => .error e
          | .ok (n, s) => .ok (.num n, s)
        else
          match ident s with
          | .error e => .error e
          | .ok (name, s) =>
            if name == "max" then
              match parseLevel s with
              | .error e => .error e
              | .ok (l1, s) =>
                match parseLevel s with
                | .error e => .error e
                | .ok (l2, s) => .ok (.max l1 l2, s)
            else if name == "imax" then
              match parseLevel s with
              | .error e => .error e
              | .ok (l1, s) =>
                match parseLevel s with
                | .error e => .error e
                | .ok (l2, s) => .ok (.imax l1 l2, s)
            else
              .ok (.param name, s)
      | none => .error "expected universe level"

private partial def parseAtom (s : PState) : Except String (SExpr × PState) :=
  match ws s with
  | .error e => .error e
  | .ok ((), s) =>
    match P.peek s with
    | .error e => .error e
    | .ok (c?, s) =>
      match c? with
      | none => .error "expected expression"
      | some '(' =>
        match symbol "(" s with
        | .error e => .error e
        | .ok ((), s) =>
          match parseExpr s with
          | .error e => .error e
          | .ok (e, s) =>
            match symbol ")" s with
            | .error e => .error e
            | .ok ((), s) => .ok (e, s)
      | some c =>
        if c.isDigit then
          .error "numeric literals not supported; use zero/succ"
        else if c.isAlpha || c == '_' then
          match ident s with
          | .error e => .error e
          | .ok (name, s) =>
            if name == "Sort" then
              match parseLevel s with
              | .error e => .error e
              | .ok (l, s) => .ok (.sort l, s)
            else if name == "Prop" then
              .ok (.sort (.num 0), s)
            else if name == "Type" then
              match P.tryP natLit s with
              | .error e => .error e
              | .ok (n?, s) =>
                match n? with
                | some n => .ok (.sort (.num (n + 1)), s)
                | none => .ok (.sort (.num 1), s)
            else if reservedWords.any (· == name) then
              .error s!"unexpected keyword '{name}'"
            else
              .ok (.var name, s)
        else
          .error s!"unexpected character '{c}'"

private partial def parseAppExpr (s : PState) : Except String (SExpr × PState) :=
  match parseAtom s with
  | .error e => .error e
  | .ok (head, s) =>
    match many parseAtom s with
    | .error e => .error e
    | .ok (args, s) =>
      .ok (args.foldl SExpr.app head, s)

private partial def parseArrowExpr (s : PState) : Except String (SExpr × PState) :=
  match parseAppExpr s with
  | .error e => .error e
  | .ok (lhs, s) =>
    match P.tryP (symbol "→") s with
    | .error e => .error e
    | .ok (arrow?, s) =>
      match arrow? with
      | some () =>
        match parseExpr s with
        | .error e => .error e
        | .ok (rhs, s) => .ok (.arrow lhs rhs, s)
      | none => .ok (lhs, s)

private partial def parseBinder (s : PState) : Except String (List (String × SExpr) × PState) :=
  match symbol "(" s with
  | .error e => .error e
  | .ok ((), s) =>
    match many1 identNonReserved s with
    | .error e => .error e
    | .ok (names, s) =>
      match symbol ":" s with
      | .error e => .error e
      | .ok ((), s) =>
        match parseExpr s with
        | .error e => .error e
        | .ok (ty, s) =>
          match symbol ")" s with
          | .error e => .error e
          | .ok ((), s) => .ok (names.map (·, ty), s)

private partial def parseExpr (s : PState) : Except String (SExpr × PState) :=
  match ws s with
  | .error e => .error e
  | .ok ((), s) =>
    match P.tryP (keyword "fun") s with
    | .error e => .error e
    | .ok (lam?, s) =>
      match lam? with
      | some () => parseLambda s
      | none =>
        match P.tryP (symbol "∀") s with
        | .error e => .error e
        | .ok (fa?, s) =>
          match fa? with
          | some () => parseForallE s
          | none =>
            match P.tryP (keyword "forall") s with
            | .error e => .error e
            | .ok (fa2?, s) =>
              match fa2? with
              | some () => parseForallE s
              | none =>
                match P.tryP (symbol "λ") s with
                | .error e => .error e
                | .ok (lam2?, s) =>
                  match lam2? with
                  | some () => parseLambda s
                  | none =>
                    match P.tryP (keyword "let") s with
                    | .error e => .error e
                    | .ok (let_?, s) =>
                      match let_? with
                      | some () => parseLetE s
                      | none => parseArrowExpr s

private partial def parseLambda (s : PState) : Except String (SExpr × PState) :=
  match many1 parseBinder s with
  | .error e => .error e
  | .ok (binders, s) =>
    let allBinders := binders.foldl (· ++ ·) []
    match symbol "=>" s with
    | .error e => .error e
    | .ok ((), s) =>
      match parseExpr s with
      | .error e => .error e
      | .ok (body, s) => .ok (SExpr.mkLam allBinders body, s)

private partial def parseForallE (s : PState) : Except String (SExpr × PState) :=
  match many1 parseBinder s with
  | .error e => .error e
  | .ok (binders, s) =>
    let allBinders := binders.foldl (· ++ ·) []
    match symbol "," s with
    | .error e => .error e
    | .ok ((), s) =>
      match parseExpr s with
      | .error e => .error e
      | .ok (body, s) => .ok (SExpr.mkPi allBinders body, s)

private partial def parseLetE (s : PState) : Except String (SExpr × PState) :=
  match identNonReserved s with
  | .error e => .error e
  | .ok (name, s) =>
    match symbol ":" s with
    | .error e => .error e
    | .ok ((), s) =>
      match parseExpr s with
      | .error e => .error e
      | .ok (ty, s) =>
        match symbol ":=" s with
        | .error e => .error e
        | .ok ((), s) =>
          match parseExpr s with
          | .error e => .error e
          | .ok (val, s) =>
            match keyword "in" s with
            | .error e => .error e
            | .ok ((), s) =>
              match parseExpr s with
              | .error e => .error e
              | .ok (body, s) => .ok (.letE name ty val body, s)

end -- mutual

private def parseConstructor (s : PState) : Except String (SConstructor × PState) :=
  match symbol "|" s with
  | .error e => .error e
  | .ok ((), s) =>
    match identNonReserved s with
    | .error e => .error e
    | .ok (name, s) =>
      match symbol ":" s with
      | .error e => .error e
      | .ok ((), s) =>
        match parseExpr s with
        | .error e => .error e
        | .ok (ty, s) => .ok ({ name, type := ty }, s)

private def parseUnivParams (s : PState) : Except String (List String × PState) :=
  match P.tryP (symbol ".{") s with
  | .error e => .error e
  | .ok (r?, s) =>
    match r? with
    | some () =>
      match sepBy identNonReserved (symbol ",") s with
      | .error e => .error e
      | .ok (params, s) =>
        match symbol "}" s with
        | .error e => .error e
        | .ok ((), s) => .ok (params, s)
    | none => .ok ([], s)

private def parseInductive (s : PState) : Except String (SDecl × PState) :=
  match identNonReserved s with
  | .error e => .error e
  | .ok (name, s) =>
    match parseUnivParams s with
    | .error e => .error e
    | .ok (univParams, s) =>
      match many parseBinder s with
      | .error e => .error e
      | .ok (paramBinders, s) =>
        let allParams := paramBinders.foldl (· ++ ·) []
        match symbol ":" s with
        | .error e => .error e
        | .ok ((), s) =>
          match parseExpr s with
          | .error e => .error e
          | .ok (ty, s) =>
            match keyword "where" s with
            | .error e => .error e
            | .ok ((), s) =>
              match many parseConstructor s with
              | .error e => .error e
              | .ok (ctors, s) =>
                -- Wrap type and constructor types with parameter binders
                let wrappedTy := SExpr.mkPi allParams ty
                let wrappedCtors := ctors.map fun c =>
                  { c with type := SExpr.mkPi allParams c.type }
                .ok (.inductive_ univParams (List.length allParams)
                  [{ name, type := wrappedTy, ctors := wrappedCtors }], s)

private partial def parseMutualType (s : PState) : Except String (SInductiveType × PState) :=
  match keyword "inductive" s with
  | .error e => .error e
  | .ok ((), s) =>
    match identNonReserved s with
    | .error e => .error e
    | .ok (name, s) =>
      match symbol ":" s with
      | .error e => .error e
      | .ok ((), s) =>
        match parseExpr s with
        | .error e => .error e
        | .ok (ty, s) =>
          match keyword "where" s with
          | .error e => .error e
          | .ok ((), s) =>
            match many parseConstructor s with
            | .error e => .error e
            | .ok (ctors, s) => .ok ({ name, type := ty, ctors }, s)

private def parseMutual (s : PState) : Except String (SDecl × PState) :=
  match parseUnivParams s with
  | .error e => .error e
  | .ok (univParams, s) =>
    match many1 parseMutualType s with
    | .error e => .error e
    | .ok (types, s) =>
      match keyword "end" s with
      | .error e => .error e
      | .ok ((), s) => .ok (.inductive_ univParams 0 types, s)

def parseCommand (s : PState) : Except String (Command × PState) :=
  match ws s with
  | .error e => .error e
  | .ok ((), s) =>
    match P.atEnd s with
    | .error e => .error e
    | .ok (done, s) =>
      if done then .error "empty input"
      else
        -- Try #check
        match P.tryP (symbol "#check") s with
        | .ok (some (), s) =>
          match parseExpr s with
          | .ok (e, s) => .ok (.check e, s)
          | .error e => .error e
        | _ =>
        -- Try #eval
        match P.tryP (symbol "#eval") s with
        | .ok (some (), s) =>
          match parseExpr s with
          | .ok (e, s) => .ok (.eval e, s)
          | .error e => .error e
        | _ =>
        -- Try #print
        match P.tryP (symbol "#print") s with
        | .ok (some (), s) =>
          match ident s with
          | .ok (name, s) => .ok (.print name, s)
          | .error e => .error e
        | _ =>
        -- Try axiom
        match P.tryP (keyword "axiom") s with
        | .ok (some (), s) =>
          match identNonReserved s with
          | .error e => .error e
          | .ok (name, s) =>
            match parseUnivParams s with
            | .error e => .error e
            | .ok (univParams, s) =>
              match symbol ":" s with
              | .error e => .error e
              | .ok ((), s) =>
                match parseExpr s with
                | .error e => .error e
                | .ok (ty, s) => .ok (.decl (.axiom_ name univParams ty), s)
        | _ =>
        -- Try def
        match P.tryP (keyword "def") s with
        | .ok (some (), s) =>
          match identNonReserved s with
          | .error e => .error e
          | .ok (name, s) =>
            match parseUnivParams s with
            | .error e => .error e
            | .ok (univParams, s) =>
              match symbol ":" s with
              | .error e => .error e
              | .ok ((), s) =>
                match parseExpr s with
                | .error e => .error e
                | .ok (ty, s) =>
                  match symbol ":=" s with
                  | .error e => .error e
                  | .ok ((), s) =>
                    match parseExpr s with
                    | .error e => .error e
                    | .ok (val, s) => .ok (.decl (.def_ name univParams ty val), s)
        | _ =>
        -- Try inductive
        match P.tryP (keyword "inductive") s with
        | .ok (some (), s) =>
          match parseInductive s with
          | .ok (d, s) => .ok (.decl d, s)
          | .error e => .error e
        | _ =>
        -- Try mutual
        match P.tryP (keyword "mutual") s with
        | .ok (some (), s) =>
          match parseMutual s with
          | .ok (d, s) => .ok (.decl d, s)
          | .error e => .error e
        | _ =>
        .error "expected command (axiom, def, inductive, mutual, #check, #eval, #print)"

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
