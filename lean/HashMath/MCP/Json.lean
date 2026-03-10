/-
  HashMath.MCP.Json — Minimal JSON type, parser, and printer for MCP protocol
-/

namespace HashMath.MCP

/-- JSON value type. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : List Json)
  | obj (fields : List (String × Json))
  deriving Inhabited, BEq

namespace Json

/-- Access a field by key in a JSON object. -/
def field? : Json → String → Option Json
  | obj fields, key => fields.lookup key
  | _, _ => none

/-- Extract a string value. -/
def asStr? : Json → Option String
  | str s => some s
  | _ => none

/-- Extract an integer value. -/
def asNum? : Json → Option Int
  | num n => some n
  | _ => none

/-- Extract a boolean value. -/
def asBool? : Json → Option Bool
  | bool b => some b
  | _ => none

/-- Extract an array. -/
def asArr? : Json → Option (List Json)
  | arr xs => some xs
  | _ => none

/-- Extract an object's fields. -/
def asObj? : Json → Option (List (String × Json))
  | obj fs => some fs
  | _ => none

/-- Get field as string, with default. -/
def fieldStr (j : Json) (key : String) (default : String := "") : String :=
  match j.field? key with
  | some (str s) => s
  | _ => default

/-- Get field as bool, with default. -/
def fieldBool (j : Json) (key : String) (default : Bool := false) : Bool :=
  match j.field? key with
  | some (bool b) => b
  | _ => default

-- ═══════════════════════════════════════════════
-- JSON Printer
-- ═══════════════════════════════════════════════

private def escapeChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.toNat < 0x20 then
    let n := c.toNat
    let hex := "0123456789abcdef"
    let hi := hex.get ⟨n / 16⟩
    let lo := hex.get ⟨n % 16⟩
    "\\u00" ++ hi.toString ++ lo.toString
  else
    c.toString

private def escapeString (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeChar c) ""

/-- Render JSON value to a compact string (no whitespace). -/
partial def render : Json → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .num n =>
    if n ≥ 0 then toString n.natAbs
    else "-" ++ toString n.natAbs
  | .str s => "\"" ++ escapeString s ++ "\""
  | .arr xs => "[" ++ String.intercalate "," (xs.map render) ++ "]"
  | .obj fields =>
    let entries := fields.map fun (k, v) =>
      "\"" ++ escapeString k ++ "\":" ++ render v
    "{" ++ String.intercalate "," entries ++ "}"

instance : ToString Json := ⟨Json.render⟩

-- ═══════════════════════════════════════════════
-- JSON Parser
-- ═══════════════════════════════════════════════

private structure JP where
  input : String
  pos : String.Pos.Raw
  deriving Repr

private def jpEnd (s : JP) : String.Pos.Raw := ⟨s.input.utf8ByteSize⟩

private def jpAtEnd (s : JP) : Bool := s.pos >= jpEnd s

private def jpPeek (s : JP) : Option Char :=
  if jpAtEnd s then none
  else some (s.input.get s.pos)

private def jpNext (s : JP) : JP :=
  if jpAtEnd s then s
  else { s with pos := s.input.next s.pos }

private def jpSkipWS (s : JP) : JP :=
  let rec go (s : JP) (fuel : Nat) : JP :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      match jpPeek s with
      | some ' ' | some '\n' | some '\r' | some '\t' => go (jpNext s) fuel
      | _ => s
  go s s.input.utf8ByteSize

private def jpExpect (s : JP) (c : Char) : Except String JP :=
  match jpPeek s with
  | some c' => if c' == c then .ok (jpNext s) else .error s!"expected '{c}', got '{c'}'"
  | none => .error s!"expected '{c}', got EOF"

private def jpExpectStr (s : JP) (expected : String) : Except String JP :=
  let rec go (s : JP) (i : Nat) : Except String JP :=
    if i >= expected.length then .ok s
    else match jpPeek s with
      | some c =>
        if c == expected.get ⟨i⟩ then go (jpNext s) (i + 1)
        else .error s!"expected '{expected}'"
      | none => .error s!"expected '{expected}', got EOF"
  go s 0

private def hexDigitVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseHex4 (s : JP) : Except String (Nat × JP) :=
  let rec go (s : JP) (remaining : Nat) (acc : Nat) : Except String (Nat × JP) :=
    match remaining with
    | 0 => .ok (acc, s)
    | n + 1 =>
      match jpPeek s with
      | some c =>
        match hexDigitVal c with
        | some d => go (jpNext s) n (acc * 16 + d)
        | none => .error "invalid hex escape"
      | none => .error "unterminated \\u escape"
  go s 4 0

private partial def jpParseString (s : JP) : Except String (String × JP) := do
  let s ← jpExpect s '"'
  let rec go (s : JP) (acc : String) : Except String (String × JP) :=
    match jpPeek s with
    | none => .error "unterminated string"
    | some '"' => .ok (acc, jpNext s)
    | some '\\' =>
      let s := jpNext s
      match jpPeek s with
      | none => .error "unterminated escape"
      | some '"' => go (jpNext s) (acc ++ "\"")
      | some '\\' => go (jpNext s) (acc ++ "\\")
      | some '/' => go (jpNext s) (acc ++ "/")
      | some 'n' => go (jpNext s) (acc ++ "\n")
      | some 'r' => go (jpNext s) (acc ++ "\r")
      | some 't' => go (jpNext s) (acc ++ "\t")
      | some 'b' => go (jpNext s) (acc.push (Char.ofNat 8))
      | some 'f' => go (jpNext s) (acc.push (Char.ofNat 12))
      | some 'u' =>
        let s := jpNext s
        match parseHex4 s with
        | .ok (val, s) => go s (acc.push (Char.ofNat val))
        | .error e => .error e
      | some c => .error s!"unknown escape '\\{c}'"
    | some c => go (jpNext s) (acc.push c)
  go s ""

private def skipDigitsAfterDot (s : JP) : JP :=
  let rec go (s : JP) (fuel : Nat) : JP :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      match jpPeek s with
      | some c => if '0' ≤ c && c ≤ '9' then go (jpNext s) fuel else s
      | none => s
  go s s.input.utf8ByteSize

private partial def jpParseNumber (s : JP) : Except String (Int × JP) := do
  let (neg, s) := match jpPeek s with
    | some '-' => (true, jpNext s)
    | _ => (false, s)
  let rec digits (s : JP) (acc : Nat) (any : Bool) : Except String (Nat × Bool × JP) :=
    match jpPeek s with
    | some c =>
      if '0' ≤ c && c ≤ '9' then
        digits (jpNext s) (acc * 10 + (c.toNat - '0'.toNat)) true
      else .ok (acc, any, s)
    | none => .ok (acc, any, s)
  let (n, any, s) ← digits s 0 false
  if !any then .error "expected digit"
  -- Skip optional fractional part
  let s := match jpPeek s with
    | some '.' => skipDigitsAfterDot (jpNext s)
    | _ => s
  -- Skip optional exponent
  let s := match jpPeek s with
    | some 'e' | some 'E' =>
      let s := jpNext s
      let s := match jpPeek s with
        | some '+' | some '-' => jpNext s
        | _ => s
      skipDigitsAfterDot s
    | _ => s
  let val : Int := if neg then -↑n else ↑n
  .ok (val, s)

-- Mutual: parseValue, parseObject, parseArray

mutual

private partial def parseValue (s : JP) : Except String (Json × JP) :=
  let s := jpSkipWS s
  match jpPeek s with
  | none => .error "unexpected end of input"
  | some '"' =>
    match jpParseString s with
    | .ok (sv, s) => .ok (.str sv, s)
    | .error e => .error e
  | some '{' => parseObject (jpNext s)
  | some '[' => parseArray (jpNext s)
  | some 't' => match jpExpectStr s "true" with
    | .ok s => .ok (.bool true, s)
    | .error e => .error e
  | some 'f' => match jpExpectStr s "false" with
    | .ok s => .ok (.bool false, s)
    | .error e => .error e
  | some 'n' => match jpExpectStr s "null" with
    | .ok s => .ok (.null, s)
    | .error e => .error e
  | some c =>
    if c == '-' || ('0' ≤ c && c ≤ '9') then
      match jpParseNumber s with
      | .ok (n, s) => .ok (.num n, s)
      | .error e => .error e
    else .error s!"unexpected character '{c}'"

private partial def parseObject (s : JP) : Except String (Json × JP) :=
  let s := jpSkipWS s
  match jpPeek s with
  | some '}' => .ok (.obj [], jpNext s)
  | _ => parseObjectFields s []

private partial def parseObjectFields (s : JP) (acc : List (String × Json)) :
    Except String (Json × JP) :=
  let s := jpSkipWS s
  match jpParseString s with
  | .error e => .error e
  | .ok (key, s) =>
    let s := jpSkipWS s
    match jpExpect s ':' with
    | .error e => .error e
    | .ok s =>
      match parseValue s with
      | .error e => .error e
      | .ok (val, s) =>
        let acc := acc ++ [(key, val)]
        let s := jpSkipWS s
        match jpPeek s with
        | some ',' => parseObjectFields (jpNext s) acc
        | some '}' => .ok (.obj acc, jpNext s)
        | _ => .error "expected ',' or '}'"

private partial def parseArray (s : JP) : Except String (Json × JP) :=
  let s := jpSkipWS s
  match jpPeek s with
  | some ']' => .ok (.arr [], jpNext s)
  | _ => parseArrayElems s []

private partial def parseArrayElems (s : JP) (acc : List Json) :
    Except String (Json × JP) :=
  match parseValue s with
  | .error e => .error e
  | .ok (val, s) =>
    let acc := acc ++ [val]
    let s := jpSkipWS s
    match jpPeek s with
    | some ',' => parseArrayElems (jpSkipWS (jpNext s)) acc
    | some ']' => .ok (.arr acc, jpNext s)
    | _ => .error "expected ',' or ']'"

end

/-- Parse a JSON value from a string. -/
def parse (input : String) : Except String Json :=
  match parseValue (jpSkipWS ⟨input, ⟨0⟩⟩) with
  | .ok (j, _) => .ok j
  | .error e => .error e

-- ═══════════════════════════════════════════════
-- Convenience constructors
-- ═══════════════════════════════════════════════

/-- Build a JSON-RPC response. -/
def rpcResult (id : Json) (result : Json) : Json :=
  .obj [("jsonrpc", .str "2.0"), ("id", id), ("result", result)]

/-- Build a JSON-RPC error response. -/
def rpcError (id : Json) (code : Int) (message : String) : Json :=
  .obj [("jsonrpc", .str "2.0"), ("id", id),
        ("error", .obj [("code", .num code), ("message", .str message)])]

end Json
end HashMath.MCP
