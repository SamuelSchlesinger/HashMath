/-
  HashMath.Subterm — Subterm hash-consing for content-addressed expression storage

  Provides `shatter` and `reassemble` to convert between kernel expressions
  (`Expr Empty`, where `href` is unconstructable) and stored expressions
  (`Expr Hash`, where large subterms are replaced by hash references).

  Size threshold: subterms whose serialized size exceeds 33 bytes
  (1-byte tag + 32-byte hash = cost of an href node) are replaced.
-/

import HashMath.Hash
import Std.Data.HashMap

namespace HashMath

/-- The size threshold: only hash-reference subterms larger than this.
    An href node costs 1 tag byte + 32 hash bytes = 33 bytes in the wire format. -/
private def hrefThreshold : Nat := 33

/-- Estimate the serialized size of an expression (without actually serializing).
    This mirrors the structure of `serializeExpr` but only counts bytes. -/
def exprSerializedSize : Expr → Nat
  | .bvar n => 1 + lebSize n
  | .sort l => 1 + levelSerializedSize l
  | .const _h ls => 1 + 32 + lebSize ls.length + ls.foldl (fun acc l => acc + levelSerializedSize l) 0
  | .app f a => 1 + exprSerializedSize f + exprSerializedSize a
  | .lam ty body => 1 + exprSerializedSize ty + exprSerializedSize body
  | .forallE ty body => 1 + exprSerializedSize ty + exprSerializedSize body
  | .letE ty val body => 1 + exprSerializedSize ty + exprSerializedSize val + exprSerializedSize body
  | .proj _h i s => 1 + 32 + lebSize i + exprSerializedSize s
  | .iref idx ls => 1 + lebSize idx + lebSize ls.length + ls.foldl (fun acc l => acc + levelSerializedSize l) 0
  | .href a => nomatch a
where
  /-- Size of a LEB128-encoded natural number. -/
  lebSize (n : Nat) : Nat :=
    if n < 128 then 1
    else 1 + lebSize (n / 128)
  termination_by n
  /-- Serialized size of a universe level. -/
  levelSerializedSize : Level → Nat
    | .zero => 1
    | .succ l => 1 + levelSerializedSize l
    | .max l₁ l₂ => 1 + levelSerializedSize l₁ + levelSerializedSize l₂
    | .imax l₁ l₂ => 1 + levelSerializedSize l₁ + levelSerializedSize l₂
    | .param n => 1 + lebSize n

/-- A store mapping hashes to the serialized kernel expressions they represent. -/
abbrev SubtermStore := Std.HashMap Hash ByteArray

/-- Shatter a kernel expression: replace subterms larger than the threshold
    with `href` hash-references, collecting the extracted subterms.
    Returns the shattered expression and a map of hash → serialized bytes. -/
def shatter (e : Expr) : Expr Hash × SubtermStore :=
  go e {}
where
  go (e : Expr) (store : SubtermStore) : Expr Hash × SubtermStore :=
    let size := exprSerializedSize e
    if size ≤ hrefThreshold then
      -- Small enough to inline — convert to Expr Hash without href
      (e.embed, store)
    else
      -- Recursively shatter children first
      let (_e', store') := goChildren e store
      -- Now store this node and replace with href
      let h := hashExpr e
      let serialized := serializeExpr e
      let store'' := store'.insert h serialized
      (.href h, store'')
  goChildren (e : Expr) (store : SubtermStore) : Expr Hash × SubtermStore :=
    match e with
    | .bvar n => (.bvar n, store)
    | .sort l => (.sort l, store)
    | .const h ls => (.const h ls, store)
    | .iref idx ls => (.iref idx ls, store)
    | .href a => nomatch a
    | .app f a =>
      let (f', s1) := go f store
      let (a', s2) := go a s1
      (.app f' a', s2)
    | .lam ty body =>
      let (ty', s1) := go ty store
      let (body', s2) := go body s1
      (.lam ty' body', s2)
    | .forallE ty body =>
      let (ty', s1) := go ty store
      let (body', s2) := go body s1
      (.forallE ty' body', s2)
    | .letE ty val body =>
      let (ty', s1) := go ty store
      let (val', s2) := go val s1
      let (body', s3) := go body s2
      (.letE ty' val' body', s3)
    | .proj h i s =>
      let (s', st) := go s store
      (.proj h i s', st)

/-- Reassemble a stored expression: resolve all `href` nodes back to
    full kernel expressions using the subterm store.
    Returns `none` if any hash reference can't be resolved. -/
partial def reassemble (e : Expr Hash) (store : SubtermStore) : Option Expr :=
  match e with
  | .bvar n => some (.bvar n)
  | .sort l => some (.sort l)
  | .const h ls => some (.const h ls)
  | .iref idx ls => some (.iref idx ls)
  | .href h => do
    let bytes ← store[h]?
    let (expr, _) ← deserializeExpr (DesCursor.ofData bytes)
    some expr
  | .app f a => do
    let f' ← reassemble f store
    let a' ← reassemble a store
    some (.app f' a')
  | .lam ty body => do
    let ty' ← reassemble ty store
    let body' ← reassemble body store
    some (.lam ty' body')
  | .forallE ty body => do
    let ty' ← reassemble ty store
    let body' ← reassemble body store
    some (.forallE ty' body')
  | .letE ty val body => do
    let ty' ← reassemble ty store
    let val' ← reassemble val store
    let body' ← reassemble body store
    some (.letE ty' val' body')
  | .proj h i s => do
    let s' ← reassemble s store
    some (.proj h i s')

/-- Serialize a stored expression (Expr Hash) to bytes.
    href nodes are serialized as tag 0x19 + 32-byte hash. -/
def serializeStoredExpr : Expr Hash → ByteArray
  | .bvar n => serByte Tag.exprBvar ++ serNat n
  | .sort l => serByte Tag.exprSort ++ serializeLevel l
  | .const h ls =>
    serByte Tag.exprConst ++ serHash h ++ serNat ls.length ++
    ByteArray.concatList (ls.map serializeLevel)
  | .app f a => serByte Tag.exprApp ++ serializeStoredExpr f ++ serializeStoredExpr a
  | .lam ty body => serByte Tag.exprLam ++ serializeStoredExpr ty ++ serializeStoredExpr body
  | .forallE ty body => serByte Tag.exprForallE ++ serializeStoredExpr ty ++ serializeStoredExpr body
  | .letE ty val body =>
    serByte Tag.exprLetE ++ serializeStoredExpr ty ++ serializeStoredExpr val ++ serializeStoredExpr body
  | .proj h i s => serByte Tag.exprProj ++ serHash h ++ serNat i ++ serializeStoredExpr s
  | .iref idx ls =>
    serByte Tag.exprIRef ++ serNat idx ++ serNat ls.length ++
    ByteArray.concatList (ls.map serializeLevel)
  | .href h => serByte Tag.exprHRef ++ serHash h

/-- Deserialize a stored expression (Expr Hash) from bytes.
    Recognizes tag 0x19 as href nodes. -/
partial def deserializeStoredExpr (c : DesCursor) : Option (Expr Hash × DesCursor) := do
  let (tag, c) ← c.readByte
  if tag == Tag.exprBvar then do
    let (n, c) ← c.readNat
    some (.bvar n, c)
  else if tag == Tag.exprSort then do
    let (l, c) ← deserializeLevel c
    some (.sort l, c)
  else if tag == Tag.exprConst then do
    let (h, c) ← c.readHash
    let (nLevels, c) ← c.readNat
    let (ls, c) ← readList c nLevels deserializeLevel
    some (.const h ls, c)
  else if tag == Tag.exprApp then do
    let (f, c) ← deserializeStoredExpr c
    let (a, c) ← deserializeStoredExpr c
    some (.app f a, c)
  else if tag == Tag.exprLam then do
    let (ty, c) ← deserializeStoredExpr c
    let (body, c) ← deserializeStoredExpr c
    some (.lam ty body, c)
  else if tag == Tag.exprForallE then do
    let (ty, c) ← deserializeStoredExpr c
    let (body, c) ← deserializeStoredExpr c
    some (.forallE ty body, c)
  else if tag == Tag.exprLetE then do
    let (ty, c) ← deserializeStoredExpr c
    let (val, c) ← deserializeStoredExpr c
    let (body, c) ← deserializeStoredExpr c
    some (.letE ty val body, c)
  else if tag == Tag.exprProj then do
    let (h, c) ← c.readHash
    let (i, c) ← c.readNat
    let (s, c) ← deserializeStoredExpr c
    some (.proj h i s, c)
  else if tag == Tag.exprIRef then do
    let (idx, c) ← c.readNat
    let (nLevels, c) ← c.readNat
    let (ls, c) ← readList c nLevels deserializeLevel
    some (.iref idx ls, c)
  else if tag == Tag.exprHRef then do
    let (h, c) ← c.readHash
    some (.href h, c)
  else none
where
  readList {β : Type} (c : DesCursor) (n : Nat) (readOne : DesCursor → Option (β × DesCursor))
      : Option (List β × DesCursor) :=
    match n with
    | 0 => some ([], c)
    | n + 1 => do
      let (x, c') ← readOne c
      let (xs, c'') ← readList c' n readOne
      some (x :: xs, c'')

-- ═══════════════════════════════════════════════════════════════════
-- Declaration-level shatter/reassemble (for DHT publish/fetch)
-- ═══════════════════════════════════════════════════════════════════

private def mergeStores (s1 s2 : SubtermStore) : SubtermStore :=
  s1.fold (init := s2) fun acc k v => acc.insert k v

/-- Shatter all expressions in a declaration and serialize in stored format.
    Returns the stored-format bytes (expressions may contain href tags)
    and the SubtermStore of extracted subterms. -/
def shatterDecl (d : Decl) : ByteArray × SubtermStore :=
  match d with
  | .axiom n ty =>
    let (sty, store) := shatter ty
    (serByte Tag.declAxiom ++ serNat n ++ serializeStoredExpr sty, store)
  | .definition n ty val =>
    let (sty, store1) := shatter ty
    let (sval, store2) := shatter val
    (serByte Tag.declDefinition ++ serNat n ++
      serializeStoredExpr sty ++ serializeStoredExpr sval,
     mergeStores store1 store2)
  | .inductive block =>
    let (blockBytes, store) := shatterBlock block
    (serByte Tag.declInductive ++ blockBytes, store)
  | .quotient kind =>
    (serByte Tag.declQuotient ++ serByte (serializeQuotKind kind), {})
where
  shatterBlock (block : InductiveBlock) : ByteArray × SubtermStore :=
    let (typesBytes, store) := shatterTypes block.types {}
    (serNat block.numUnivParams ++ serNat block.numParams ++
      serNat block.types.length ++ typesBytes ++ serBool block.isUnsafe,
     store)
  shatterTypes : List InductiveType → SubtermStore → ByteArray × SubtermStore
    | [], store => (ByteArray.empty, store)
    | it :: rest, store =>
      let (itBytes, store1) := shatterIndType it store
      let (restBytes, store2) := shatterTypes rest store1
      (itBytes ++ restBytes, store2)
  shatterIndType (it : InductiveType) (store : SubtermStore) : ByteArray × SubtermStore :=
    let (sty, store1) := shatter it.type
    let store1 := mergeStores store store1
    let (ctorsBytes, store2) := shatterCtors it.ctors store1
    (serializeStoredExpr sty ++ serNat it.ctors.length ++ ctorsBytes, store2)
  shatterCtors : List Expr → SubtermStore → ByteArray × SubtermStore
    | [], store => (ByteArray.empty, store)
    | c :: rest, store =>
      let (sc, store1) := shatter c
      let store1 := mergeStores store store1
      let (restBytes, store2) := shatterCtors rest store1
      (serializeStoredExpr sc ++ restBytes, store2)

/-- Deserialize a stored-format declaration and reassemble all href references.
    The stored format uses the same tags as canonical declarations but
    expressions may contain href (0x19) nodes. Subterm bytes are looked up
    in the provided store and deserialized as canonical expressions.
    This is backward-compatible: canonical-format bytes (no hrefs) also work. -/
partial def reassembleStoredDecl (bs : ByteArray) (store : SubtermStore) : Option Decl := do
  let c := DesCursor.ofData bs
  let (tag, c) ← c.readByte
  if tag == Tag.declAxiom then
    let (n, c) ← c.readNat
    let (sty, _) ← deserializeStoredExpr c
    let ty ← reassemble sty store
    some (.axiom n ty)
  else if tag == Tag.declDefinition then
    let (n, c) ← c.readNat
    let (sty, c) ← deserializeStoredExpr c
    let (sval, _) ← deserializeStoredExpr c
    let ty ← reassemble sty store
    let val ← reassemble sval store
    some (.definition n ty val)
  else if tag == Tag.declInductive then
    let (block, _) ← reassembleBlock c store
    some (.inductive block)
  else if tag == Tag.declQuotient then
    let (kind, _) ← deserializeQuotKind c
    some (.quotient kind)
  else none
where
  reassembleBlock (c : DesCursor) (store : SubtermStore)
      : Option (InductiveBlock × DesCursor) := do
    let (numUnivParams, c) ← c.readNat
    let (numParams, c) ← c.readNat
    let (nTypes, c) ← c.readNat
    let (types, c) ← reassembleTypes c nTypes store
    let (isUnsafe, c) ← c.readBool
    some (⟨numUnivParams, numParams, types, isUnsafe⟩, c)
  reassembleTypes (c : DesCursor) (n : Nat) (store : SubtermStore)
      : Option (List InductiveType × DesCursor) :=
    match n with
    | 0 => some ([], c)
    | n + 1 => do
      let (it, c) ← reassembleIndType c store
      let (rest, c) ← reassembleTypes c n store
      some (it :: rest, c)
  reassembleIndType (c : DesCursor) (store : SubtermStore)
      : Option (InductiveType × DesCursor) := do
    let (sty, c) ← deserializeStoredExpr c
    let ty ← reassemble sty store
    let (nCtors, c) ← c.readNat
    let (ctors, c) ← reassembleCtors c nCtors store
    some (⟨ty, ctors⟩, c)
  reassembleCtors (c : DesCursor) (n : Nat) (store : SubtermStore)
      : Option (List Expr × DesCursor) :=
    match n with
    | 0 => some ([], c)
    | n + 1 => do
      let (sc, c) ← deserializeStoredExpr c
      let e ← reassemble sc store
      let (rest, c) ← reassembleCtors c n store
      some (e :: rest, c)

/-- Collect all href hashes from stored-format declaration bytes.
    Parses the stored format and extracts every href hash found in expressions. -/
partial def collectStoredDeclHRefs (bs : ByteArray) : List Hash :=
  match go bs with
  | some hs => hs.eraseDups
  | none => []
where
  collectFromExpr : Expr Hash → List Hash
    | .href h => [h]
    | .app f a => collectFromExpr f ++ collectFromExpr a
    | .lam ty body => collectFromExpr ty ++ collectFromExpr body
    | .forallE ty body => collectFromExpr ty ++ collectFromExpr body
    | .letE ty val body =>
      collectFromExpr ty ++ collectFromExpr val ++ collectFromExpr body
    | .proj _ _ s => collectFromExpr s
    | _ => []
  go (bs : ByteArray) : Option (List Hash) := do
    let c := DesCursor.ofData bs
    let (tag, c) ← c.readByte
    if tag == Tag.declAxiom then
      let (_, c) ← c.readNat
      let (sty, _) ← deserializeStoredExpr c
      some (collectFromExpr sty)
    else if tag == Tag.declDefinition then
      let (_, c) ← c.readNat
      let (sty, c) ← deserializeStoredExpr c
      let (sval, _) ← deserializeStoredExpr c
      some (collectFromExpr sty ++ collectFromExpr sval)
    else if tag == Tag.declInductive then
      let (_, c) ← c.readNat  -- numUnivParams
      let (_, c) ← c.readNat  -- numParams
      let (nTypes, c) ← c.readNat
      goTypes c nTypes
    else
      some []
  goTypes (c : DesCursor) : Nat → Option (List Hash)
    | 0 => some []
    | n + 1 => do
      let (sty, c) ← deserializeStoredExpr c
      let (nCtors, c) ← c.readNat
      let (ctorHRefs, c) ← goCtors c nCtors
      let rest ← goTypes c n
      some (collectFromExpr sty ++ ctorHRefs ++ rest)
  goCtors (c : DesCursor) : Nat → Option (List Hash × DesCursor)
    | 0 => some ([], c)
    | n + 1 => do
      let (sc, c) ← deserializeStoredExpr c
      let (rest, c) ← goCtors c n
      some (collectFromExpr sc ++ rest, c)

end HashMath
