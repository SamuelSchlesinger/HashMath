/-
  HashMath.Serialize — Canonical binary serialization for HashMath CIC terms
-/

import HashMath.Decl

namespace HashMath

-- Tags for domain separation in serialization/hashing.
namespace Tag
  -- Level tags
  def levelZero  : UInt8 := 0x00
  def levelSucc  : UInt8 := 0x01
  def levelMax   : UInt8 := 0x02
  def levelIMax  : UInt8 := 0x03
  def levelParam : UInt8 := 0x04

  -- Expr tags
  def exprBvar    : UInt8 := 0x10
  def exprSort    : UInt8 := 0x11
  def exprConst   : UInt8 := 0x12
  def exprApp     : UInt8 := 0x13
  def exprLam     : UInt8 := 0x14
  def exprForallE : UInt8 := 0x15
  def exprLetE    : UInt8 := 0x16
  def exprProj    : UInt8 := 0x17
  def exprIRef    : UInt8 := 0x18

  -- Decl tags
  def declAxiom      : UInt8 := 0x20
  def declDefinition : UInt8 := 0x21
  def declInductive  : UInt8 := 0x22
  def declQuotient   : UInt8 := 0x23

  -- Derived entity tags (for Merkle hashing of inductive sub-entities)
  def indType   : UInt8 := 0x30
  def indCtor   : UInt8 := 0x31
  def indRec    : UInt8 := 0x32
end Tag

/-- Serialize a single byte. -/
def serByte (b : UInt8) : ByteArray :=
  ByteArray.mk #[b]

/-- Serialize a Nat as LEB128. -/
def serNat (n : Nat) : ByteArray :=
  encodeLEB128 n

/-- Serialize a Bool as a single byte (0x01 for true, 0x00 for false). -/
def serBool (b : Bool) : ByteArray :=
  ByteArray.mk #[if b then 0x01 else 0x00]

/-- Serialize a Hash (fixed 32 bytes). -/
def serHash (h : Hash) : ByteArray :=
  h.bytes

/-- Serialize a universe level to its canonical byte representation. -/
def serializeLevel : Level → ByteArray
  | .zero => serByte Tag.levelZero
  | .succ l => serByte Tag.levelSucc ++ serializeLevel l
  | .max l₁ l₂ => serByte Tag.levelMax ++ serializeLevel l₁ ++ serializeLevel l₂
  | .imax l₁ l₂ => serByte Tag.levelIMax ++ serializeLevel l₁ ++ serializeLevel l₂
  | .param n => serByte Tag.levelParam ++ serNat n

/-- Serialize an expression to its canonical byte representation. -/
def serializeExpr : Expr → ByteArray
  | .bvar n => serByte Tag.exprBvar ++ serNat n
  | .sort l => serByte Tag.exprSort ++ serializeLevel l
  | .const h ls =>
    serByte Tag.exprConst ++ serHash h ++ serNat ls.length ++
    ByteArray.concatList (ls.map serializeLevel)
  | .app f a => serByte Tag.exprApp ++ serializeExpr f ++ serializeExpr a
  | .lam ty body => serByte Tag.exprLam ++ serializeExpr ty ++ serializeExpr body
  | .forallE ty body => serByte Tag.exprForallE ++ serializeExpr ty ++ serializeExpr body
  | .letE ty val body =>
    serByte Tag.exprLetE ++ serializeExpr ty ++ serializeExpr val ++ serializeExpr body
  | .proj h i s => serByte Tag.exprProj ++ serHash h ++ serNat i ++ serializeExpr s
  | .iref idx ls =>
    serByte Tag.exprIRef ++ serNat idx ++ serNat ls.length ++
    ByteArray.concatList (ls.map serializeLevel)

/-- Serialize a QuotKind to a single byte. -/
def serializeQuotKind : QuotKind → UInt8
  | .quot => 0x00
  | .quotMk => 0x01
  | .quotLift => 0x02
  | .quotInd => 0x03

/-- Serialize an InductiveType. -/
def serializeInductiveType (it : InductiveType) : ByteArray :=
  serializeExpr it.type ++
  serNat it.ctors.length ++
  ByteArray.concatList (it.ctors.map serializeExpr)

/-- Serialize an InductiveBlock. -/
def serializeInductiveBlock (block : InductiveBlock) : ByteArray :=
  serNat block.numUnivParams ++
  serNat block.numParams ++
  serNat block.types.length ++
  ByteArray.concatList (block.types.map serializeInductiveType) ++
  serBool block.isUnsafe

/-- Serialize a declaration to its canonical byte representation. -/
def serializeDecl : Decl → ByteArray
  | .axiom n ty =>
    serByte Tag.declAxiom ++ serNat n ++ serializeExpr ty
  | .definition n ty val =>
    serByte Tag.declDefinition ++ serNat n ++ serializeExpr ty ++ serializeExpr val
  | .inductive block =>
    serByte Tag.declInductive ++ serializeInductiveBlock block
  | .quotient kind =>
    serByte Tag.declQuotient ++ serByte (serializeQuotKind kind)

-- ═══════════════════════════════════════════════════════════════════
-- Deserialization
-- ═══════════════════════════════════════════════════════════════════

/-- A cursor for reading from a ByteArray. -/
structure DesCursor where
  data : ByteArray
  pos : Nat

namespace DesCursor

def ofData (data : ByteArray) : DesCursor := ⟨data, 0⟩

def remaining (c : DesCursor) : Nat :=
  if c.pos ≥ c.data.size then 0 else c.data.size - c.pos

def readByte (c : DesCursor) : Option (UInt8 × DesCursor) :=
  if c.pos < c.data.size then
    some (c.data.get! c.pos, ⟨c.data, c.pos + 1⟩)
  else none

def readBytes (c : DesCursor) (n : Nat) : Option (ByteArray × DesCursor) :=
  if c.pos + n ≤ c.data.size then
    some (c.data.extract c.pos (c.pos + n), ⟨c.data, c.pos + n⟩)
  else none

def readHash (c : DesCursor) : Option (Hash × DesCursor) := do
  let (bs, c') ← c.readBytes 32
  if h : bs.size = 32 then
    some (⟨bs, h⟩, c')
  else none

def readNat (c : DesCursor) : Option (Nat × DesCursor) := do
  let (n, newPos) ← decodeLEB128 c.data c.pos
  some (n, ⟨c.data, newPos⟩)

def readBool (c : DesCursor) : Option (Bool × DesCursor) := do
  let (b, c') ← c.readByte
  some (b != 0, c')

end DesCursor

private def readList (c : DesCursor) (n : Nat) (readOne : DesCursor → Option (α × DesCursor))
    : Option (List α × DesCursor) :=
  match n with
  | 0 => some ([], c)
  | n + 1 => do
    let (x, c') ← readOne c
    let (xs, c'') ← readList c' n readOne
    some (x :: xs, c'')

/-- Deserialize a universe level. -/
partial def deserializeLevel (c : DesCursor) : Option (Level × DesCursor) := do
  let (tag, c) ← c.readByte
  if tag == Tag.levelZero then
    some (.zero, c)
  else if tag == Tag.levelSucc then do
    let (l, c) ← deserializeLevel c
    some (.succ l, c)
  else if tag == Tag.levelMax then do
    let (l₁, c) ← deserializeLevel c
    let (l₂, c) ← deserializeLevel c
    some (.max l₁ l₂, c)
  else if tag == Tag.levelIMax then do
    let (l₁, c) ← deserializeLevel c
    let (l₂, c) ← deserializeLevel c
    some (.imax l₁ l₂, c)
  else if tag == Tag.levelParam then do
    let (n, c) ← c.readNat
    some (.param n, c)
  else none

/-- Deserialize an expression. -/
partial def deserializeExpr (c : DesCursor) : Option (Expr × DesCursor) := do
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
    let (f, c) ← deserializeExpr c
    let (a, c) ← deserializeExpr c
    some (.app f a, c)
  else if tag == Tag.exprLam then do
    let (ty, c) ← deserializeExpr c
    let (body, c) ← deserializeExpr c
    some (.lam ty body, c)
  else if tag == Tag.exprForallE then do
    let (ty, c) ← deserializeExpr c
    let (body, c) ← deserializeExpr c
    some (.forallE ty body, c)
  else if tag == Tag.exprLetE then do
    let (ty, c) ← deserializeExpr c
    let (val, c) ← deserializeExpr c
    let (body, c) ← deserializeExpr c
    some (.letE ty val body, c)
  else if tag == Tag.exprProj then do
    let (h, c) ← c.readHash
    let (i, c) ← c.readNat
    let (s, c) ← deserializeExpr c
    some (.proj h i s, c)
  else if tag == Tag.exprIRef then do
    let (idx, c) ← c.readNat
    let (nLevels, c) ← c.readNat
    let (ls, c) ← readList c nLevels deserializeLevel
    some (.iref idx ls, c)
  else none

/-- Deserialize a QuotKind. -/
def deserializeQuotKind (c : DesCursor) : Option (QuotKind × DesCursor) := do
  let (b, c) ← c.readByte
  if b == 0x00 then some (.quot, c)
  else if b == 0x01 then some (.quotMk, c)
  else if b == 0x02 then some (.quotLift, c)
  else if b == 0x03 then some (.quotInd, c)
  else none

/-- Deserialize an InductiveType. -/
def deserializeInductiveType (c : DesCursor) : Option (InductiveType × DesCursor) := do
  let (ty, c) ← deserializeExpr c
  let (nCtors, c) ← c.readNat
  let (ctors, c) ← readList c nCtors deserializeExpr
  some (⟨ty, ctors⟩, c)

/-- Deserialize an InductiveBlock. -/
def deserializeInductiveBlock (c : DesCursor) : Option (InductiveBlock × DesCursor) := do
  let (numUnivParams, c) ← c.readNat
  let (numParams, c) ← c.readNat
  let (nTypes, c) ← c.readNat
  let (types, c) ← readList c nTypes deserializeInductiveType
  let (isUnsafe, c) ← c.readBool
  some (⟨numUnivParams, numParams, types, isUnsafe⟩, c)

/-- Deserialize a declaration from its canonical byte representation. -/
def deserializeDecl (bs : ByteArray) : Option Decl :=
  let c := DesCursor.ofData bs
  match c.readByte with
  | none => none
  | some (tag, c) =>
    if tag == Tag.declAxiom then do
      let (n, c) ← c.readNat
      let (ty, _) ← deserializeExpr c
      some (.axiom n ty)
    else if tag == Tag.declDefinition then do
      let (n, c) ← c.readNat
      let (ty, c) ← deserializeExpr c
      let (val, _) ← deserializeExpr c
      some (.definition n ty val)
    else if tag == Tag.declInductive then do
      let (block, _) ← deserializeInductiveBlock c
      some (.inductive block)
    else if tag == Tag.declQuotient then do
      -- serializeDecl writes: 0x23 ++ serByte(serializeQuotKind kind)
      -- Tag 0x23 already consumed; deserializeQuotKind reads the next byte
      let (kind, _) ← deserializeQuotKind c
      some (.quotient kind)
    else none

/-- Collect all constant hashes referenced in an expression. -/
def Expr.constHashes : Expr → List Hash
  | .bvar _ => []
  | .sort _ => []
  | .const h _ => [h]
  | .app f a => f.constHashes ++ a.constHashes
  | .lam ty body => ty.constHashes ++ body.constHashes
  | .forallE ty body => ty.constHashes ++ body.constHashes
  | .letE ty val body => ty.constHashes ++ val.constHashes ++ body.constHashes
  | .proj h _ s => h :: s.constHashes
  | .iref _ _ => []

/-- Collect all constant hashes referenced in a declaration. -/
def Decl.constHashes : Decl → List Hash
  | .axiom _ ty => ty.constHashes
  | .definition _ ty val => ty.constHashes ++ val.constHashes
  | .inductive block =>
    block.types.foldl (fun acc it =>
      acc ++ it.type.constHashes ++
      it.ctors.foldl (fun acc' c => acc' ++ c.constHashes) []) []
  | .quotient _ => []

end HashMath
