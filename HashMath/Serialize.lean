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

  -- Decl tags
  def declAxiom      : UInt8 := 0x20
  def declDefinition : UInt8 := 0x21
  def declInductive  : UInt8 := 0x22
  def declQuotient   : UInt8 := 0x23
end Tag

/-- Serialize a single byte. -/
private def serByte (b : UInt8) : ByteArray :=
  ByteArray.mk #[b]

/-- Serialize a Nat as LEB128. -/
private def serNat (n : Nat) : ByteArray :=
  encodeLEB128 n

/-- Serialize a Hash (fixed 32 bytes). -/
private def serHash (h : Hash) : ByteArray :=
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
  serByte (if block.isUnsafe then 0x01 else 0x00)

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

end HashMath
