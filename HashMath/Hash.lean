/-
  HashMath.Hash — SHA-256 Merkle-tree hashing for HashMath CIC terms

  Uses a Merkle-tree scheme: each node hashes (tag ∥ child_hashes).
  This matches the whitepaper specification: H(app(f,a)) = SHA256(0x13 ∥ H(f) ∥ H(a)).
-/

import HashMath.Serialize
import HashMath.SHA256

namespace HashMath

/-- Compute the Hash of a ByteArray using SHA-256. -/
def hashBytes (data : ByteArray) : Hash :=
  ⟨sha256 data, sha256_size data⟩

/-- Hash a universe level (Merkle-tree: tag ∥ child hashes). -/
def hashLevel : Level → Hash
  | .zero => hashBytes (serByte Tag.levelZero)
  | .succ l => hashBytes (serByte Tag.levelSucc ++ (hashLevel l).bytes)
  | .max l₁ l₂ => hashBytes (serByte Tag.levelMax ++ (hashLevel l₁).bytes ++ (hashLevel l₂).bytes)
  | .imax l₁ l₂ => hashBytes (serByte Tag.levelIMax ++ (hashLevel l₁).bytes ++ (hashLevel l₂).bytes)
  | .param n => hashBytes (serByte Tag.levelParam ++ serNat n)
where
  serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
  serNat (n : Nat) : ByteArray := encodeLEB128 n

/-- Hash an expression (Merkle-tree: tag ∥ child hashes). -/
def hashExpr : Expr → Hash
  | .bvar n => hashBytes (serByte Tag.exprBvar ++ serNat n)
  | .sort l => hashBytes (serByte Tag.exprSort ++ (hashLevel l).bytes)
  | .const h ls =>
    hashBytes (serByte Tag.exprConst ++ h.bytes ++ serNat ls.length ++
      ByteArray.concatList (ls.map fun l => (hashLevel l).bytes))
  | .app f a => hashBytes (serByte Tag.exprApp ++ (hashExpr f).bytes ++ (hashExpr a).bytes)
  | .lam ty body => hashBytes (serByte Tag.exprLam ++ (hashExpr ty).bytes ++ (hashExpr body).bytes)
  | .forallE ty body => hashBytes (serByte Tag.exprForallE ++ (hashExpr ty).bytes ++ (hashExpr body).bytes)
  | .letE ty val body =>
    hashBytes (serByte Tag.exprLetE ++ (hashExpr ty).bytes ++ (hashExpr val).bytes ++ (hashExpr body).bytes)
  | .proj h i s => hashBytes (serByte Tag.exprProj ++ h.bytes ++ serNat i ++ (hashExpr s).bytes)
  | .iref idx ls =>
    hashBytes (serByte Tag.exprIRef ++ serNat idx ++ serNat ls.length ++
      ByteArray.concatList (ls.map fun l => (hashLevel l).bytes))
where
  serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
  serNat (n : Nat) : ByteArray := encodeLEB128 n

/-- Hash an inductive type within a block. -/
private def hashInductiveType (it : InductiveType) : Hash :=
  let serNat (n : Nat) : ByteArray := encodeLEB128 n
  hashBytes ((hashExpr it.type).bytes ++
    serNat it.ctors.length ++
    ByteArray.concatList (it.ctors.map fun c => (hashExpr c).bytes))

/-- Hash an inductive block. -/
private def hashInductiveBlock (block : InductiveBlock) : Hash :=
  let serNat (n : Nat) : ByteArray := encodeLEB128 n
  let serBool (b : Bool) : ByteArray := ByteArray.mk #[if b then 0x01 else 0x00]
  hashBytes (serNat block.numUnivParams ++
    serNat block.numParams ++
    serNat block.types.length ++
    ByteArray.concatList (block.types.map fun it => (hashInductiveType it).bytes) ++
    serBool block.isUnsafe)

/-- Hash a declaration (Merkle-tree: tag ∥ child hashes). -/
def hashDecl : Decl → Hash
  | .axiom n ty =>
    let serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
    let serNat (n : Nat) : ByteArray := encodeLEB128 n
    hashBytes (serByte Tag.declAxiom ++ serNat n ++ (hashExpr ty).bytes)
  | .definition n ty val =>
    let serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
    let serNat (n : Nat) : ByteArray := encodeLEB128 n
    hashBytes (serByte Tag.declDefinition ++ serNat n ++ (hashExpr ty).bytes ++ (hashExpr val).bytes)
  | .inductive block =>
    let serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
    hashBytes (serByte Tag.declInductive ++ (hashInductiveBlock block).bytes)
  | .quotient kind =>
    let serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
    hashBytes (serByte Tag.declQuotient ++ serByte (serializeQuotKind kind))

-- Derived entity hash functions for inductive sub-entities

/-- Hash of the i-th type in an inductive block. -/
def hashIndType (blockHash : Hash) (typeIdx : Nat) : Hash :=
  let serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
  let serNat (n : Nat) : ByteArray := encodeLEB128 n
  hashBytes (serByte Tag.indType ++ blockHash.bytes ++ serNat typeIdx)

/-- Hash of the j-th constructor of the i-th type in an inductive block. -/
def hashCtor (blockHash : Hash) (typeIdx ctorIdx : Nat) : Hash :=
  let serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
  let serNat (n : Nat) : ByteArray := encodeLEB128 n
  hashBytes (serByte Tag.indCtor ++ blockHash.bytes ++ serNat typeIdx ++ serNat ctorIdx)

/-- Hash of the recursor of the i-th type in an inductive block. -/
def hashRec (blockHash : Hash) (typeIdx : Nat) : Hash :=
  let serByte (b : UInt8) : ByteArray := ByteArray.mk #[b]
  let serNat (n : Nat) : ByteArray := encodeLEB128 n
  hashBytes (serByte Tag.indRec ++ blockHash.bytes ++ serNat typeIdx)

-- Collision resistance axiom: if sha256 produces equal outputs,
-- the inputs were equal. This is the standard cryptographic assumption.
axiom sha256_collision_resistant (a b : ByteArray) :
  sha256 a = sha256 b → a = b

/-- hashBytes is injective (given SHA-256 collision resistance). -/
theorem hashBytes_injective (a b : ByteArray) :
    hashBytes a = hashBytes b → a = b := by
  intro h
  have : (hashBytes a).bytes = (hashBytes b).bytes := by rw [h]
  simp [hashBytes] at this
  exact sha256_collision_resistant _ _ this

end HashMath
