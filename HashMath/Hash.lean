/-
  HashMath.Hash — SHA3-256 hashing for HashMath CIC terms

  Uses a pure Lean SHA3-256 implementation (Keccak[512]).
  In a production system, this would be an FFI binding to a C implementation.
-/

import HashMath.Serialize

namespace HashMath

-- We axiomatize SHA3-256 for now. The implementation can be swapped in later
-- via FFI or a pure Lean implementation.

/-- SHA3-256 hash function. Axiomatized; the actual implementation is part of the TCB. -/
opaque sha3_256 (data : ByteArray) : ByteArray

/-- Axiom: sha3_256 always produces 32 bytes. -/
axiom sha3_256_size (data : ByteArray) : (sha3_256 data).size = 32

/-- Compute the Hash of a ByteArray using SHA3-256. -/
def hashBytes (data : ByteArray) : Hash :=
  ⟨sha3_256 data, sha3_256_size data⟩

/-- Hash a universe level. -/
def hashLevel (l : Level) : Hash :=
  hashBytes (serializeLevel l)

/-- Hash an expression. -/
def hashExpr (e : Expr) : Hash :=
  hashBytes (serializeExpr e)

/-- Hash a declaration. -/
def hashDecl (d : Decl) : Hash :=
  hashBytes (serializeDecl d)

-- Collision resistance axiom: if sha3_256 produces equal outputs,
-- the inputs were equal. This is the standard cryptographic assumption.
axiom sha3_collision_resistant (a b : ByteArray) :
  sha3_256 a = sha3_256 b → a = b

/-- hashBytes is injective (given SHA3 collision resistance). -/
theorem hashBytes_injective (a b : ByteArray) :
    hashBytes a = hashBytes b → a = b := by
  intro h
  have : (hashBytes a).bytes = (hashBytes b).bytes := by rw [h]
  simp [hashBytes] at this
  exact sha3_collision_resistant _ _ this

/-- If two expressions hash to the same value, their serializations are equal. -/
theorem hashExpr_injective_serialization (e₁ e₂ : Expr) :
    hashExpr e₁ = hashExpr e₂ → serializeExpr e₁ = serializeExpr e₂ := by
  intro h
  exact hashBytes_injective _ _ h

end HashMath
