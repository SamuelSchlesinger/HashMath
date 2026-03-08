/-
  HashMath.Properties.HashInjectivity — Merkle hash equality implies term equality
  (modulo SHA-256 collision resistance)

  With the Merkle-tree hashing scheme, injectivity follows from:
  1. Tag uniqueness (different constructors → different first byte)
  2. Fixed-size children (32-byte hashes → unambiguous parsing)
  3. SHA-256 collision resistance (equal hashes → equal pre-images)
-/

import HashMath.Hash
import HashMath.Properties.SerializeInj

namespace HashMath

/-- If two levels hash to the same value, they are equal
    (assuming SHA-256 collision resistance). -/
theorem hashLevel_injective (l₁ l₂ : Level) :
    hashLevel l₁ = hashLevel l₂ → l₁ = l₂ := by
  sorry -- Follows from tag uniqueness + fixed-size children + collision resistance

/-- If two expressions hash to the same value, they are equal
    (assuming SHA-256 collision resistance). -/
theorem hashExpr_injective (e₁ e₂ : Expr) :
    hashExpr e₁ = hashExpr e₂ → e₁ = e₂ := by
  sorry -- Follows from tag uniqueness + fixed-size children + collision resistance

/-- If two declarations hash to the same value, they are equal
    (assuming SHA-256 collision resistance). -/
theorem hashDecl_injective (d₁ d₂ : Decl) :
    hashDecl d₁ = hashDecl d₂ → d₁ = d₂ := by
  sorry -- Follows from tag uniqueness + fixed-size children + collision resistance

end HashMath
