/-
  HashMath.Properties.HashInjectivity — Hash equality and serialization injectivity

  SHA-256 is NOT injective (pigeonhole: infinite domain, 2^256 codomain).
  Hash "injectivity" is a computational assumption, not a mathematical truth.

  What IS provable: serialization injectivity (see SerializeInj.lean).
  This means that if two terms have equal hashes, the only explanation is
  a SHA-256 collision on their (distinct) serializations.

  The theorems below are parameterized by an explicit collision-resistance
  hypothesis. They should NOT be treated as unconditional facts.
-/

import HashMath.Hash
import HashMath.Properties.SerializeInj

namespace HashMath

/-- If two levels hash to the same value, they are equal —
    assuming no SHA-256 collisions on the relevant inputs. -/
theorem hashLevel_injective
    (sha256_no_collision : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (l₁ l₂ : Level) :
    hashLevel l₁ = hashLevel l₂ → l₁ = l₂ := by
  sorry -- Requires serializeLevel injectivity + sha256_no_collision

/-- If two expressions hash to the same value, they are equal —
    assuming no SHA-256 collisions on the relevant inputs. -/
theorem hashExpr_injective
    (sha256_no_collision : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (e₁ e₂ : Expr) :
    hashExpr e₁ = hashExpr e₂ → e₁ = e₂ := by
  sorry -- Requires serializeExpr injectivity + sha256_no_collision

/-- If two declarations hash to the same value, they are equal —
    assuming no SHA-256 collisions on the relevant inputs. -/
theorem hashDecl_injective
    (sha256_no_collision : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (d₁ d₂ : Decl) :
    hashDecl d₁ = hashDecl d₂ → d₁ = d₂ := by
  sorry -- Requires serializeDecl injectivity + sha256_no_collision

end HashMath
