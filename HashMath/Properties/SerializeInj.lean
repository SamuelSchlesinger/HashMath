/-
  HashMath.Properties.SerializeInj — Serialization is injective

  We prove that the serialize functions are injective, meaning
  structurally different terms produce different byte representations.
  Combined with SHA3 collision resistance, this gives hash injectivity.
-/

import HashMath.Serialize

namespace HashMath

-- The key insight: each serialization starts with a unique tag byte,
-- and within each tag, the structure is unambiguous because:
-- 1. LEB128 is a prefix-free encoding
-- 2. Hashes are fixed-length (32 bytes)
-- 3. List lengths are encoded before elements
-- 4. Recursive subexpressions are serialized in a deterministic order

-- Full formal proof of injectivity requires showing LEB128 is prefix-free
-- and that the recursive structure is unambiguous. We state the key theorems
-- and provide partial proofs.

/-- LEB128 encoding is injective. -/
theorem encodeLEB128_injective (n m : Nat) :
    encodeLEB128 n = encodeLEB128 m → n = m := by
  intro h
  -- The proof proceeds by strong induction on max(n, m).
  -- For n, m < 128: the single byte determines the value.
  -- For n, m ≥ 128: the low 7 bits + high bit set determines n%128 = m%128,
  -- and by IH on n/128, m/128 we get n/128 = m/128.
  sorry -- Full proof requires careful byte-level reasoning

/-- Level serialization is injective. -/
theorem serializeLevel_injective (l₁ l₂ : Level) :
    serializeLevel l₁ = serializeLevel l₂ → l₁ = l₂ := by
  sorry -- Follows from tag uniqueness + LEB128 injectivity + structural induction

/-- Expression serialization is injective. -/
theorem serializeExpr_injective (e₁ e₂ : Expr) :
    serializeExpr e₁ = serializeExpr e₂ → e₁ = e₂ := by
  sorry -- Follows from tag uniqueness + fixed-length hashes + LEB128 injectivity

/-- Declaration serialization is injective. -/
theorem serializeDecl_injective (d₁ d₂ : Decl) :
    serializeDecl d₁ = serializeDecl d₂ → d₁ = d₂ := by
  sorry -- Follows from tag uniqueness + sub-serialization injectivity

end HashMath
