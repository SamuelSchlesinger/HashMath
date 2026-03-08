/-
  HashMath.Properties.HashInjectivity — Hash equality implies term equality
  (modulo SHA3 collision resistance)
-/

import HashMath.Hash
import HashMath.Properties.SerializeInj

namespace HashMath

/-- If two levels hash to the same value, they are equal
    (assuming SHA3 collision resistance). -/
theorem hashLevel_injective (l₁ l₂ : Level) :
    hashLevel l₁ = hashLevel l₂ → l₁ = l₂ := by
  intro h
  have hsz := hashBytes_injective _ _ h
  exact serializeLevel_injective l₁ l₂ hsz

/-- If two expressions hash to the same value, they are equal
    (assuming SHA3 collision resistance). -/
theorem hashExpr_injective (e₁ e₂ : Expr) :
    hashExpr e₁ = hashExpr e₂ → e₁ = e₂ := by
  intro h
  have hsz := hashBytes_injective _ _ h
  exact serializeExpr_injective e₁ e₂ hsz

/-- If two declarations hash to the same value, they are equal
    (assuming SHA3 collision resistance). -/
theorem hashDecl_injective (d₁ d₂ : Decl) :
    hashDecl d₁ = hashDecl d₂ → d₁ = d₂ := by
  intro h
  have hsz := hashBytes_injective _ _ h
  exact serializeDecl_injective d₁ d₂ hsz

end HashMath
