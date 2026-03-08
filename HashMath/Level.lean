/-
  HashMath.Level — Universe levels for HashMath CIC
-/

import HashMath.Basic

namespace HashMath

/-- Universe levels with 5 constructors.
    `param` uses de Bruijn index instead of a name. -/
inductive Level where
  | zero : Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  | param : Nat → Level
  deriving Repr, BEq, Inhabited

namespace Level

/-- Substitute universe parameters. `subst ls l` replaces `param i` with `ls[i]`. -/
def substParams (ls : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (substParams ls l)
  | .max l₁ l₂ => .max (substParams ls l₁) (substParams ls l₂)
  | .imax l₁ l₂ => .imax (substParams ls l₁) (substParams ls l₂)
  | .param n => ls.getD n (.param n)

/-- Normalize a level to a canonical form.
    `imax u 0 = 0` and `imax u (succ v) = max u (succ v)`. -/
def normalize : Level → Level
  | .zero => .zero
  | .succ l => .succ (normalize l)
  | .max l₁ l₂ => .max (normalize l₁) (normalize l₂)
  | .imax l₁ l₂ =>
    match normalize l₂ with
    | .zero => .zero
    | .succ l₂' => .max (normalize l₁) (.succ l₂')
    | l₂' => .imax (normalize l₁) l₂'
  | .param n => .param n

/-- Check if a level has no free universe parameters. -/
def isClosed : Level → Bool
  | .zero => true
  | .succ l => isClosed l
  | .max l₁ l₂ => isClosed l₁ && isClosed l₂
  | .imax l₁ l₂ => isClosed l₁ && isClosed l₂
  | .param _ => false

/-- Evaluate a closed level to a natural number. -/
def toNat : Level → Option Nat
  | .zero => some 0
  | .succ l => l.toNat.map (· + 1)
  | .max l₁ l₂ => do
    let n₁ ← l₁.toNat
    let n₂ ← l₂.toNat
    return Nat.max n₁ n₂
  | .imax l₁ l₂ => do
    let n₁ ← l₁.toNat
    let n₂ ← l₂.toNat
    if n₂ = 0 then return 0
    else return Nat.max n₁ n₂
  | .param _ => none

/-- Check `l₁ ≤ l₂` for closed ground levels. -/
def leq (l₁ l₂ : Level) : Option Bool := do
  let n₁ ← l₁.normalize.toNat
  let n₂ ← l₂.normalize.toNat
  return n₁ ≤ n₂

/-- Structural equality of levels (syntactic, after normalization). -/
def beqNorm (l₁ l₂ : Level) : Bool :=
  l₁.normalize == l₂.normalize

end Level

end HashMath
