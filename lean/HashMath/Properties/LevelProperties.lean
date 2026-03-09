/-
  HashMath.Properties.LevelProperties — Properties of Level operations

  Simple unfolding lemmas and structural inductions for substParams,
  isClosed, toNat, nSucc, and normalize.
-/

import HashMath.Level

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- substParams structural lemmas
-- ═══════════════════════════════════════════════════════════════════

@[simp] theorem Level.substParams_zero (ls : List Level) :
    Level.substParams ls .zero = .zero := rfl

@[simp] theorem Level.substParams_succ (ls : List Level) (l : Level) :
    Level.substParams ls (.succ l) = .succ (Level.substParams ls l) := rfl

@[simp] theorem Level.substParams_max (ls : List Level) (l₁ l₂ : Level) :
    Level.substParams ls (.max l₁ l₂) =
      .max (Level.substParams ls l₁) (Level.substParams ls l₂) := rfl

@[simp] theorem Level.substParams_imax (ls : List Level) (l₁ l₂ : Level) :
    Level.substParams ls (.imax l₁ l₂) =
      .imax (Level.substParams ls l₁) (Level.substParams ls l₂) := rfl

-- ═══════════════════════════════════════════════════════════════════
-- isClosed
-- ═══════════════════════════════════════════════════════════════════

@[simp] theorem Level.isClosed_zero : Level.zero.isClosed = true := rfl

@[simp] theorem Level.isClosed_param (n : Nat) : (Level.param n).isClosed = false := rfl

-- ═══════════════════════════════════════════════════════════════════
-- toNat
-- ═══════════════════════════════════════════════════════════════════

@[simp] theorem Level.toNat_zero : Level.zero.toNat = some 0 := rfl

theorem Level.toNat_nSucc (n : Nat) : (Level.nSucc n).toNat = some n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [Level.nSucc, Level.toNat, ih, Option.map]

-- ═══════════════════════════════════════════════════════════════════
-- normalize
-- ═══════════════════════════════════════════════════════════════════

@[simp] theorem Level.normalize_zero : Level.zero.normalize = .zero := rfl

@[simp] theorem Level.normalize_param (n : Nat) : (Level.param n).normalize = .param n := rfl

end HashMath
