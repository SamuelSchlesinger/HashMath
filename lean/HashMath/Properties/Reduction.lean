/-
  HashMath.Properties.Reduction — Proofs connecting reduction functions to the spec

  Shows that the implementation's `betaReduce`, `zetaReduce`, etc. agree with
  the `Reduces` / `ReducesStar` inductive relations defined in Spec.lean.
-/

import HashMath.Reduce
import HashMath.Properties.Spec
import HashMath.Properties.DeBruijn

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- betaReduce agrees with the spec
-- ═══════════════════════════════════════════════════════════════════

/-- `betaReduce` is definitionally `body.instantiate arg`. -/
theorem betaReduce_eq_instantiate (body arg : Expr) :
    betaReduce body arg = body.instantiate arg :=
  rfl

/-- `betaReduce` agrees with the `Reduces.beta` rule: for any environment,
    `(λ ty. body) arg` reduces to `betaReduce body arg`. -/
theorem betaReduce_spec (env : Environment) (ty body arg : Expr) :
    Reduces env (.app (.lam ty body) arg) (betaReduce body arg) :=
  Reduces.beta ty body arg

-- ═══════════════════════════════════════════════════════════════════
-- zetaReduce agrees with the spec
-- ═══════════════════════════════════════════════════════════════════

/-- `zetaReduce` agrees with the `Reduces.zeta` rule: for any environment,
    `let x : ty := val in body` reduces to `zetaReduce val body`. -/
theorem zetaReduce_spec (env : Environment) (ty val body : Expr) :
    Reduces env (.letE ty val body) (zetaReduce val body) :=
  Reduces.zeta ty val body

-- ═══════════════════════════════════════════════════════════════════
-- Congruence for multi-step reduction
-- ═══════════════════════════════════════════════════════════════════

/-- If `f` reduces to `f'` in multiple steps, then `app f a` reduces to
    `app f' a` in multiple steps. Congruence under application. -/
theorem ReducesStar.appFn {env : Environment} {f f' a : Expr}
    (h : ReducesStar env f f') : ReducesStar env (.app f a) (.app f' a) := by
  induction h with
  | refl _ => exact .refl _
  | step _ f₂ _ hstep _ ih =>
    exact .step _ (.app f₂ a) _ (Reduces.appFn _ _ a hstep) ih

-- ═══════════════════════════════════════════════════════════════════
-- Single-step beta as multi-step
-- ═══════════════════════════════════════════════════════════════════

/-- A single beta step viewed as a multi-step reduction. -/
theorem beta_reduces_star (env : Environment) (ty body arg : Expr) :
    ReducesStar env (.app (.lam ty body) arg) (body.instantiate arg) :=
  ReducesStar.single (Reduces.beta ty body arg)

end HashMath
