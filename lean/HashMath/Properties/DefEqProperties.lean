/-
  HashMath.Properties.DefEqProperties — Definitional equality properties (Layer 4)

  This file states soundness and structural properties of the algorithmic
  `isDefEq` and `isSubtype` functions with respect to the declarative
  `IsDefEq` relation defined in Spec.lean.

  STATUS: All proofs are sorry'd (except where noted).

  WHY PROOFS ARE BLOCKED:
  `isDefEq`, `isDefEqCore`, and `isSubtype` are defined as `partial def`
  in a `mutual` block in DefEq.lean. Lean 4's kernel treats `partial`
  functions as opaque — it cannot unfold their definitions, making case
  analysis and induction on their execution impossible.

  The key consequence: even `isDefEq_refl` (which should follow from the
  `t == s` check on the first line of `isDefEq`) cannot be proven because
  we cannot unfold `isDefEq` to expose that check.

  APPROACH FOR FUTURE WORK:
  - Reflexivity might be provable if `isDefEq` is refactored to use
    well-founded recursion, since the `t == s` shortcut is the very first
    thing checked.
  - Soundness (`isDefEq_sound`) requires showing every branch of the
    algorithm produces terms that are related by `IsDefEq` — this needs
    both unfoldability and Layer 2 reduction properties.
  - Symmetry and transitivity of the algorithm are extremely hard to prove
    directly. The recommended approach is to prove soundness w.r.t. the
    declarative `IsDefEq` (which is defined as an equivalence relation),
    and derive symmetry/transitivity from the spec.
-/

import HashMath.Properties.Spec
import HashMath.DefEq

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- 4.1 Soundness of isDefEq
-- ═══════════════════════════════════════════════════════════════════

/-- **Soundness of isDefEq**: if the algorithmic equality checker accepts
    two terms as definitionally equal, then they are related by the
    declarative `IsDefEq` relation.

    This is the key theorem connecting the algorithm to the specification.
    It says: the checker never claims two terms are equal when they aren't
    (according to the declarative theory).

    Blocked by: `isDefEq` is `partial` — cannot unfold in proofs.
    Would require case analysis on every branch of `isDefEq` + `isDefEqCore`,
    plus Layer 2 properties showing `whnf`/`whnfCore` produce terms related
    by `ReducesStar`. -/
theorem isDefEq_sound
    (env : Environment) (ctx : LocalCtx) (t s : Expr) :
    isDefEq env ctx t s = true →
    IsDefEq env t s := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 4.2 Reflexivity
-- ═══════════════════════════════════════════════════════════════════

/-- **Reflexivity of isDefEq**: every expression is definitionally equal
    to itself.

    The first line of `isDefEq` checks `t == s` (BEq on Expr), which
    should return `true` when `t` and `s` are the same value. This means
    reflexivity should hold whenever `BEq Expr` is reflexive.

    Blocked by: `isDefEq` is `partial` — cannot unfold to see the
    `t == s` check. Also requires `BEq.beq` reflexivity for `Expr`.
    If `isDefEq` were non-`partial`, this would likely be a short proof
    using `simp [isDefEq, BEq.beq]`. -/
theorem isDefEq_refl
    (env : Environment) (ctx : LocalCtx) (e : Expr) :
    isDefEq env ctx e e = true := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 4.3 Symmetry (conditional on soundness)
-- ═══════════════════════════════════════════════════════════════════

/-- **Symmetry via the spec**: if `isDefEq` is sound, then whenever the
    algorithm accepts `(t, s)`, the declarative relation also holds for
    `(s, t)`. This does NOT mean the algorithm itself is symmetric — only
    that the declarative relation is.

    This follows immediately from `isDefEq_sound` + `IsDefEq.symm`, but
    to show the *algorithm* returns `true` on `(s, t)` whenever it does
    on `(t, s)`, we would need a separate (harder) proof.

    Blocked by: depends on `isDefEq_sound`. -/
theorem isDefEq_symm_spec
    (env : Environment) (ctx : LocalCtx) (t s : Expr) :
    isDefEq env ctx t s = true →
    IsDefEq env s t := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 4.4 Soundness of isSubtype
-- ═══════════════════════════════════════════════════════════════════

/-- **Soundness of isSubtype**: if `isSubtype` accepts `T ≤ U`, then
    either `T` and `U` are definitionally equal, or they are related by
    cumulativity (Sort levels or covariant Pi codomains).

    The subtyping relation is: `Sort l₁ ≤ Sort l₂` when `l₁ ≤ l₂`,
    and `Π A. B₁ ≤ Π A. B₂` when `A ≡ A` and `B₁ ≤ B₂` (covariant
    in the codomain, invariant in the domain).

    For typing purposes: if `e : T` and `T ≤ U`, then `e : U`.

    Blocked by: `isSubtype` is `partial` — cannot unfold in proofs. -/
theorem isSubtype_sound
    (env : Environment) (ctx : LocalCtx) (T U : Expr) :
    isSubtype env ctx T U = true →
    IsDefEq env T U := by
  -- Note: this is a simplification. Full subtyping is a refinement of
  -- definitional equality that also allows `Sort l₁ ≤ Sort l₂` when
  -- `l₁ ≤ l₂` (even if they're not definitionally equal). A proper
  -- formulation would use a `IsSubtype` relation. For now we use
  -- `IsDefEq` as an approximation, since `IsDefEq` in the spec includes
  -- Sort-level equality via `proofIrrel` / `conv` rules.
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 4.5 isDefEq implies isSubtype
-- ═══════════════════════════════════════════════════════════════════

/-- **DefEq implies subtyping**: if two types are definitionally equal,
    then one is a subtype of the other. This follows from the first line
    of `isSubtype` which calls `isDefEq`.

    Blocked by: `isSubtype` is `partial` — cannot unfold in proofs. -/
theorem isDefEq_implies_isSubtype
    (env : Environment) (ctx : LocalCtx) (T U : Expr) :
    isDefEq env ctx T U = true →
    isSubtype env ctx T U = true := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 4.6 isSubtype reflexivity
-- ═══════════════════════════════════════════════════════════════════

/-- **Reflexivity of isSubtype**: every type is a subtype of itself.
    Should follow from `isDefEq_refl` + `isDefEq_implies_isSubtype`.

    Blocked by: depends on `isDefEq_refl` and `isDefEq_implies_isSubtype`,
    both of which are blocked by `partial`. -/
theorem isSubtype_refl
    (env : Environment) (ctx : LocalCtx) (T : Expr) :
    isSubtype env ctx T T = true := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 4.7 Reduction implies definitional equality (algorithmic)
-- ═══════════════════════════════════════════════════════════════════

/-- **Reduction implies algorithmic equality**: if `e` reduces to `e'`
    (in the `ReducesStar` sense), then `isDefEq` accepts `(e, e')`.

    This is the algorithmic counterpart of `ReducesStar.toIsDefEq`.
    It says the algorithm is complete for reduction-related terms.

    Blocked by: `isDefEq` is `partial`. Would require showing that
    `whnf` produces the same normal form for both sides. -/
theorem reduces_implies_isDefEq
    (env : Environment) (ctx : LocalCtx) (e e' : Expr) :
    ReducesStar env e e' →
    isDefEq env ctx e e' = true := by
  sorry

end HashMath
