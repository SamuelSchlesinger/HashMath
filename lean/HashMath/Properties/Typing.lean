/-
  HashMath.Properties.Typing — Type inference soundness (Layer 3)

  This file states the main soundness theorem for `inferType`: if the
  algorithmic type inferrer accepts an expression and returns a type T,
  then the declarative typing judgment `HasType env ctx e T` holds.

  STATUS: All proofs are sorry'd.

  WHY PROOFS ARE BLOCKED:
  `inferType` is defined as `partial def` in a `mutual` block (along with
  `isDefEq`, `isDefEqCore`, `isSubtype`). Lean 4 treats `partial` functions
  as opaque constants — the kernel cannot unfold their definitions, so we
  cannot perform case analysis or structural induction on their execution.

  To fill in these proofs, one would need to either:
  1. Refactor `inferType` to use well-founded recursion (e.g., on expression
     size + fuel), making it non-`partial` and unfoldable.
  2. Create a fuel-bounded mirror (`inferTypeN : Nat → ... → Option (Except
     String Expr)`) and prove it agrees with the `partial` version on
     terminating inputs, then prove properties of the fuel-bounded version.
  3. Use `@[implemented_by]` to link a kernel-visible specification to the
     efficient `partial` implementation — but this introduces a trusted gap.

  Any of these approaches is significant refactoring work.
-/

import HashMath.Properties.Spec
import HashMath.DefEq

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- 3.1 inferType soundness
-- ═══════════════════════════════════════════════════════════════════

/-- **Soundness of inferType**: if `inferType` returns a type `T` for
    expression `e` in environment `env` with context `ctx`, then the
    declarative judgment `HasType env ctx e T` holds.

    This is the central theorem connecting the algorithmic implementation
    to the formal specification. It says inferType never lies — every
    accepted term genuinely has the inferred type.

    Blocked by: `inferType` is `partial` — cannot unfold in proofs. -/
theorem inferType_sound
    (env : Environment) (ctx : LocalCtx) (e : Expr) (T : Expr) :
    inferType env ctx e = .ok T →
    HasType env ctx e T := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 3.2 Types of well-typed terms are themselves typed
-- ═══════════════════════════════════════════════════════════════════

/-- **Types are typed**: if `inferType` returns `T` for expression `e`,
    then `T` itself is a type — i.e., there exists some universe level
    `l` such that `HasType env ctx T (Sort l)`.

    This is a key regularity property of CIC: well-typed terms have
    well-typed types. Combined with `inferType_sound`, it establishes
    that the type checker maintains the sort discipline.

    Blocked by: requires `inferType_sound` + mutual induction on the
    inference derivation. Also blocked by `inferType` being `partial`. -/
theorem inferType_type_of_type
    (env : Environment) (ctx : LocalCtx) (e : Expr) (T : Expr) :
    inferType env ctx e = .ok T →
    ∃ l, HasType env ctx T (.sort l) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 3.3 inferType for closed expressions
-- ═══════════════════════════════════════════════════════════════════

/-- **Soundness of inferTypeClosed**: specialization of `inferType_sound`
    to the empty context. This is the form most directly used by
    `checkDecl`, which type-checks top-level declarations.

    Blocked by: depends on `inferType_sound`. -/
theorem inferTypeClosed_sound
    (env : Environment) (e : Expr) (T : Expr) :
    inferTypeClosed env e = .ok T →
    HasType env [] e T := by
  -- inferTypeClosed is defined as `inferType env [] e`
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 3.4 inferType respects weakening
-- ═══════════════════════════════════════════════════════════════════

/-- **Weakening**: if `e` is well-typed in context `ctx`, then `e.liftN 1`
    is well-typed in any extended context `ty :: ctx`, with the same type
    (appropriately lifted).

    This is needed for the binder cases of `inferType_sound` — when we
    go under a lambda or forall, we extend the context and must show the
    body remains well-typed.

    Blocked by: requires structural induction on `HasType` derivation +
    de Bruijn lifting lemmas from Layer 1. -/
theorem hasType_weakening
    (env : Environment) (ctx : Ctx) (e T ty : Expr) :
    HasType env ctx e T →
    HasType env (ty :: ctx) (e.liftN 1) (T.liftN 1) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 3.5 inferType determinism
-- ═══════════════════════════════════════════════════════════════════

/-- **Determinism**: `inferType` returns at most one type for any given
    expression. (The algorithmic inferrer is a function, so this is
    trivially true — but it's useful to state explicitly for
    metatheoretic reasoning.)

    This is immediate from `inferType` being a function: if it returns
    `.ok T₁` and `.ok T₂`, then `T₁ = T₂`. -/
theorem inferType_deterministic
    (env : Environment) (ctx : LocalCtx) (e : Expr) (T₁ T₂ : Expr) :
    inferType env ctx e = .ok T₁ →
    inferType env ctx e = .ok T₂ →
    T₁ = T₂ := by
  intro h₁ h₂
  rw [h₁] at h₂
  exact Except.ok.inj h₂

end HashMath
