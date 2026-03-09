/-
  HashMath.Quotient — The 4 quotient constants: types and hashes

  Quotient reduction rules are in Reduce.lean (they need whnfCore).
-/

import HashMath.Hash

namespace HashMath

/-- Compute the hash of a quotient declaration. -/
def quotientHash (kind : QuotKind) : Hash :=
  hashDecl (.quotient kind)

/-- Get the type of a quotient constant.
    These types use de Bruijn indices (no names):
    - Quot:      Π (α : Sort u). (α → α → Prop) → Sort u
    - Quot.mk:   Π (α : Sort u). (r : α → α → Prop) → α → Quot r
    - Quot.lift:  Sort 0  (placeholder — full type needs Eq which is user-defined)
    - Quot.ind:   Sort 0  (placeholder — full type needs Quot ref under binders)
-/
def quotientType (kind : QuotKind) : Expr :=
  match kind with
  | .quot =>
    -- Quot : Π (α : Sort u). (α → α → Prop) → Sort u
    let sortU := Expr.sort (.param 0)
    let α := Expr.bvar 1
    let relTy := Expr.forallE α (Expr.forallE (α.liftN 1) (Expr.sort .zero))
    Expr.forallE sortU (Expr.forallE relTy sortU)
  | .quotMk =>
    -- Quot.mk : Π (α : Sort u) (r : α → α → Prop) (a : α). Quot r
    -- Under 3 binders: α = bvar 2, r = bvar 1, a = bvar 0
    -- Return type: Quot r = app (app (const quotHash [param 0]) α) r
    let sortU := Expr.sort (.param 0)
    let α₂ := Expr.bvar 2  -- α under 3 binders
    let α₁ := Expr.bvar 1  -- α under 2 binders
    let relTy := Expr.forallE α₁ (Expr.forallE (α₁.liftN 1) (Expr.sort .zero))
    let quotHash := quotientHash .quot
    let quotReturn := Expr.app (.app (.const quotHash [.param 0]) α₂) (.bvar 1)
    Expr.forallE sortU (Expr.forallE relTy (Expr.forallE α₂ quotReturn))
  | .quotLift =>
    -- Quot.lift : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} →
    --             (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
    -- Placeholder: full type requires Eq, which is a user-defined inductive.
    -- Reduction (Quot.lift f h (Quot.mk r a) → f a) works without the type.
    Expr.sort .zero
  | .quotInd =>
    -- Quot.ind : {α : Sort u} → {r : α → α → Prop} →
    --            {β : Quot r → Prop} → (∀ a, β (Quot.mk r a)) → ∀ q, β q
    -- Placeholder: full type requires Quot under binders and is complex.
    -- Reduction (Quot.ind h (Quot.mk r a) → h a) works without the type.
    Expr.sort .zero

end HashMath
