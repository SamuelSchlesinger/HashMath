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
    -- Under 1 binder (α): α = bvar 0
    let sortU := Expr.sort (.param 0)
    let α := Expr.bvar 0  -- α under 1 binder
    let relTy := Expr.forallE α (Expr.forallE (α.liftN 1) (Expr.sort .zero))
    Expr.forallE sortU (Expr.forallE relTy sortU)
  | .quotMk =>
    -- Quot.mk : Π (α : Sort u) (r : α → α → Prop) (a : α). Quot r
    -- relTy domain: under 1 binder (α), α = bvar 0
    -- a domain: under 2 binders (α, r), α = bvar 1
    -- Return type: under 3 binders (α, r, a), α = bvar 2, r = bvar 1
    let sortU := Expr.sort (.param 0)
    let α_under1 := Expr.bvar 0  -- α under 1 binder (for relTy domain)
    let relTy := Expr.forallE α_under1 (Expr.forallE (α_under1.liftN 1) (Expr.sort .zero))
    let quotHash := quotientHash .quot
    -- Under 3 binders: α = bvar 2, r = bvar 1
    let α_under3 := Expr.bvar 2
    let quotReturn := Expr.app (.app (.const quotHash [.param 0]) α_under3) (.bvar 1)
    -- Under 2 binders: α = bvar 1
    let α_under2 := Expr.bvar 1
    Expr.forallE sortU (Expr.forallE relTy (Expr.forallE α_under2 quotReturn))
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
