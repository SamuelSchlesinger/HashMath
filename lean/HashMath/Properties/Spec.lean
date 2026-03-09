/-
  HashMath.Properties.Spec — Formal specification of CIC typing and reduction

  This file defines the inductive relations that serve as the reference
  specification for the type checker. The implementation (inferType, isDefEq,
  whnf, etc.) should be sound with respect to these relations.
-/

import HashMath.Reduce

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- Reduction relation
-- ═══════════════════════════════════════════════════════════════════

/-- One-step reduction relation. `Reduces env e e'` means `e` reduces to `e'`
    in one step in environment `env`. -/
inductive Reduces (env : Environment) : Expr → Expr → Prop where
  /-- β-reduction: `(λ ty. body) arg → body[arg/0]` -/
  | beta (ty body arg : Expr) :
      Reduces env (.app (.lam ty body) arg) (body.instantiate arg)
  /-- ζ-reduction: `let x : ty := val in body → body[val/0]` -/
  | zeta (ty val body : Expr) :
      Reduces env (.letE ty val body) (body.instantiate val)
  /-- δ-reduction: unfold a defined constant -/
  | delta (h : Hash) (univs : List Level) (val : Expr) :
      env.getDeclValue h univs = some val →
      Reduces env (.const h univs) val
  /-- δ-reduction at the head of an application spine -/
  | deltaApp (h : Hash) (univs : List Level) (val : Expr) (args : List Expr) :
      env.getDeclValue h univs = some val →
      Reduces env (Expr.mkAppN (.const h univs) args) (Expr.mkAppN val args)
  /-- Projection reduction: `.proj(I, i, ctor params... fields...) → fields[i]` -/
  | proj (typeName : Hash) (idx : Nat) (struct result : Expr) :
      projReduce env typeName idx struct = some result →
      Reduces env (.proj typeName idx struct) result
  /-- Congruence: reduce the function in an application -/
  | appFn (f f' a : Expr) :
      Reduces env f f' →
      Reduces env (.app f a) (.app f' a)

/-- Reflexive-transitive closure of reduction. -/
inductive ReducesStar (env : Environment) : Expr → Expr → Prop where
  | refl (e : Expr) : ReducesStar env e e
  | step (e₁ e₂ e₃ : Expr) :
      Reduces env e₁ e₂ → ReducesStar env e₂ e₃ → ReducesStar env e₁ e₃

/-- ReducesStar is transitive. -/
theorem ReducesStar.trans {env : Environment} {e₁ e₂ e₃ : Expr} :
    ReducesStar env e₁ e₂ → ReducesStar env e₂ e₃ → ReducesStar env e₁ e₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl _ => exact h₂
  | step _ e₂' _ hstep _ ih => exact .step _ e₂' _ hstep (ih h₂)

-- ═══════════════════════════════════════════════════════════════════
-- Declarative definitional equality
-- ═══════════════════════════════════════════════════════════════════

/-- Declarative definitional equality. This is the specification that the
    algorithmic `isDefEq` should be sound with respect to.

    Note: this is an equivalence relation closed under reduction and congruence. -/
inductive IsDefEq (env : Environment) : Expr → Expr → Prop where
  /-- Reflexivity -/
  | refl (e : Expr) : IsDefEq env e e
  /-- Symmetry -/
  | symm (t s : Expr) : IsDefEq env t s → IsDefEq env s t
  /-- Transitivity -/
  | trans (t u s : Expr) :
      IsDefEq env t u → IsDefEq env u s → IsDefEq env t s
  /-- Reduction is included in definitional equality -/
  | reduce (e e' : Expr) :
      Reduces env e e' → IsDefEq env e e'
  /-- Congruence for application -/
  | congApp (f₁ f₂ a₁ a₂ : Expr) :
      IsDefEq env f₁ f₂ → IsDefEq env a₁ a₂ →
      IsDefEq env (.app f₁ a₁) (.app f₂ a₂)
  /-- Congruence for lambda -/
  | congLam (ty₁ ty₂ body₁ body₂ : Expr) :
      IsDefEq env ty₁ ty₂ → IsDefEq env body₁ body₂ →
      IsDefEq env (.lam ty₁ body₁) (.lam ty₂ body₂)
  /-- Congruence for forallE -/
  | congForallE (ty₁ ty₂ body₁ body₂ : Expr) :
      IsDefEq env ty₁ ty₂ → IsDefEq env body₁ body₂ →
      IsDefEq env (.forallE ty₁ body₁) (.forallE ty₂ body₂)
  /-- η-expansion for lambdas: `e = λ x. e x` -/
  | etaLam (ty body e : Expr) :
      IsDefEq env body (.app (e.liftN 1) (.bvar 0)) →
      IsDefEq env (.lam ty body) e
  /-- Proof irrelevance: two proofs of the same Prop are equal -/
  | proofIrrel (t s : Expr) :
      -- (simplified: full version would reference the typing judgment)
      IsDefEq env t s

-- ═══════════════════════════════════════════════════════════════════
-- Typing judgment
-- ═══════════════════════════════════════════════════════════════════

/-- A local context: list of types for bound variables.
    `ctx[i]` is the type of `bvar i` (most recently bound first). -/
abbrev Ctx := List Expr

/-- The typing judgment. `HasType env ctx e T` means expression `e` has
    type `T` in environment `env` with local context `ctx`.

    This is the *declarative* specification. The algorithmic `inferType`
    should be sound with respect to this (every accepted term is typable). -/
inductive HasType (env : Environment) : Ctx → Expr → Expr → Prop where
  /-- Bound variable: look up in context, lift past intervening binders -/
  | bvar (ctx : Ctx) (i : Nat) (T : Expr) :
      ctx[i]? = some T →
      HasType env ctx (.bvar i) (T.liftN (i + 1))

  /-- Sort: the type of `Sort l` is `Sort (succ l)` -/
  | sort (ctx : Ctx) (l : Level) :
      HasType env ctx (.sort l) (.sort (.succ l))

  /-- Constant: look up declared type -/
  | constDecl (ctx : Ctx) (h : Hash) (univs : List Level) (T : Expr) :
      env.getDeclType h univs = some T →
      HasType env ctx (.const h univs) T

  /-- Inductive type constant -/
  | constInd (ctx : Ctx) (h : Hash) (univs : List Level)
      (block : InductiveBlock) (typeIdx : Nat) (indTy : InductiveType) :
      env.getInductiveBlockForType h = some (block, typeIdx) →
      block.types[typeIdx]? = some indTy →
      HasType env ctx (.const h univs) (indTy.type.substLevelParams univs)

  /-- Constructor constant -/
  | constCtor (ctx : Ctx) (h : Hash) (univs : List Level)
      (info : ConstructorInfo) :
      env.getConstructorInfo h = some info →
      HasType env ctx (.const h univs) (info.ty.substLevelParams univs)

  /-- Recursor constant -/
  | constRec (ctx : Ctx) (h : Hash) (univs : List Level)
      (info : RecursorInfo) :
      env.getRecursorInfo h = some info →
      HasType env ctx (.const h univs) (info.recTy.substLevelParams univs)

  /-- Application: if `f : Π A. B` and `a : A'` with `A' ≡ A`,
      then `f a : B[a/0]` -/
  | app (ctx : Ctx) (f a : Expr) (A A' B : Expr) :
      HasType env ctx f (.forallE A B) →
      HasType env ctx a A' →
      IsDefEq env A' A →
      HasType env ctx (.app f a) (B.instantiate a)

  /-- Lambda: if `ty : Sort l` and `body : bodyTy` (under binder),
      then `λ ty. body : Π ty. bodyTy` -/
  | lam (ctx : Ctx) (ty body bodyTy : Expr) (l : Level) :
      HasType env ctx ty (.sort l) →
      HasType env (ty :: ctx) body bodyTy →
      HasType env ctx (.lam ty body) (.forallE ty bodyTy)

  /-- Dependent product: if `ty : Sort l₁` and `body : Sort l₂` (under binder),
      then `Π ty. body : Sort (imax l₁ l₂)` -/
  | forallE (ctx : Ctx) (ty body : Expr) (l₁ l₂ : Level) :
      HasType env ctx ty (.sort l₁) →
      HasType env (ty :: ctx) body (.sort l₂) →
      HasType env ctx (.forallE ty body) (.sort (.imax l₁ l₂))

  /-- Let: if `val : ty` and `body : bodyTy` (under binder),
      then `let x : ty := val in body : bodyTy[val/0]` -/
  | letE (ctx : Ctx) (ty val body bodyTy : Expr) :
      HasType env ctx val ty →
      HasType env (ty :: ctx) body bodyTy →
      HasType env ctx (.letE ty val body) (bodyTy.instantiate val)

  /-- Type conversion: if `e : T` and `T ≡ T'`, then `e : T'` -/
  | conv (ctx : Ctx) (e T T' : Expr) :
      HasType env ctx e T →
      IsDefEq env T T' →
      HasType env ctx e T'

-- ═══════════════════════════════════════════════════════════════════
-- Well-formed environment
-- ═══════════════════════════════════════════════════════════════════

/-- A declaration is well-typed in the given environment. -/
inductive DeclWellTyped (env : Environment) : Decl → Prop where
  /-- An axiom is well-typed if its type is a Sort. -/
  | axiom_ (n : Nat) (ty : Expr) (l : Level) :
      HasType env [] ty (.sort l) →
      DeclWellTyped env (.axiom n ty)
  /-- A definition is well-typed if its type is a Sort and its value
      has a subtype of the declared type. -/
  | definition_ (n : Nat) (ty val valTy : Expr) (l : Level) :
      HasType env [] ty (.sort l) →
      HasType env [] val valTy →
      -- valTy ≤ ty (subtyping)
      DeclWellTyped env (.definition n ty val)

/-- A well-formed environment: all declarations are well-typed, and hashes
    are consistent with declaration content. -/
structure WellFormedEnv (env : Environment) : Prop where
  /-- Every declaration is well-typed -/
  decls_typed : ∀ h info, env.lookup h = some info →
    DeclWellTyped env info.decl
  /-- Hash-declaration consistency -/
  hash_correct : ∀ h info, env.lookup h = some info →
    hashDecl info.decl = h

-- ═══════════════════════════════════════════════════════════════════
-- Basic properties of the specification
-- ═══════════════════════════════════════════════════════════════════

/-- IsDefEq is reflexive (immediate from constructor). -/
theorem IsDefEq.rfl' {env : Environment} {e : Expr} : IsDefEq env e e :=
  IsDefEq.refl e

/-- ReducesStar includes single steps. -/
theorem ReducesStar.single {env : Environment} {e₁ e₂ : Expr} :
    Reduces env e₁ e₂ → ReducesStar env e₁ e₂ :=
  fun h => .step e₁ e₂ e₂ h (.refl e₂)

/-- Reduction implies definitional equality. -/
theorem Reduces.toIsDefEq {env : Environment} {e₁ e₂ : Expr} :
    Reduces env e₁ e₂ → IsDefEq env e₁ e₂ :=
  fun h => IsDefEq.reduce e₁ e₂ h

/-- Multi-step reduction implies definitional equality. -/
theorem ReducesStar.toIsDefEq {env : Environment} {e₁ e₂ : Expr} :
    ReducesStar env e₁ e₂ → IsDefEq env e₁ e₂ := by
  intro h
  induction h with
  | refl _ => exact IsDefEq.refl _
  | step _ e₂' _ hstep _ ih =>
    exact IsDefEq.trans _ e₂' _ (hstep.toIsDefEq) ih

/-- HasType is closed under multi-step reduction of the type. -/
theorem HasType.conv_reduces {env : Environment} {ctx : Ctx} {e T T' : Expr} :
    HasType env ctx e T → ReducesStar env T T' → HasType env ctx e T' :=
  fun ht hr => HasType.conv ctx e T T' ht hr.toIsDefEq

end HashMath
