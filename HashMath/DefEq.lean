/-
  HashMath.DefEq — Definitional equality and type inference for HashMath CIC
-/

import HashMath.Reduce
import HashMath.Inductive
import HashMath.Quotient

namespace HashMath

/-- Check level equality after normalization. -/
def isLevelDefEq (l₁ l₂ : Level) : Bool :=
  l₁.beqNorm l₂

/-- Check cumulativity: Sort l₁ ≤ Sort l₂ -/
def isLevelLeq (l₁ l₂ : Level) : Option Bool :=
  l₁.normalize.leq l₂.normalize

-- Helper to extract the field type from a constructor type
private def getFieldType (ctorTy : Expr) (numParams : Nat) (idx : Nat) : Expr :=
  go ctorTy 0 numParams idx
where
  go (ty : Expr) (current : Nat) (numParams : Nat) (idx : Nat) : Expr :=
    match ty with
    | .forallE domTy body =>
      if current < numParams then go body (current + 1) numParams idx
      else if current == numParams + idx then domTy
      else go body (current + 1) numParams idx
    | _ => .sort .zero

/-- A local context mapping de Bruijn indices to their types.
    Index 0 is the most recently bound variable. -/
abbrev LocalCtx := List Expr

mutual

/-- Infer the type of an expression.
    `ctx` is the local context: `ctx[i]` is the type of `bvar i`. -/
partial def inferType (env : Environment) (ctx : LocalCtx) (e : Expr) : Except String Expr :=
  match e with
  | .bvar i =>
    match ctx[i]? with
    | some ty => .ok ty
    | none => .error s!"inferType: bound variable index {i} out of range (context size {ctx.length})"
  | .sort l => .ok (.sort (.succ l))
  | .const h univs =>
    match env.getDeclType h univs with
    | some ty => .ok ty
    | none =>
      match env.lookup h with
      | some info =>
        match info.decl with
        | .inductive block =>
          match block.types.head? with
          | some indTy => .ok (indTy.type.substLevelParams univs)
          | none => .error "inferType: empty inductive block"
        | .quotient kind => .ok (quotientType kind)
        | _ => .error "inferType: declaration has no type"
      | none => .error "inferType: unknown constant"
  | .app f a => do
    let fTy ← inferType env ctx f
    let fTy' := whnf env fTy
    match fTy' with
    | .forallE _domTy bodyTy => .ok (bodyTy.instantiate a)
    | _ => .error "inferType: function expected in application"
  | .lam ty body => do
    let _ ← inferType env ctx ty
    -- Go under the binder: push ty onto context
    let bodyTy ← inferType env (ty :: ctx) body
    .ok (.forallE ty bodyTy)
  | .forallE ty body => do
    let tyTy ← inferType env ctx ty
    let tyTy' := whnf env tyTy
    -- Go under the binder: push ty onto context
    let bodyTy ← inferType env (ty :: ctx) body
    let bodyTy' := whnf env bodyTy
    match tyTy', bodyTy' with
    | .sort l₁, .sort l₂ => .ok (.sort (.imax l₁ l₂))
    | .sort _, _ => .error "inferType: forall body must be a type"
    | _, _ => .error "inferType: forall domain must be a type"
  | .letE ty val body => do
    let _ ← inferType env ctx ty
    let valTy ← inferType env ctx val
    if !(isDefEq env ctx valTy ty) then
      .error "inferType: let value type mismatch"
    else
      -- Go under the let binder: push ty onto context
      let bodyTy ← inferType env (ty :: ctx) body
      .ok (bodyTy.instantiate val)
  | .proj typeName idx struct => do
    let _structTy ← inferType env ctx struct
    match env.getInductiveBlock typeName with
    | some block =>
      match block.types with
      | [indTy] =>
        match indTy.ctors with
        | [ctorTy] => .ok (getFieldType ctorTy block.numParams idx)
        | _ => .error "inferType: proj on non-structure"
      | _ => .error "inferType: proj on mutual inductive"
    | none => .error "inferType: unknown inductive for projection"

/-- Check definitional equality of two expressions. -/
partial def isDefEq (env : Environment) (ctx : LocalCtx) (t s : Expr) : Bool :=
  if t == s then true
  else
    let t' := whnfCore env t
    let s' := whnfCore env s
    if t' == s' then true
    else if proofIrrelCheck env ctx t' s' then true
    else
      let t'' := whnf env t'
      let s'' := whnf env s'
      if t'' == s'' then true
      else isDefEqCore env ctx t'' s''

/-- Check proof irrelevance: if both terms have types in Prop, they're equal. -/
partial def proofIrrelCheck (env : Environment) (ctx : LocalCtx) (t s : Expr) : Bool :=
  match inferType env ctx t with
  | .error _ => false
  | .ok tTy =>
    let tTyTy := match inferType env ctx tTy with
      | .ok ty => some (whnf env ty)
      | .error _ => none
    match tTyTy with
    | some (.sort .zero) =>
      match inferType env ctx s with
      | .ok sTy => isDefEq env ctx tTy sTy
      | .error _ => false
    | _ => false

/-- Structural definitional equality check (after whnf). -/
partial def isDefEqCore (env : Environment) (ctx : LocalCtx) (t s : Expr) : Bool :=
  match t, s with
  | .bvar i, .bvar j => i == j
  | .sort l₁, .sort l₂ => isLevelDefEq l₁ l₂
  | .const h₁ ls₁, .const h₂ ls₂ =>
    h₁ == h₂ && ls₁.length == ls₂.length &&
    (List.zip ls₁ ls₂).all fun (l₁, l₂) => isLevelDefEq l₁ l₂
  | .app f₁ a₁, .app f₂ a₂ =>
    isDefEq env ctx f₁ f₂ && isDefEq env ctx a₁ a₂
  | .lam ty₁ body₁, .lam ty₂ body₂ =>
    isDefEq env ctx ty₁ ty₂ && isDefEq env (ty₁ :: ctx) body₁ body₂
  | .forallE ty₁ body₁, .forallE ty₂ body₂ =>
    isDefEq env ctx ty₁ ty₂ && isDefEq env (ty₁ :: ctx) body₁ body₂
  | .letE ty₁ val₁ body₁, .letE ty₂ val₂ body₂ =>
    isDefEq env ctx ty₁ ty₂ && isDefEq env ctx val₁ val₂ &&
    isDefEq env (ty₁ :: ctx) body₁ body₂
  | .proj h₁ i₁ s₁, .proj h₂ i₂ s₂ =>
    h₁ == h₂ && i₁ == i₂ && isDefEq env ctx s₁ s₂
  -- η-expansion
  | .lam ty body, _ =>
    let s' := Expr.app (s.liftN 1) (.bvar 0)
    isDefEq env (ty :: ctx) body s'
  | _, .lam ty body =>
    let t' := Expr.app (t.liftN 1) (.bvar 0)
    isDefEq env (ty :: ctx) t' body
  | _, _ => false

end -- mutual

-- Convenience wrappers for closed terms (no local context)

/-- Infer the type of a closed expression. -/
def inferTypeClosed (env : Environment) (e : Expr) : Except String Expr :=
  inferType env [] e

/-- Check definitional equality of closed expressions. -/
def isDefEqClosed (env : Environment) (t s : Expr) : Bool :=
  isDefEq env [] t s

end HashMath
