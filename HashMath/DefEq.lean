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

-- Helper to extract the field type from a constructor type,
-- substituting parameters and earlier fields from the struct value.
private partial def getFieldType (env : Environment) (ctorTy : Expr) (numParams : Nat)
    (idx : Nat) (struct : Expr) (_typeName : Hash) : Expr :=
  let structWhnf := whnf env struct
  let (_, structArgs) := structWhnf.getAppFnArgs
  go ctorTy 0 numParams idx structArgs
where
  go (ty : Expr) (current : Nat) (numParams idx : Nat)
      (structArgs : List Expr) : Expr :=
    match ty with
    | .forallE domTy body =>
      if current == numParams + idx then
        domTy
      else
        let argVal := structArgs.getD current (.sort .zero)
        go (body.instantiate argVal) (current + 1) numParams idx structArgs
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
    | some ty => .ok (ty.liftN (i + 1))
    | none => .error s!"inferType: bound variable index {i} out of range (context size {ctx.length})"
  | .sort l => .ok (.sort (.succ l))
  | .const h univs =>
    -- Check regular declarations (axioms, definitions)
    match env.getDeclType h univs with
    | some ty => .ok ty
    | none =>
      -- Check inductive types (by derived type hash)
      match env.getInductiveBlockForType h with
      | some (block, typeIdx) =>
        match block.types[typeIdx]? with
        | some indTy => .ok (indTy.type.substLevelParams univs)
        | none => .error "inferType: invalid inductive type index"
      | none =>
        -- Check constructors
        match env.getConstructorInfo h with
        | some ctorInfo => .ok (ctorInfo.ty.substLevelParams univs)
        | none =>
          -- Check recursors
          match env.getRecursorInfo h with
          | some recInfo => .ok (recInfo.recTy.substLevelParams univs)
          | none =>
            -- Check inductive blocks (by block hash) and quotients
            match env.lookup h with
            | some info =>
              match info.decl with
              | .inductive block =>
                match block.types.head? with
                | some indTy => .ok (indTy.type.substLevelParams univs)
                | none => .error "inferType: empty inductive block"
              | .quotient kind => .ok ((quotientType kind).substLevelParams univs)
              | _ => .error "inferType: declaration has no type"
            | none => .error "inferType: unknown constant"
  | .app f a => do
    let fTy ← inferType env ctx f
    let fTy' := whnf env fTy
    match fTy' with
    | .forallE domTy bodyTy =>
      let aTy ← inferType env ctx a
      if !(isDefEq env ctx aTy domTy) then
        .error "inferType: argument type mismatch in application"
      else
        .ok (bodyTy.instantiate a)
    | _ => .error "inferType: function expected in application"
  | .lam ty body => do
    let tyTy ← inferType env ctx ty
    let tyTy' := whnf env tyTy
    match tyTy' with
    | .sort _ => pure ()
    | _ => .error "inferType: lambda domain must be a type"
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
        | [ctorTy] => .ok (getFieldType env ctorTy block.numParams idx struct typeName)
        | _ => .error "inferType: proj on non-structure"
      | _ => .error "inferType: proj on mutual inductive"
    | none => .error "inferType: unknown inductive for projection"
  | .iref _ _ => .error "inferType: unresolved iref (should have been resolved before type-checking)"

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
  | .iref idx₁ ls₁, .iref idx₂ ls₂ =>
    idx₁ == idx₂ && ls₁.length == ls₂.length &&
    (List.zip ls₁ ls₂).all fun (l₁, l₂) => isLevelDefEq l₁ l₂
  -- η-expansion for lambdas
  | .lam ty body, _ =>
    let s' := Expr.app (s.liftN 1) (.bvar 0)
    isDefEq env (ty :: ctx) body s'
  | _, .lam ty body =>
    let t' := Expr.app (t.liftN 1) (.bvar 0)
    isDefEq env (ty :: ctx) t' body
  | _, _ =>
    -- Structural η for structures: compare field-by-field
    structEtaCheck env ctx t s

/-- Structural η: if both terms have the same structure type (single-constructor inductive),
    compare field-by-field via projections. -/
partial def structEtaCheck (env : Environment) (ctx : LocalCtx) (t s : Expr) : Bool :=
  match inferType env ctx t with
  | .error _ => false
  | .ok tTy =>
    let tTy' := whnf env tTy
    let (tyFn, _) := tTy'.getAppFnArgs
    match tyFn with
    | .const tyHash _ =>
      match env.getInductiveBlockForType tyHash with
      | some (block, _) =>
        if block.isStructureLike then
          match inferType env ctx s with
          | .error _ => false
          | .ok sTy =>
            let sTy' := whnf env sTy
            let (sTyFn, _) := sTy'.getAppFnArgs
            match sTyFn with
            | .const sTyHash _ =>
              if tyHash == sTyHash then
                match block.numFields with
                | some nFields =>
                  if nFields == 0 then true
                  else (List.range nFields).all fun i =>
                    isDefEq env ctx (.proj tyHash i t) (.proj tyHash i s)
                | none => false
              else false
            | _ => false
        else false
      | none => false
    | _ => false

/-- Check subtype relation: `t` is a subtype of `s`.
    Supports Sort cumulativity (Sort l₁ ≤ Sort l₂ when l₁ ≤ l₂)
    and covariant Π codomains. -/
partial def isSubtype (env : Environment) (ctx : LocalCtx) (t s : Expr) : Bool :=
  if isDefEq env ctx t s then true
  else
    let t' := whnf env t
    let s' := whnf env s
    match t', s' with
    | .sort l₁, .sort l₂ =>
      match isLevelLeq l₁ l₂ with
      | some true => true
      | _ => false
    | .forallE ty₁ body₁, .forallE ty₂ body₂ =>
      -- contravariant domain (must be defEq), covariant codomain
      isDefEq env ctx ty₁ ty₂ && isSubtype env (ty₁ :: ctx) body₁ body₂
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
