/-
  HashMath.DefEq — Definitional equality and type inference for HashMath CIC
-/

import HashMath.Reduce
import HashMath.Inductive
import HashMath.Quotient

namespace HashMath

/-- Check level equality after normalization.
    Falls back to numeric comparison for closed ground levels. -/
partial def isLevelDefEq (l₁ l₂ : Level) : Bool :=
  levelEqNorm l₁.normalize l₂.normalize
where
  levelEqNorm (a b : Level) : Bool :=
    a == b ||
    match (a.toNat, b.toNat) with
    | (some n₁, some n₂) => n₁ == n₂
    | _ =>
      match a, b with
      | .succ a', .succ b' => levelEqNorm a' b'
      | .max a₁ a₂, .max b₁ b₂ =>
        (levelEqNorm a₁ b₁ && levelEqNorm a₂ b₂) ||
        (levelEqNorm a₁ b₂ && levelEqNorm a₂ b₁)
      | .imax .zero x, _ => levelEqNorm x b
      | _, .imax .zero x => levelEqNorm a x
      | .imax a₁ a₂, .imax b₁ b₂ => levelEqNorm a₁ b₁ && levelEqNorm a₂ b₂
      | _, _ => false

/-- Check cumulativity: Sort l₁ ≤ Sort l₂ -/
def isLevelLeq (l₁ l₂ : Level) : Option Bool :=
  l₁.normalize.leq l₂.normalize

-- Helper to extract the field type from a constructor type,
-- substituting parameters and earlier fields from the struct value.
private partial def getFieldType (env : Environment) (ctorTy : Expr) (numParams : Nat)
    (idx : Nat) (struct : Expr) (typeName : Hash)
    (structTy : Option Expr := none) : Expr :=
  let structWhnf := whnf env struct
  let (fn, structArgs) := structWhnf.getAppFnArgs
  let effectiveArgs := match fn with
    | .const _ _ => structArgs  -- constructor: use args directly
    | _ =>
      -- Non-constructor: use type args for params, projections for fields
      match structTy with
      | some sTy =>
        let sTyWhnf := whnf env sTy
        let typeArgs := sTyWhnf.getAppArgs
        let fieldProjections := (List.range idx).map (fun i => Expr.proj typeName i struct)
        typeArgs ++ fieldProjections
      | none => structArgs
  go ctorTy 0 numParams idx effectiveArgs
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

/-- Resolve iref nodes in a single-type inductive block.
    All iref indices map to the given type hash (since there's only one type). -/
private def resolveIRefSingleType (typeName : Hash) : Expr → Expr
  | .iref _ ls => .const typeName ls
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const h ls => .const h ls
  | .app f a => .app (resolveIRefSingleType typeName f) (resolveIRefSingleType typeName a)
  | .lam ty body => .lam (resolveIRefSingleType typeName ty) (resolveIRefSingleType typeName body)
  | .forallE ty body => .forallE (resolveIRefSingleType typeName ty) (resolveIRefSingleType typeName body)
  | .letE ty val body => .letE (resolveIRefSingleType typeName ty) (resolveIRefSingleType typeName val) (resolveIRefSingleType typeName body)
  | .proj h i s => .proj h i (resolveIRefSingleType typeName s)

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
  | .const h univs => do
    -- Validate universe parameter count
    if let some expected := env.getExpectedUnivParams h then
      if univs.length != expected then
        throw s!"inferType: constant has {univs.length} universe arguments but expected {expected}"
    -- Check regular declarations (axioms, definitions)
    match env.getDeclType h univs with
    | some ty => .ok ty
    | none =>
      -- Check inductive types (by derived type hash)
      match env.getInductiveBlockForType h with
      | some (block, typeIdx) =>
        match block.types[typeIdx]? with
        | some indTy => .ok (indTy.type.substLevelParams univs)
        | none => .error s!"inferType: invalid inductive type index {typeIdx}"
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
      if !(isSubtype env ctx aTy domTy) then
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
    let structTy ← inferType env ctx struct
    match env.getInductiveBlockForType typeName with
    | some (block, _) =>
      match block.types with
      | [indTy] =>
        match indTy.ctors with
        | [rawCtorTy] =>
          let ctorTy := resolveIRefSingleType typeName rawCtorTy
          .ok (getFieldType env ctorTy block.numParams idx struct typeName (some structTy))
        | _ => .error "inferType: proj on non-structure"
      | _ => .error "inferType: proj on mutual inductive"
    | none => .error "inferType: unknown inductive for projection"
  | .iref idx _ => .error s!"inferType: unresolved iref {idx} (should have been resolved before type-checking)"

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
  -- Only try struct eta if at least one side is a constructor application (after whnf).
  -- Otherwise projections won't reduce and we'll loop:
  -- structEtaCheck(t,s) → isDefEq(proj i t, proj i s) → isDefEq(t,s) → structEtaCheck(t,s)
  let isCtorApp (e : Expr) : Bool :=
    match (whnf env e).getAppFn with
    | .const h _ => match env.getConstructorInfo h with | some _ => true | none => false
    | _ => false
  if !isCtorApp t && !isCtorApp s then false
  else
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
                -- Also check full applied types match
                if !(isDefEq env ctx tTy' sTy') then false
                else match block.numFields with
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
