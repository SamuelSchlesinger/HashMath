/-
  HashMath.Elab — Elaboration from surface syntax to kernel terms

  Converts named variables to de Bruijn indices, resolves constant
  references by name→hash lookup, and translates surface declarations
  into kernel declarations.
-/

import HashMath.Syntax
import HashMath.Parser
import HashMath.TypeChecker

namespace HashMath

private def listIndexOf (l : List String) (name : String) : Option Nat :=
  go l 0
where
  go : List String → Nat → Option Nat
    | [], _ => none
    | x :: xs, i => if x == name then some i else go xs (i + 1)

private def listEnum (l : List α) : List (α × Nat) :=
  go l 0
where
  go : List α → Nat → List (α × Nat)
    | [], _ => []
    | x :: xs, i => (x, i) :: go xs (i + 1)

private def listHead (l : List String) (default : String) : String :=
  match l with
  | [] => default
  | x :: _ => x

structure ElabContext where
  locals : List String
  constants : Std.HashMap String Hash
  univParams : List String
  deriving Inhabited

namespace ElabContext

def empty : ElabContext := ⟨[], {}, []⟩

def pushLocal (ctx : ElabContext) (name : String) : ElabContext :=
  { ctx with locals := name :: ctx.locals }

end ElabContext

private def nSucc : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (nSucc n)

def elabLevel (ctx : ElabContext) (l : SLevel) : Except String Level :=
  match l with
  | .num n => .ok (nSucc n)
  | .param name =>
    match listIndexOf ctx.univParams name with
    | some idx => .ok (.param idx)
    | none => .error s!"unknown universe parameter '{name}'"
  | .succ l => do return .succ (← elabLevel ctx l)
  | .max l₁ l₂ => do return .max (← elabLevel ctx l₁) (← elabLevel ctx l₂)
  | .imax l₁ l₂ => do return .imax (← elabLevel ctx l₁) (← elabLevel ctx l₂)

partial def elabExpr (ctx : ElabContext) (e : SExpr) : Except String Expr :=
  match e with
  | .var name =>
    match listIndexOf ctx.locals name with
    | some idx => .ok (.bvar idx)
    | none =>
      match ctx.constants[name]? with
      | some h => .ok (.const h [])
      | none => .error s!"unknown variable '{name}'"
  | .sort l => do return .sort (← elabLevel ctx l)
  | .app f a => do return .app (← elabExpr ctx f) (← elabExpr ctx a)
  | .lam name ty body => do
    return .lam (← elabExpr ctx ty) (← elabExpr (ctx.pushLocal name) body)
  | .pi name ty body => do
    return .forallE (← elabExpr ctx ty) (← elabExpr (ctx.pushLocal name) body)
  | .arrow dom cod => do
    return .forallE (← elabExpr ctx dom) (← elabExpr (ctx.pushLocal "_") cod)
  | .letE name ty val body => do
    return .letE (← elabExpr ctx ty) (← elabExpr ctx val) (← elabExpr (ctx.pushLocal name) body)
  | .proj typeName idx struct =>
    match ctx.constants[typeName]? with
    | some h => do return .proj h idx (← elabExpr ctx struct)
    | none => .error s!"unknown type '{typeName}' in projection"

/-- Elaborate a constructor type, replacing references to types in the mutual block with iref. -/
partial def elabCtorExpr (ctx : ElabContext) (typeNames : List String)
    (univLevels : List Level) (e : SExpr) : Except String Expr :=
  match e with
  | .var name =>
    match listIndexOf typeNames name with
    | some idx => .ok (.iref idx univLevels)
    | none =>
      match listIndexOf ctx.locals name with
      | some idx => .ok (.bvar idx)
      | none =>
        match ctx.constants[name]? with
        | some h => .ok (.const h [])
        | none => .error s!"unknown variable '{name}' in constructor type"
  | .sort l => do return .sort (← elabLevel ctx l)
  | .app f a => do
    return .app (← elabCtorExpr ctx typeNames univLevels f)
               (← elabCtorExpr ctx typeNames univLevels a)
  | .lam name ty body => do
    return .lam (← elabCtorExpr ctx typeNames univLevels ty)
               (← elabCtorExpr (ctx.pushLocal name) typeNames univLevels body)
  | .pi name ty body => do
    return .forallE (← elabCtorExpr ctx typeNames univLevels ty)
                   (← elabCtorExpr (ctx.pushLocal name) typeNames univLevels body)
  | .arrow dom cod => do
    return .forallE (← elabCtorExpr ctx typeNames univLevels dom)
                   (← elabCtorExpr (ctx.pushLocal "_") typeNames univLevels cod)
  | .letE name ty val body => do
    return .letE (← elabCtorExpr ctx typeNames univLevels ty)
               (← elabCtorExpr ctx typeNames univLevels val)
               (← elabCtorExpr (ctx.pushLocal name) typeNames univLevels body)
  | .proj typeName idx struct =>
    match ctx.constants[typeName]? with
    | some h => do return .proj h idx (← elabCtorExpr ctx typeNames univLevels struct)
    | none => .error s!"unknown type '{typeName}' in projection"

inductive ElabResult where
  | declared : String → Hash → ElabResult
  | checked : Expr → Expr → ElabResult
  | evaluated : Expr → Expr → ElabResult
  | printed : String → String → ElabResult
  deriving Repr

structure Codebase where
  env : Environment
  names : Std.HashMap String Hash
  hashToName : Std.HashMap Hash String
  deriving Inhabited

namespace Codebase

def empty : Codebase := ⟨Environment.empty, {}, {}⟩

def toElabCtx (cb : Codebase) (univParams : List String := []) : ElabContext :=
  { locals := [], constants := cb.names, univParams }

def registerName (cb : Codebase) (name : String) (h : Hash) : Codebase :=
  { cb with
    names := cb.names.insert name h
    hashToName := cb.hashToName.insert h name }

def resolve (cb : Codebase) (name : String) : Option Hash :=
  cb.names[name]?

def ppLevel (_cb : Codebase) (univParams : List String) : Level → String
  | .zero => "0"
  | .succ l => s!"succ ({_cb.ppLevel univParams l})"
  | .max l₁ l₂ => s!"max ({_cb.ppLevel univParams l₁}) ({_cb.ppLevel univParams l₂})"
  | .imax l₁ l₂ => s!"imax ({_cb.ppLevel univParams l₁}) ({_cb.ppLevel univParams l₂})"
  | .param n => univParams.getD n s!"?u{n}"

def ppLevelSimple (cb : Codebase) (univParams : List String) : Level → String
  | .zero => "Prop"
  | .succ .zero => "Type"
  | .succ l => s!"Type {cb.ppLevel univParams l}"
  | l => s!"Sort ({cb.ppLevel univParams l})"

private def reprHashShort (h : Hash) : String :=
  let bytes := h.bytes
  s!"{bytes.get! 0}{bytes.get! 1}{bytes.get! 2}{bytes.get! 3}..."

private partial def freshName (existing : List String) (base : String) : String :=
  if existing.any (· == base) then freshName existing (base ++ "'")
  else base

partial def ppExpr (cb : Codebase) (univParams : List String := [])
    (boundNames : List String := []) : Expr → String
  | .bvar i => boundNames.getD i s!"#{i}"
  | .sort l => cb.ppLevelSimple univParams l
  | .const h ls =>
    let name := match cb.hashToName[h]? with | some n => n | none => s!"@{reprHashShort h}"
    if ls.isEmpty then name
    else
      let lvlStrs : List String := ls.map (cb.ppLevel univParams)
      let joined := String.intercalate ", " lvlStrs
      name ++ ".{" ++ joined ++ "}"
  | .app f a =>
    let fStr := cb.ppExpr univParams boundNames f
    let aStr := match a with
      | .app _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _ =>
        s!"({cb.ppExpr univParams boundNames a})"
      | _ => cb.ppExpr univParams boundNames a
    s!"{fStr} {aStr}"
  | .lam ty body =>
    let tyStr := cb.ppExpr univParams boundNames ty
    let name := freshName boundNames "x"
    let bodyStr := cb.ppExpr univParams (name :: boundNames) body
    s!"(λ ({name} : {tyStr}) => {bodyStr})"
  | .forallE ty body =>
    let tyStr := cb.ppExpr univParams boundNames ty
    if body.hasLooseBVarGe 0 then
      let name := freshName boundNames "x"
      let bodyStr := cb.ppExpr univParams (name :: boundNames) body
      s!"(∀ ({name} : {tyStr}), {bodyStr})"
    else
      let bodyStr := cb.ppExpr univParams ("_" :: boundNames) body
      s!"({tyStr} → {bodyStr})"
  | .letE ty val body =>
    let tyStr := cb.ppExpr univParams boundNames ty
    let valStr := cb.ppExpr univParams boundNames val
    let name := freshName boundNames "x"
    let bodyStr := cb.ppExpr univParams (name :: boundNames) body
    s!"(let {name} : {tyStr} := {valStr} in {bodyStr})"
  | .proj h i s =>
    let typeName := match cb.hashToName[h]? with | some n => n | none => s!"@{reprHashShort h}"
    let sStr := match s with
      | .app _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _ =>
        s!"({cb.ppExpr univParams boundNames s})"
      | _ => cb.ppExpr univParams boundNames s
    s!"{typeName}.{i} {sStr}"
  | .iref idx _ls => s!"(iref {idx})"

/-- Elaborate one inductive type from surface syntax. -/
private def elabOneInductiveType (ctx : ElabContext) (univParams : List String)
    (typeNames : List String) (_numParams : Nat)
    (sind : SInductiveType) (_tidx : Nat) : Except String (InductiveType × List String) := do
  let ty' ← elabExpr ctx sind.type
  let univLevels := (List.range univParams.length).map (fun i => Level.param i)
  let ctorsAndNames ← elabCtors ctx typeNames univLevels sind.ctors
  let elabCtors := ctorsAndNames.map (·.1)
  let cNames := ctorsAndNames.map (fun p => sind.name ++ "." ++ p.2)
  return ({ type := ty', ctors := elabCtors }, cNames)
where
  elabCtors (ctx : ElabContext) (typeNames : List String) (univLevels : List Level)
      : List SConstructor → Except String (List (Expr × String))
    | [] => .ok []
    | sctor :: rest => do
      let ctorTy ← elabCtorExpr ctx typeNames univLevels sctor.type
      let rest' ← elabCtors ctx typeNames univLevels rest
      return (ctorTy, sctor.name) :: rest'

/-- Register all names for an inductive block (types, constructors, recursors). -/
private def registerInductiveNames (cb : Codebase) (blockHash : Hash)
    (typeNames : List String) (ctorNames : List (List String)) : Codebase :=
  let cb := registerTypes cb blockHash typeNames 0
  registerCtors cb blockHash ctorNames 0
where
  registerTypes (cb : Codebase) (blockHash : Hash) : List String → Nat → Codebase
    | [], _ => cb
    | tname :: rest, tidx =>
      let typeHash := hashIndType blockHash tidx
      let recHash := hashRec blockHash tidx
      let cb := cb.registerName tname typeHash
      let cb := cb.registerName (tname ++ ".rec") recHash
      registerTypes cb blockHash rest (tidx + 1)
  registerCtors (cb : Codebase) (blockHash : Hash) : List (List String) → Nat → Codebase
    | [], _ => cb
    | cnames :: rest, tidx =>
      let cb := registerCtorsForType cb blockHash cnames tidx 0
      registerCtors cb blockHash rest (tidx + 1)
  registerCtorsForType (cb : Codebase) (blockHash : Hash) : List String → Nat → Nat → Codebase
    | [], _, _ => cb
    | cname :: rest, tidx, cidx =>
      let ctorHash := hashCtor blockHash tidx cidx
      let cb := cb.registerName cname ctorHash
      registerCtorsForType cb blockHash rest tidx (cidx + 1)

/-- Elaborate all inductive types in a block. -/
private def elabInductiveTypes (ctx : ElabContext) (univParams : List String)
    (typeNames : List String) (numParams : Nat)
    : List SInductiveType → Nat → Except String (List InductiveType × List (List String))
  | [], _ => .ok ([], [])
  | sind :: rest, tidx => do
    let (indTy, cNames) ← elabOneInductiveType ctx univParams typeNames numParams sind tidx
    let (restTypes, restNames) ← elabInductiveTypes ctx univParams typeNames numParams rest (tidx + 1)
    return (indTy :: restTypes, cNames :: restNames)

def processCommand (cb : Codebase) (cmd : Command) : Except String (Codebase × ElabResult) := do
  match cmd with
  | .decl (.axiom_ name univParams ty) =>
    let ctx := cb.toElabCtx univParams
    let ty' ← elabExpr ctx ty
    let decl := Decl.axiom univParams.length ty'
    let (h, env') ← checkDecl cb.env decl
    let cb' := { cb with env := env' }.registerName name h
    return (cb', .declared name h)

  | .decl (.def_ name univParams ty val) =>
    let ctx := cb.toElabCtx univParams
    let ty' ← elabExpr ctx ty
    let val' ← elabExpr ctx val
    let decl := Decl.definition univParams.length ty' val'
    let (h, env') ← checkDecl cb.env decl
    let cb' := { cb with env := env' }.registerName name h
    return (cb', .declared name h)

  | .decl (.inductive_ univParams numParams types) =>
    let ctx := cb.toElabCtx univParams
    let typeNames := types.map (·.name)
    let (elabTypes, ctorNames) ← elabInductiveTypes ctx univParams typeNames numParams types 0
    let block : InductiveBlock := {
      numUnivParams := univParams.length
      numParams := numParams
      types := elabTypes
    }
    let (h, env') ← checkDecl cb.env (Decl.inductive block)
    let cb' := { cb with env := env' }
    let cb' := registerInductiveNames cb' h typeNames ctorNames
    return (cb', .declared (listHead typeNames "inductive") h)

  | .check e =>
    let ctx := cb.toElabCtx
    let e' ← elabExpr ctx e
    let ty ← inferTypeClosed cb.env e'
    return (cb, .checked e' ty)

  | .eval e =>
    let ctx := cb.toElabCtx
    let e' ← elabExpr ctx e
    let result := whnf cb.env e'
    return (cb, .evaluated e' result)

  | .print name =>
    match cb.resolve name with
    | some h =>
      let info := match cb.env.lookup h with
        | some di => s!"{repr di.decl}"
        | none =>
          match cb.env.getConstructorInfo h with
          | some ci => s!"constructor (cIdx: {ci.cIdx}, nFields: {ci.nFields})"
          | none =>
            match cb.env.getRecursorInfo h with
            | some ri => s!"recursor (nMotives: {ri.nMotives}, nMinors: {ri.nMinors})"
            | none => "not found"
      return (cb, .printed name info)
    | none => .error s!"unknown name '{name}'"

private def processCommandList (cb : Codebase) : List Command → List ElabResult →
    Except String (Codebase × List ElabResult)
  | [], results => .ok (cb, results.reverse)
  | cmd :: rest, results => do
    let (cb', result) ← cb.processCommand cmd
    processCommandList cb' rest (result :: results)

def processSource (cb : Codebase) (source : String) : Except String (Codebase × List ElabResult) := do
  let cmds ← parseCommands source
  processCommandList cb cmds []

end Codebase

end HashMath
