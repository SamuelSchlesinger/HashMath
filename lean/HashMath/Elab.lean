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

/-! ## Codebase (moved before elabExprCore so match elaboration can use it) -/

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

end Codebase

/-! ## Match elaboration helpers -/

/-- Extract the head type name and arguments from a surface type expression.
    E.g., `List A` → `("List", [A])` -/
private def getTypeNameAndArgs : SExpr → Option (String × List SExpr)
  | .var name _ => some (name, [])
  | .app f a =>
    match getTypeNameAndArgs f with
    | some (name, args) => some (name, args ++ [a])
    | none => none
  | _ => none

/-- Strip `numSkip` leading forallE binders from a type, instantiating each with the
    corresponding expression from `skipExprs`. Then extract `numExtract` forallE domain types. -/
private def extractTelescope (ty : Expr) (numSkip : Nat) (skipExprs : List Expr)
    (univLevels : List Level) (numExtract : Nat) : List Expr :=
  let ty := ty.substLevelParams univLevels
  let inner := instantiateN ty numSkip skipExprs
  extractN inner numExtract []
where
  instantiateN : Expr → Nat → List Expr → Expr
    | ty, 0, _ => ty
    | .forallE _ body, n+1, p :: ps => instantiateN (body.instantiate p) n ps
    | ty, _, _ => ty
  extractN : Expr → Nat → List Expr → List Expr
    | _, 0, acc => acc.reverse
    | .forallE ty body, n+1, acc => extractN body n (ty :: acc)
    | _, _, acc => acc.reverse

/-- Compute IH types for recursive fields in a match minor.
    Each recursive field gets an IH whose type is the motive applied to
    the index args and the recursive field variable. -/
private def computeIHTypes (motive : Expr) (nFields : Nat)
    (fieldTypes : List Expr) (recursiveFields : List (Nat × Nat × List Expr))
    (numParams : Nat) : List Expr :=
  go recursiveFields 0
where
  go : List (Nat × Nat × List Expr) → Nat → List Expr
    | [], _ => []
    | (recIdx, _, _) :: rest, k =>
      let depth := nFields + k
      let motiveL := motive.liftN depth
      let fieldBvar := Expr.bvar (depth - 1 - recIdx)
      -- Get index args from the field type (for indexed types)
      let idxArgs := match fieldTypes[recIdx]? with
        | some ft => ft.getAppArgs.drop numParams
        | none => []
      let liftedIdxArgs := idxArgs.map (fun e => e.liftN (depth - recIdx))
      let ihType := Expr.mkAppN motiveL (liftedIdxArgs ++ [fieldBvar])
      ihType :: go rest (k + 1)

/-- Find the index of a constructor name in a list. -/
private def findArmIdx : List String → String → Option Nat
  | [], _ => none
  | c :: cs, name => if c == name then some 0
    else match findArmIdx cs name with
      | some i => some (i + 1)
      | none => none

/-- Elaborate a match expression by desugaring to a recursor application.
    `elabRec` is the recursive elaboration function (from elabExprCore). -/
private def elabMatchExpr
    (elabRec : ElabContext → SExpr → Except String Expr)
    (elabLvl : SLevel → Except String Level)
    (ctx : ElabContext) (cb : Codebase)
    (univs : List SLevel) (scrutinee : SExpr) (asVars : List String)
    (typeExpr : SExpr) (returnExpr : SExpr)
    (armCtors : List String) (armVarss : List (List String)) (armBodies : List SExpr)
    : Except String Expr := do
  -- 1. Extract type name and args
  let (typeName, typeArgSExprs) ← match getTypeNameAndArgs typeExpr with
    | some p => pure p
    | none => .error "match: type expression must be a type name applied to arguments"

  -- 2. Look up type info
  let typeHash ← match cb.resolve typeName with
    | some h => pure h
    | none => .error s!"match: unknown type '{typeName}'"
  let (block, typeIdx) ← match cb.env.getInductiveBlockForType typeHash with
    | some info => pure info
    | none => .error s!"match: '{typeName}' is not an inductive type"
  let recName := typeName ++ ".rec"
  let recHash ← match cb.resolve recName with
    | some h => pure h
    | none => .error s!"match: could not find recursor '{recName}'"
  let recInfo ← match cb.env.getRecursorInfo recHash with
    | some ri => pure ri
    | none => .error s!"match: recursor info not found for '{recName}'"

  -- 3. Check non-mutual (for now)
  if recInfo.nMotives != 1 then
    .error "match: mutual inductive types are not supported in match expressions"
  else pure ()

  -- 4. Elaborate type arguments and split into params/indices
  let typeArgKExprs ← typeArgSExprs.mapM (elabRec ctx)
  let paramExprs := typeArgKExprs.take block.numParams
  let indexExprs := typeArgKExprs.drop block.numParams

  if paramExprs.length != block.numParams then
    .error s!"match: expected {block.numParams} type parameters for '{typeName}', got {paramExprs.length}"
  else pure ()

  -- 5. Compute universe levels for the recursor
  let recUnivLevels ← univs.mapM elabLvl
  -- If no explicit levels and recursor allows large elim, default to .{1}
  let recUnivLevels :=
    if recUnivLevels.isEmpty && recInfo.allowsLargeElim then
      [Level.succ Level.zero]
    else recUnivLevels
  let blockUnivLevels := recUnivLevels.take block.numUnivParams

  -- 6. Elaborate scrutinee
  let scrutineeK ← elabRec ctx scrutinee

  -- 7. Build motive
  let nIndices := recInfo.nIndices
  let indTy ← match block.types[typeIdx]? with
    | some ty => pure ty
    | none => .error "match: type index out of range"

  -- Get index types from the inductive type's type
  let indexTypes := extractTelescope indTy.type block.numParams paramExprs blockUnivLevels nIndices

  -- Build motive binder names: asVars padded with "_" to nIndices + 1
  let motiveBinderCount := nIndices + 1
  let motiveNames := asVars ++ (List.range (motiveBinderCount - asVars.length)).map (fun _ => "_")
  let motiveNames := motiveNames.take motiveBinderCount

  -- Push motive binder names onto context and elaborate return type
  let motiveCtx := motiveNames.foldl (fun c name => c.pushLocal name) ctx
  let returnK ← elabRec motiveCtx returnExpr

  -- Build major premise type at depth nIndices
  let typeConst := Expr.const typeHash blockUnivLevels
  let liftedParams := paramExprs.map (fun p => p.liftN nIndices)
  let indexBvars := (List.range nIndices).reverse.map (fun i => Expr.bvar i)
  let majorType := Expr.mkAppN typeConst (liftedParams ++ indexBvars)

  -- Build motive: fun (i0 : I0) ... (iK : IK) (x : T params i0...iK) => Return
  let motiveInner := Expr.lam majorType returnK
  let motive := indexTypes.foldr (fun idxTy acc => Expr.lam idxTy acc) motiveInner

  -- 8. Build minors (one per constructor, ordered by cIdx)
  let nCtors := indTy.ctors.length
  if armCtors.length != nCtors then
    .error s!"match: expected {nCtors} arms for type '{typeName}', got {armCtors.length}"
  else pure ()
  let minors ← buildMinors elabRec ctx cb block recInfo typeIdx motive paramExprs blockUnivLevels
      armCtors armVarss armBodies nCtors 0 []

  -- 9. Assemble recursor call: rec.{u} params motive minors indices scrutinee
  let recConst := Expr.const recHash recUnivLevels
  let result := Expr.mkAppN recConst (paramExprs ++ [motive] ++ minors ++ indexExprs ++ [scrutineeK])
  pure result
where
  buildMinors (elabRec : ElabContext → SExpr → Except String Expr)
      (ctx : ElabContext) (cb : Codebase) (block : InductiveBlock)
      (recInfo : RecursorInfo) (typeIdx : Nat) (motive : Expr)
      (paramExprs : List Expr) (blockUnivLevels : List Level)
      (armCtors : List String) (armVarss : List (List String)) (armBodies : List SExpr)
      (nCtors : Nat) (ctorIdx : Nat) (acc : List Expr) : Except String (List Expr) :=
    if ctorIdx >= nCtors then pure acc
    else do
      let ctorHash := hashCtor recInfo.blockHash typeIdx ctorIdx
      let ctorInfo ← match cb.env.getConstructorInfo ctorHash with
        | some ci => pure ci
        | none => .error s!"match: constructor info not found (index {ctorIdx})"
      let ctorName ← match cb.hashToName[ctorHash]? with
        | some n => pure n
        | none => .error s!"match: could not find name for constructor at index {ctorIdx}"

      -- Find matching arm
      let armIdx ← match findArmIdx armCtors ctorName with
        | some i => pure i
        | none => .error s!"match: missing arm for constructor '{ctorName}'"
      let armVars ← match armVarss[armIdx]? with
        | some v => pure v
        | none => .error "match: internal error (arm vars)"
      let armBody ← match armBodies[armIdx]? with
        | some b => pure b
        | none => .error "match: internal error (arm body)"

      let nFields := ctorInfo.nFields
      let nRecFields := ctorInfo.recursiveFields.length
      let expectedVars := nFields + nRecFields
      if armVars.length != expectedVars then
        .error s!"match: constructor '{ctorName}' expects {expectedVars} variables ({nFields} fields + {nRecFields} IHs), got {armVars.length}"
      else pure ()

      -- Compute field types from constructor type
      let fieldTypes := extractTelescope ctorInfo.ty block.numParams paramExprs blockUnivLevels nFields

      -- Elaborate arm body with all vars in scope
      let armCtx := armVars.foldl (fun c name => c.pushLocal name) ctx
      let minorBody ← elabRec armCtx armBody

      -- Compute IH types
      let ihTypes := computeIHTypes motive nFields fieldTypes ctorInfo.recursiveFields block.numParams

      -- Wrap body with IH lambdas (innermost), then field lambdas (outermost)
      let minor := ihTypes.foldr (fun ihTy acc => Expr.lam ihTy acc) minorBody
      let minor := fieldTypes.foldr (fun fTy acc => Expr.lam fTy acc) minor

      buildMinors elabRec ctx cb block recInfo typeIdx motive paramExprs blockUnivLevels
          armCtors armVarss armBodies nCtors (ctorIdx + 1) (acc ++ [minor])

/-! ## Expression elaboration -/

def elabLevel (ctx : ElabContext) (l : SLevel) : Except String Level :=
  match l with
  | .num n => .ok (Level.nSucc n)
  | .param name =>
    match listIndexOf ctx.univParams name with
    | some idx => .ok (.param idx)
    | none => .error s!"unknown universe parameter '{name}'"
  | .succ l => do return .succ (← elabLevel ctx l)
  | .max l₁ l₂ => do return .max (← elabLevel ctx l₁) (← elabLevel ctx l₂)
  | .imax l₁ l₂ => do return .imax (← elabLevel ctx l₁) (← elabLevel ctx l₂)

/-- Elaborate a surface expression to a kernel expression.
    When `irefCtx` is provided, variable references matching type names in the mutual block
    are elaborated as `iref` references instead of constants.
    When `cb` is provided, `match` expressions are supported. -/
partial def elabExprCore (ctx : ElabContext)
    (irefCtx : Option (List String × List Level))
    (cb : Option Codebase := none)
    (e : SExpr) : Except String Expr :=
  let rec_ := elabExprCore ctx irefCtx cb
  let recLocal := fun name => elabExprCore (ctx.pushLocal name) irefCtx cb
  match e with
  | .var name univArgs =>
    -- Check local variables first (they shadow type names and constants)
    match listIndexOf ctx.locals name with
    | some idx => .ok (.bvar idx)
    | none =>
      -- Then check type names (for constructor types in inductive blocks)
      match irefCtx.bind (fun (typeNames, univLevels) =>
          (listIndexOf typeNames name).map (fun idx => Expr.iref idx univLevels)) with
      | some e => .ok e
      | none =>
        match ctx.constants[name]? with
        | some h => do
          let univLevels ← univArgs.mapM (elabLevel ctx)
          .ok (.const h univLevels)
        | none => .error s!"unknown variable '{name}'"
  | .sort l => do return .sort (← elabLevel ctx l)
  | .app f a => do return .app (← rec_ f) (← rec_ a)
  | .lam name ty body => do
    return .lam (← rec_ ty) (← recLocal name body)
  | .pi name ty body => do
    return .forallE (← rec_ ty) (← recLocal name body)
  | .arrow dom cod => do
    return .forallE (← rec_ dom) (← recLocal "_" cod)
  | .letE name ty val body => do
    return .letE (← rec_ ty) (← rec_ val) (← recLocal name body)
  | .proj typeName idx struct =>
    match ctx.constants[typeName]? with
    | some h => do return .proj h idx (← rec_ struct)
    | none => .error s!"unknown type '{typeName}' in projection"
  | .match_ univs scrut asVars typeE retE armCtors armVarss armBodies =>
    match cb with
    | none => .error "match expressions require codebase context"
    | some codebase =>
      let elabRec := fun ctx' e => elabExprCore ctx' irefCtx cb e
      let elabLvl := elabLevel ctx
      elabMatchExpr elabRec elabLvl ctx codebase univs scrut asVars typeE retE armCtors armVarss armBodies

def elabExpr (ctx : ElabContext) (e : SExpr) (cb : Option Codebase := none) : Except String Expr :=
  elabExprCore ctx none cb e

/-- Elaborate a constructor type, replacing references to types in the mutual block with iref. -/
def elabCtorExpr (ctx : ElabContext) (typeNames : List String)
    (univLevels : List Level) (e : SExpr) (cb : Option Codebase := none) : Except String Expr :=
  elabExprCore ctx (some (typeNames, univLevels)) cb e

/-! ## Inductive type elaboration and command processing -/

namespace Codebase

/-- Elaborate one inductive type from surface syntax. -/
private def elabOneInductiveType (ctx : ElabContext) (univParams : List String)
    (typeNames : List String)
    (sind : SInductiveType) : Except String (InductiveType × List String) := do
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
    (typeNames : List String)
    : List SInductiveType → Except String (List InductiveType × List (List String))
  | [] => .ok ([], [])
  | sind :: rest => do
    let (indTy, cNames) ← elabOneInductiveType ctx univParams typeNames sind
    let (restTypes, restNames) ← elabInductiveTypes ctx univParams typeNames rest
    return (indTy :: restTypes, cNames :: restNames)

def processCommand (cb : Codebase) (cmd : Command) : Except String (Codebase × ElabResult) := do
  match cmd with
  | .decl (.axiom_ name univParams ty) =>
    let ctx := cb.toElabCtx univParams
    let ty' ← elabExpr ctx ty (some cb)
    let decl := Decl.axiom univParams.length ty'
    let (h, env') ← checkDecl cb.env decl
    let cb' := { cb with env := env' }.registerName name h
    return (cb', .declared name h)

  | .decl (.def_ name univParams ty val) =>
    let ctx := cb.toElabCtx univParams
    let ty' ← elabExpr ctx ty (some cb)
    let val' ← elabExpr ctx val (some cb)
    let decl := Decl.definition univParams.length ty' val'
    let (h, env') ← checkDecl cb.env decl
    let cb' := { cb with env := env' }.registerName name h
    return (cb', .declared name h)

  | .decl (.inductive_ univParams numParams types) =>
    let ctx := cb.toElabCtx univParams
    let typeNames := types.map (·.name)
    let (elabTypes, ctorNames) ← elabInductiveTypes ctx univParams typeNames types
    let block : InductiveBlock := {
      numUnivParams := univParams.length
      numParams := numParams
      types := elabTypes
    }
    let (h, env') ← checkDecl cb.env (Decl.inductive block)
    let cb' := { cb with env := env' }
    let cb' := registerInductiveNames cb' h typeNames ctorNames
    return (cb', .declared (typeNames.headD "inductive") h)

  | .check e =>
    let ctx := cb.toElabCtx
    let e' ← elabExpr ctx e (some cb)
    let ty ← inferTypeClosed cb.env e'
    return (cb, .checked e' ty)

  | .eval e =>
    let ctx := cb.toElabCtx
    let e' ← elabExpr ctx e (some cb)
    let result := normalize cb.env e'
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

  | .import_ path => .error s!"import '{path}' must be resolved at IO level (use file processing)"

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
