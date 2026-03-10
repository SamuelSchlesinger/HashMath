/-
  HashMath.Environment — Declaration environment indexed by hash
-/

import HashMath.Hash
import Std.Data.HashMap

namespace HashMath

/-- Resolved information about a declaration in the environment. -/
structure DeclInfo where
  decl : Decl
  hash : Hash
  deriving Repr

/-- The HashMath environment: a map from hashes to declarations. -/
structure Environment where
  decls : Std.HashMap Hash DeclInfo := {}
  ctors : Std.HashMap Hash ConstructorInfo := {}
  recs : Std.HashMap Hash RecursorInfo := {}
  indTypes : Std.HashMap Hash (InductiveBlock × Nat) := {}  -- type hash → (block, typeIdx)
  deriving Inhabited

namespace Environment

/-- The empty environment. -/
def empty : Environment := ⟨{}, {}, {}, {}⟩

/-- Look up a declaration by its hash. -/
def lookup (env : Environment) (h : Hash) : Option DeclInfo :=
  env.decls[h]?

/-- Look up constructor info by hash. -/
def getConstructorInfo (env : Environment) (h : Hash) : Option ConstructorInfo :=
  env.ctors[h]?

/-- Look up recursor info by hash. -/
def getRecursorInfo (env : Environment) (h : Hash) : Option RecursorInfo :=
  env.recs[h]?

/-- Look up the inductive block and type index for an inductive type hash. -/
def getInductiveBlockForType (env : Environment) (h : Hash) : Option (InductiveBlock × Nat) :=
  env.indTypes[h]?

/-- Resolve `iref` references in an expression: replace `iref i univs` with
    `const (hashIndType blockHash i) univs`. -/
def resolveIRef (blockHash : Hash) (e : Expr) : Expr :=
  match e with
  | .iref idx ls => .const (hashIndType blockHash idx) ls
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const h ls => .const h ls
  | .app f a => .app (resolveIRef blockHash f) (resolveIRef blockHash a)
  | .lam ty body => .lam (resolveIRef blockHash ty) (resolveIRef blockHash body)
  | .forallE ty body => .forallE (resolveIRef blockHash ty) (resolveIRef blockHash body)
  | .letE ty val body => .letE (resolveIRef blockHash ty) (resolveIRef blockHash val) (resolveIRef blockHash body)
  | .proj h i s => .proj h i (resolveIRef blockHash s)

/-- Walk a raw (pre-resolution) constructor type, skip `numParams` leading forallE binders,
    then for each remaining forallE check if its domain's head is an `iref`. Returns
    (fieldIdx, targetTypeIdx, indexArgs) triples for recursive fields.
    The indexArgs are the arguments to the type after the parameters (expressed as bvars
    relative to the fields telescope: bvar 0 = current field, bvar 1 = previous, etc.). -/
private def computeRecursiveFields (rawCtorTy : Expr) (numParams : Nat)
    : List (Nat × Nat × List Expr) :=
  go (stripN rawCtorTy numParams) 0
where
  stripN : Expr → Nat → Expr
    | .forallE _ body, n + 1 => stripN body n
    | e, _ => e
  go : Expr → Nat → List (Nat × Nat × List Expr)
    | .forallE domTy body, idx =>
      match domTy.getAppFn with
      | .iref targetIdx _ =>
        let allArgs := domTy.getAppArgs
        if allArgs.length < numParams then go body (idx + 1)
        else
          let paramArgs := allArgs.take numParams
          let expectedParams := (List.range numParams).map
            (fun i => Expr.bvar (idx + numParams - 1 - i))
          if paramArgs != expectedParams then go body (idx + 1)
          else
            let indexArgs := allArgs.drop numParams
            (idx, targetIdx, indexArgs) :: go body (idx + 1)
      | _ => go body (idx + 1)
    | _, _ => []

/-- Add a declaration to the environment. Returns the hash and updated environment. -/
def addDecl (env : Environment) (d : Decl) : Hash × Environment :=
  let h := hashDecl d
  let info : DeclInfo := { decl := d, hash := h }
  let env' := { env with decls := env.decls.insert h info }
  match d with
  | .inductive block => (h, registerInductive env' h block)
  | _ => (h, env')
where
  registerInductive (env : Environment) (blockHash : Hash) (block : InductiveBlock) : Environment :=
    let nTypes := block.types.length
    let totalMinors := block.types.foldl (fun acc indTy => acc + indTy.ctors.length) 0
    (List.range nTypes).foldl (fun (envAcc : Environment × Nat) i =>
      let (env, globalCtorOffset) := envAcc
      let typeHash := hashIndType blockHash i
      let env := { env with indTypes := env.indTypes.insert typeHash (block, i) }
      match block.types[i]? with
      | some indTy =>
        let env := (List.range indTy.ctors.length).foldl (fun env j =>
          let ctorHash := hashCtor blockHash i j
          let rawCtorTy := match indTy.ctors[j]? with | some ty => ty | none => .sort .zero
          let ctorTy := resolveIRef blockHash rawCtorTy
          let nFields := countForallE ctorTy - block.numParams
          let recFields := computeRecursiveFields rawCtorTy block.numParams
          let ctorInfo : ConstructorInfo := {
            indHash := typeHash
            blkIdx := i
            cIdx := globalCtorOffset + j  -- global constructor index
            nParams := block.numParams
            nFields := nFields
            recursiveFields := recFields
            ty := ctorTy
          }
          { env with ctors := env.ctors.insert ctorHash ctorInfo }
        ) env
        let recHash := hashRec blockHash i
        let nIndices := countForallE indTy.type - block.numParams
        let recInfo : RecursorInfo := {
          indHash := typeHash
          blockHash := blockHash
          blkIdx := i
          nParams := block.numParams
          nMotives := nTypes
          nMinors := totalMinors
          nIndices := nIndices
          recTy := .sort .zero  -- placeholder (updated in checkDecl)
        }
        ({ env with recs := env.recs.insert recHash recInfo }, globalCtorOffset + indTy.ctors.length)
      | none => (env, globalCtorOffset)
    ) (env, 0) |>.1
  countForallE : Expr → Nat
    | .forallE _ body => 1 + countForallE body
    | _ => 0

/-- Check if a hash exists in the environment (decls, ctors, recs, or indTypes). -/
def contains (env : Environment) (h : Hash) : Bool :=
  env.decls.contains h || env.ctors.contains h ||
  env.recs.contains h || env.indTypes.contains h

/-- Get the type of a declaration (for axioms and definitions). -/
def getDeclType (env : Environment) (h : Hash) (univs : List Level) : Option Expr :=
  match env.lookup h with
  | some info =>
    match info.decl with
    | .axiom _ ty => some (ty.substLevelParams univs)
    | .definition _ ty _ => some (ty.substLevelParams univs)
    | _ => none
  | none => none

/-- Get the value/definition body of a definition. -/
def getDeclValue (env : Environment) (h : Hash) (univs : List Level) : Option Expr :=
  match env.lookup h with
  | some info =>
    match info.decl with
    | .definition _ _ val => some (val.substLevelParams univs)
    | _ => none
  | none => none

/-- Get an inductive block from the environment (by block declaration hash). -/
def getInductiveBlock (env : Environment) (h : Hash) : Option InductiveBlock :=
  match env.lookup h with
  | some info =>
    match info.decl with
    | .inductive block => some block
    | _ => none
  | none => none

/-- Get the expected number of universe parameters for a constant hash,
    checking all entity types (declarations, inductive types, constructors, recursors). -/
def getExpectedUnivParams (env : Environment) (h : Hash) : Option Nat :=
  -- Regular declarations (axioms, definitions, inductive blocks, quotients)
  match env.lookup h with
  | some info => some info.decl.numUnivParams
  | none =>
    -- Inductive types (by derived type hash)
    match env.getInductiveBlockForType h with
    | some (block, _) => some block.numUnivParams
    | none =>
      -- Constructors
      match env.getConstructorInfo h with
      | some ctorInfo =>
        match env.getInductiveBlockForType ctorInfo.indHash with
        | some (block, _) => some block.numUnivParams
        | none => none
      | none =>
        -- Recursors (block params + 1 if large elimination allowed)
        match env.getRecursorInfo h with
        | some recInfo =>
          match env.getInductiveBlockForType recInfo.indHash with
          | some (block, _) =>
            some (block.numUnivParams + if recInfo.allowsLargeElim then 1 else 0)
          | none => none
        | none => none

end Environment

end HashMath
