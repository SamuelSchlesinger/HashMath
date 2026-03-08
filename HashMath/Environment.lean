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
  deriving Inhabited

namespace Environment

/-- The empty environment. -/
def empty : Environment := ⟨{}⟩

/-- Look up a declaration by its hash. -/
def lookup (env : Environment) (h : Hash) : Option DeclInfo :=
  env.decls[h]?

/-- Add a declaration to the environment. Returns the hash and updated environment. -/
def addDecl (env : Environment) (d : Decl) : Hash × Environment :=
  let h := hashDecl d
  let info : DeclInfo := { decl := d, hash := h }
  (h, { decls := env.decls.insert h info })

/-- Check if a hash exists in the environment. -/
def contains (env : Environment) (h : Hash) : Bool :=
  env.decls.contains h

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

/-- Get an inductive block from the environment. -/
def getInductiveBlock (env : Environment) (h : Hash) : Option InductiveBlock :=
  match env.lookup h with
  | some info =>
    match info.decl with
    | .inductive block => some block
    | _ => none
  | none => none

end Environment

end HashMath
