/-
  HashMath.TypeChecker — Declaration checking for HashMath CIC
-/

import HashMath.DefEq

namespace HashMath

/-- Check that a declaration is well-typed and add it to the environment. -/
def checkDecl (env : Environment) (d : Decl) : Except String (Hash × Environment) := do
  match d with
  | .axiom _numUnivs ty =>
    let _ ← inferTypeClosed env ty
    return env.addDecl d

  | .definition _numUnivs ty val =>
    let _ ← inferTypeClosed env ty
    let valTy ← inferTypeClosed env val
    if !(isSubtype env [] valTy ty) then
      throw "checkDecl: definition value type mismatch"
    return env.addDecl d

  | .inductive block =>
    match checkInductiveBlock env block with
    | .ok () =>
      let (h, env') := env.addDecl d
      -- Update recursor info with proper generated types
      let env'' := (List.range block.types.length).foldl (fun env i =>
        let recHash := hashRec h i
        let recInfo := generateRecursorInfo block i h
        { env with recs := env.recs.insert recHash recInfo }
      ) env'
      return (h, env'')
    | .error e => throw s!"checkDecl: inductive error: {e}"

  | .quotient _ =>
    return env.addDecl d

/-- Check that an expression has a given type. -/
def checkType (env : Environment) (e : Expr) (expectedTy : Expr) : Except String Unit := do
  let inferredTy ← inferTypeClosed env e
  if !(isSubtype env [] inferredTy expectedTy) then
    throw "checkType: type mismatch"

end HashMath
