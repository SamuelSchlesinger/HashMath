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
    if !(isDefEqClosed env valTy ty) then
      throw "checkDecl: definition value type mismatch"
    return env.addDecl d

  | .inductive block =>
    match checkInductiveBlock env block with
    | .ok () => return env.addDecl d
    | .error e => throw s!"checkDecl: inductive error: {e}"

  | .quotient _ =>
    return env.addDecl d

/-- Check that an expression has a given type. -/
def checkType (env : Environment) (e : Expr) (expectedTy : Expr) : Except String Unit := do
  let inferredTy ← inferTypeClosed env e
  if !(isDefEqClosed env inferredTy expectedTy) then
    throw "checkType: type mismatch"

end HashMath
