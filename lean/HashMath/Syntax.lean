/-
  HashMath.Syntax — Surface syntax AST for the HashMath frontend
-/

import HashMath.Basic

namespace HashMath

/-- Surface-level universe levels with named parameters. -/
inductive SLevel where
  | num : Nat → SLevel
  | param : String → SLevel
  | succ : SLevel → SLevel
  | max : SLevel → SLevel → SLevel
  | imax : SLevel → SLevel → SLevel
  deriving Repr, BEq, Inhabited

/-- Surface-level expressions with named variables and constants. -/
inductive SExpr where
  | var : String → List SLevel → SExpr
  | sort : SLevel → SExpr
  | app : SExpr → SExpr → SExpr
  | lam : String → SExpr → SExpr → SExpr       -- fun (name : type) => body
  | pi : String → SExpr → SExpr → SExpr         -- ∀ (name : type), body
  | arrow : SExpr → SExpr → SExpr               -- type → type (non-dependent)
  | letE : String → SExpr → SExpr → SExpr → SExpr  -- let name : ty := val in body
  | proj : String → Nat → SExpr → SExpr
  | match_ (recUnivs : List SLevel) (scrutinee : SExpr) (asVars : List String)
           (typeExpr : SExpr) (returnExpr : SExpr)
           (armCtors : List String) (armVarss : List (List String)) (armBodies : List SExpr) : SExpr
  deriving Repr, BEq, Inhabited

namespace SExpr

/-- Build a multi-argument application. -/
def mkApp (fn : SExpr) (args : List SExpr) : SExpr :=
  args.foldl .app fn

/-- Build a multi-binder lambda. -/
def mkLam (binders : List (String × SExpr)) (body : SExpr) : SExpr :=
  binders.foldr (fun (n, ty) acc => .lam n ty acc) body

/-- Build a multi-binder pi. -/
def mkPi (binders : List (String × SExpr)) (body : SExpr) : SExpr :=
  binders.foldr (fun (n, ty) acc => .pi n ty acc) body

end SExpr

/-- A constructor in a surface inductive declaration. -/
structure SConstructor where
  name : String
  type : SExpr
  deriving Repr

/-- A single inductive type in a (possibly mutual) block. -/
structure SInductiveType where
  name : String
  type : SExpr
  ctors : List SConstructor
  deriving Repr

/-- Surface-level declarations. -/
inductive SDecl where
  | axiom_ : String → List String → SExpr → SDecl
  | def_ : String → List String → SExpr → SExpr → SDecl
  | inductive_ : List String → Nat → List SInductiveType → SDecl
  deriving Repr

/-- A top-level command. -/
inductive Command where
  | decl : SDecl → Command
  | check : SExpr → Command        -- #check expr
  | eval : SExpr → Command         -- #eval expr
  | print : String → Command       -- #print name
  | import_ : String → Command     -- import "path"
  deriving Repr

end HashMath
