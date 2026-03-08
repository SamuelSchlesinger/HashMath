/-
  HashMath.Expr — Expression terms for HashMath CIC
-/

import HashMath.Level

namespace HashMath

/-- Expressions with 8 constructors using de Bruijn indices.
    Binder names and binder info are excluded (alpha-invariant). -/
inductive Expr where
  | bvar   : Nat → Expr
  | sort   : Level → Expr
  | const  : Hash → List Level → Expr
  | app    : Expr → Expr → Expr
  | lam    : (ty : Expr) → (body : Expr) → Expr
  | forallE : (ty : Expr) → (body : Expr) → Expr
  | letE   : (ty : Expr) → (value : Expr) → (body : Expr) → Expr
  | proj   : (typeName : Hash) → (idx : Nat) → (struct : Expr) → Expr
  deriving Repr, BEq, Inhabited

namespace Expr

/-- Lift free de Bruijn variables by `n` starting from depth `cutoff`. -/
def liftN (e : Expr) (n : Nat) (cutoff : Nat := 0) : Expr :=
  match e with
  | .bvar i => if i >= cutoff then .bvar (i + n) else .bvar i
  | .sort l => .sort l
  | .const h ls => .const h ls
  | .app f a => .app (f.liftN n cutoff) (a.liftN n cutoff)
  | .lam ty body => .lam (ty.liftN n cutoff) (body.liftN n (cutoff + 1))
  | .forallE ty body => .forallE (ty.liftN n cutoff) (body.liftN n (cutoff + 1))
  | .letE ty val body => .letE (ty.liftN n cutoff) (val.liftN n cutoff) (body.liftN n (cutoff + 1))
  | .proj h i s => .proj h i (s.liftN n cutoff)

/-- Substitute expression `s` for de Bruijn variable `var` in `e`.
    After substitution, free variables above `var` are decremented. -/
def substN (e : Expr) (var : Nat) (s : Expr) : Expr :=
  match e with
  | .bvar i =>
    if i == var then s
    else if i > var then .bvar (i - 1)
    else .bvar i
  | .sort l => .sort l
  | .const h ls => .const h ls
  | .app f a => .app (f.substN var s) (a.substN var s)
  | .lam ty body => .lam (ty.substN var s) (body.substN (var + 1) (s.liftN 1))
  | .forallE ty body => .forallE (ty.substN var s) (body.substN (var + 1) (s.liftN 1))
  | .letE ty val body => .letE (ty.substN var s) (val.substN var s) (body.substN (var + 1) (s.liftN 1))
  | .proj h i struct => .proj h i (struct.substN var s)

/-- Instantiate the outermost bound variable (bvar 0) with `s`. -/
def instantiate (e : Expr) (s : Expr) : Expr :=
  e.substN 0 s

/-- Instantiate bvar 0 with multiple values (for multi-arg application).
    `instantiateRev [a₀, a₁, ..., aₙ]` substitutes bvar 0 with aₙ first,
    then bvar 0 with aₙ₋₁, etc. -/
def instantiateRev (e : Expr) (args : Array Expr) : Expr :=
  args.foldr (fun arg acc => acc.instantiate arg) e

/-- Abstract variable at de Bruijn level `lvl` — replace free occurrences
    of `bvar lvl` with `bvar 0`, shifting accordingly. This is the inverse
    of instantiate in some sense. Typically used when going under a binder:
    if the context has depth `d`, the bound variable inside the binder is `bvar d`. -/
def abstract (e : Expr) (fvar : Expr) : Expr :=
  go e fvar 0
where
  go (e : Expr) (target : Expr) (depth : Nat) : Expr :=
    if e == target then .bvar depth
    else match e with
    | .bvar i => if i >= depth then .bvar (i + 1) else .bvar i
    | .sort l => .sort l
    | .const h ls => .const h ls
    | .app f a => .app (go f target depth) (go a target depth)
    | .lam ty body => .lam (go ty target depth) (go body target (depth + 1))
    | .forallE ty body => .forallE (go ty target depth) (go body target (depth + 1))
    | .letE ty val body => .letE (go ty target depth) (go val target depth) (go body target (depth + 1))
    | .proj h i s => .proj h i (go s target depth)

/-- Substitute universe level parameters in an expression. -/
def substLevelParams (e : Expr) (ls : List Level) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .sort l => .sort (l.substParams ls)
  | .const h lvls => .const h (lvls.map (Level.substParams ls))
  | .app f a => .app (f.substLevelParams ls) (a.substLevelParams ls)
  | .lam ty body => .lam (ty.substLevelParams ls) (body.substLevelParams ls)
  | .forallE ty body => .forallE (ty.substLevelParams ls) (body.substLevelParams ls)
  | .letE ty val body => .letE (ty.substLevelParams ls) (val.substLevelParams ls) (body.substLevelParams ls)
  | .proj h i s => .proj h i (s.substLevelParams ls)

/-- Check if the expression has any loose bound variables ≥ depth. -/
def hasLooseBVarGe (e : Expr) (depth : Nat) : Bool :=
  match e with
  | .bvar i => i >= depth
  | .sort _ => false
  | .const _ _ => false
  | .app f a => f.hasLooseBVarGe depth || a.hasLooseBVarGe depth
  | .lam ty body => ty.hasLooseBVarGe depth || body.hasLooseBVarGe (depth + 1)
  | .forallE ty body => ty.hasLooseBVarGe depth || body.hasLooseBVarGe (depth + 1)
  | .letE ty val body => ty.hasLooseBVarGe depth || val.hasLooseBVarGe depth || body.hasLooseBVarGe (depth + 1)
  | .proj _ _ s => s.hasLooseBVarGe depth

/-- Check if the expression is closed (no loose bound variables). -/
def isClosed (e : Expr) : Bool :=
  !e.hasLooseBVarGe 0

/-- Get the head of an application spine. `(f a b c).getAppFn = f`. -/
def getAppFn : Expr → Expr
  | .app f _ => f.getAppFn
  | e => e

/-- Get the arguments of an application spine. `(f a b c).getAppArgs = [a, b, c]`. -/
def getAppArgs : Expr → List Expr
  | .app f a => f.getAppArgs ++ [a]
  | _ => []

/-- Decompose an application into head and args. -/
def getAppFnArgs (e : Expr) : Expr × List Expr :=
  (e.getAppFn, e.getAppArgs)

/-- Build an application from a function and argument list. -/
def mkAppN (fn : Expr) (args : List Expr) : Expr :=
  args.foldl .app fn

end Expr

end HashMath
