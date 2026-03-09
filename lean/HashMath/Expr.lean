/-
  HashMath.Expr — Expression terms for HashMath CIC
-/

import HashMath.Level

namespace HashMath

/-- BEq instance for Empty (vacuously — no inhabitants). -/
instance : BEq Empty where
  beq a _ := nomatch a

/-- Repr instance for Empty (vacuously — no inhabitants). -/
instance : Repr Empty where
  reprPrec a _ := nomatch a

/-- Expressions with 10 constructors using de Bruijn indices.
    Binder names and binder info are excluded (alpha-invariant).
    `iref` is a block-relative inductive self-reference used inside
    constructor types before the block hash is known. It is resolved
    to `const` when the inductive block is added to the environment.
    `href` is a hash-reference to a content-addressed subterm. The type
    parameter `α` controls whether href is available:
    - `α = Empty` (default): href is unconstructable (kernel expressions)
    - `α = Hash`: href carries the hash of the referenced subterm -/
inductive Expr (α : Type := Empty) where
  | bvar   : Nat → Expr α
  | sort   : Level → Expr α
  | const  : Hash → List Level → Expr α
  | app    : Expr α → Expr α → Expr α
  | lam    : (ty : Expr α) → (body : Expr α) → Expr α
  | forallE : (ty : Expr α) → (body : Expr α) → Expr α
  | letE   : (ty : Expr α) → (value : Expr α) → (body : Expr α) → Expr α
  | proj   : (typeName : Hash) → (idx : Nat) → (struct : Expr α) → Expr α
  | iref   : (typeIdx : Nat) → (univs : List Level) → Expr α
  | href   : α → Expr α
  deriving Repr, BEq, Inhabited

namespace Expr

/-- Lift free de Bruijn variables by `n` starting from depth `cutoff`. -/
def liftN (e : Expr α) (n : Nat) (cutoff : Nat := 0) : Expr α :=
  match e with
  | .bvar i => if i >= cutoff then .bvar (i + n) else .bvar i
  | .sort l => .sort l
  | .const h ls => .const h ls
  | .app f a => .app (f.liftN n cutoff) (a.liftN n cutoff)
  | .lam ty body => .lam (ty.liftN n cutoff) (body.liftN n (cutoff + 1))
  | .forallE ty body => .forallE (ty.liftN n cutoff) (body.liftN n (cutoff + 1))
  | .letE ty val body => .letE (ty.liftN n cutoff) (val.liftN n cutoff) (body.liftN n (cutoff + 1))
  | .proj h i s => .proj h i (s.liftN n cutoff)
  | .iref idx ls => .iref idx ls
  | .href a => .href a

/-- Substitute expression `s` for de Bruijn variable `var` in `e`.
    After substitution, free variables above `var` are decremented. -/
def substN (e : Expr α) (var : Nat) (s : Expr α) : Expr α :=
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
  | .iref idx ls => .iref idx ls
  | .href a => .href a

/-- Instantiate the outermost bound variable (bvar 0) with `s`. -/
def instantiate (e : Expr α) (s : Expr α) : Expr α :=
  e.substN 0 s

/-- Instantiate bvar 0 with multiple values (for multi-arg application).
    `instantiateRev [a₀, a₁, ..., aₙ]` substitutes bvar 0 with aₙ first,
    then bvar 0 with aₙ₋₁, etc. -/
def instantiateRev (e : Expr α) (args : Array (Expr α)) : Expr α :=
  args.foldr (fun arg acc => acc.instantiate arg) e

/-- Abstract variable at de Bruijn level `lvl` — replace free occurrences
    of `bvar lvl` with `bvar 0`, shifting accordingly. This is the inverse
    of instantiate in some sense. Typically used when going under a binder:
    if the context has depth `d`, the bound variable inside the binder is `bvar d`. -/
def abstract [BEq α] (e : Expr α) (fvar : Expr α) : Expr α :=
  go e fvar 0
where
  go (e : Expr α) (target : Expr α) (depth : Nat) : Expr α :=
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
    | .iref idx ls => .iref idx ls
    | .href a => .href a

/-- Substitute universe level parameters in an expression. -/
def substLevelParams (e : Expr α) (ls : List Level) : Expr α :=
  match e with
  | .bvar i => .bvar i
  | .sort l => .sort (l.substParams ls)
  | .const h lvls => .const h (lvls.map (Level.substParams ls))
  | .app f a => .app (f.substLevelParams ls) (a.substLevelParams ls)
  | .lam ty body => .lam (ty.substLevelParams ls) (body.substLevelParams ls)
  | .forallE ty body => .forallE (ty.substLevelParams ls) (body.substLevelParams ls)
  | .letE ty val body => .letE (ty.substLevelParams ls) (val.substLevelParams ls) (body.substLevelParams ls)
  | .proj h i s => .proj h i (s.substLevelParams ls)
  | .iref idx lvls => .iref idx (lvls.map (Level.substParams ls))
  | .href a => .href a

/-- Check if the expression has any loose bound variables ≥ depth. -/
def hasLooseBVarGe (e : Expr α) (depth : Nat) : Bool :=
  match e with
  | .bvar i => i >= depth
  | .sort _ => false
  | .const _ _ => false
  | .app f a => f.hasLooseBVarGe depth || a.hasLooseBVarGe depth
  | .lam ty body => ty.hasLooseBVarGe depth || body.hasLooseBVarGe (depth + 1)
  | .forallE ty body => ty.hasLooseBVarGe depth || body.hasLooseBVarGe (depth + 1)
  | .letE ty val body => ty.hasLooseBVarGe depth || val.hasLooseBVarGe depth || body.hasLooseBVarGe (depth + 1)
  | .proj _ _ s => s.hasLooseBVarGe depth
  | .iref _ _ => false
  | .href _ => false

/-- Check if the expression is closed (no loose bound variables). -/
def isClosed (e : Expr α) : Bool :=
  !e.hasLooseBVarGe 0

/-- Get the head of an application spine. `(f a b c).getAppFn = f`. -/
def getAppFn : Expr α → Expr α
  | .app f _ => f.getAppFn
  | e => e

/-- Get the arguments of an application spine. `(f a b c).getAppArgs = [a, b, c]`. -/
def getAppArgs (e : Expr α) : List (Expr α) :=
  go e []
where
  go : Expr α → List (Expr α) → List (Expr α)
    | .app f a, acc => go f (a :: acc)
    | _, acc => acc

/-- Decompose an application into head and args. -/
def getAppFnArgs (e : Expr α) : Expr α × List (Expr α) :=
  (e.getAppFn, e.getAppArgs)

/-- Build an application from a function and argument list. -/
def mkAppN (fn : Expr α) (args : List (Expr α)) : Expr α :=
  args.foldl .app fn

/-- Embed a kernel expression (Expr Empty) into any Expr α.
    This is safe because Expr Empty cannot contain href nodes. -/
def embed (e : Expr Empty) : Expr α :=
  match e with
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const h ls => .const h ls
  | .app f a => .app (embed f) (embed a)
  | .lam ty body => .lam (embed ty) (embed body)
  | .forallE ty body => .forallE (embed ty) (embed body)
  | .letE ty val body => .letE (embed ty) (embed val) (embed body)
  | .proj h i s => .proj h i (embed s)
  | .iref idx ls => .iref idx ls
  | .href a => nomatch a

end Expr

end HashMath
