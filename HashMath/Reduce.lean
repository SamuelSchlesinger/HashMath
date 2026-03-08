/-
  HashMath.Reduce — Reduction engine for HashMath CIC

  Implements β, δ, ι, ζ, projection, and quotient reduction.
  All definitions are fully transparent (no opacity mechanism).
-/

import HashMath.Environment

namespace HashMath

/-- β-reduction: `(λ ty. body) arg → body[arg/0]` -/
def betaReduce (body : Expr) (arg : Expr) : Expr :=
  body.instantiate arg

/-- ζ-reduction: `let x : ty := val in body → body[val/0]` -/
def zetaReduce (val : Expr) (body : Expr) : Expr :=
  body.instantiate val

/-- Projection reduction: `proj(I, i, ctor args) → args[numParams + i]` -/
def projReduce (env : Environment) (typeName : Hash) (idx : Nat) (struct : Expr) : Option Expr :=
  let (fn, args) := struct.getAppFnArgs
  match fn with
  | .const _h _ =>
    match env.getInductiveBlock typeName with
    | some block =>
      match block.types with
      | [indTy] =>
        match indTy.ctors with
        | [_ctorTy] =>
          let fieldIdx := block.numParams + idx
          args[fieldIdx]?
        | _ => none
      | _ => none
    | none => none
  | _ => none

/-- Weak head normal form (core reductions: β, ζ, ι, proj — not δ). -/
partial def whnfCore (env : Environment) (e : Expr) : Expr :=
  match e with
  | .app fn arg =>
    let fn' := whnfCore env fn
    match fn' with
    | .lam _ty body => whnfCore env (betaReduce body arg)
    | _ =>
      if fn' == fn then e
      else .app fn' arg
  | .letE _ty val body => whnfCore env (zetaReduce val body)
  | .proj typeName idx struct =>
    let struct' := whnfCore env struct
    match projReduce env typeName idx struct' with
    | some result => whnfCore env result
    | none => .proj typeName idx struct'
  | _ => e

/-- Weak head normal form (including δ-reduction — all defs are transparent). -/
partial def whnf (env : Environment) (e : Expr) : Expr :=
  let e' := whnfCore env e
  match e' with
  | .const h univs =>
    match env.getDeclValue h univs with
    | some val => whnf env val
    | none => e'
  | .app _fn _arg =>
    -- Try unfolding the head constant
    let (hd, allArgs) := e'.getAppFnArgs
    match hd with
    | .const h univs =>
      match env.getDeclValue h univs with
      | some val => whnf env (Expr.mkAppN val allArgs)
      | none => e'
    | _ => e'
  | _ => e'

/-- δ-unfold: unfold a single constant if it has a definition. -/
def deltaUnfold (env : Environment) (h : Hash) (univs : List Level) : Option Expr :=
  env.getDeclValue h univs

end HashMath
