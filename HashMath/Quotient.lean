/-
  HashMath.Quotient — The 4 quotient constants and their reduction rules
-/

import HashMath.Reduce

namespace HashMath

/-- Get the type of a quotient constant. -/
def quotientType (kind : QuotKind) : Expr :=
  match kind with
  | .quot =>
    -- Quot : {α : Sort u} → (α → α → Prop) → Sort u
    let sortU := Expr.sort (.param 0)
    let α := Expr.bvar 1
    let relTy := Expr.forallE α (Expr.forallE (α.liftN 1) (Expr.sort .zero))
    Expr.forallE sortU (Expr.forallE relTy sortU)
  | .quotMk =>
    -- Simplified placeholder
    Expr.sort .zero
  | .quotLift =>
    Expr.sort .zero
  | .quotInd =>
    Expr.sort .zero

/-- Quotient reduction: `Quot.lift f h (Quot.mk r a) → f a` -/
def quotLiftReduce (args : List Expr) (env : Environment) : Option Expr :=
  -- Quot.lift {α} {r} {β} f h q
  if args.length < 6 then none
  else
    let f := args[3]!
    let q := args[5]!
    let q' := whnfCore env q
    let (qfn, qargs) := q'.getAppFnArgs
    match qfn with
    | Expr.const _h _ =>
      if qargs.length >= 3 then
        some (.app f (qargs[2]!))
      else
        none
    | _ => none

/-- Quotient reduction: `Quot.ind h (Quot.mk r a) → h a` -/
def quotIndReduce (args : List Expr) (env : Environment) : Option Expr :=
  if args.length < 5 then none
  else
    let h := args[3]!
    let q := args[4]!
    let q' := whnfCore env q
    let (qfn, qargs) := q'.getAppFnArgs
    match qfn with
    | Expr.const _h _ =>
      if qargs.length >= 3 then
        some (.app h (qargs[2]!))
      else
        none
    | _ => none

end HashMath
