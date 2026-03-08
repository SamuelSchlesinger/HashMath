/-
  HashMath.Reduce — Reduction engine for HashMath CIC

  Implements β, δ, ι, ζ, projection, and quotient reduction.
  All definitions are fully transparent (no opacity mechanism).
-/

import HashMath.Environment
import HashMath.Quotient

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

/-- ι-reduction: apply a recursor to a constructor.
    Given `rec params motives minors indices (ctor params fields)`,
    select the appropriate minor premise and apply to the fields. -/
def iotaReduce (env : Environment) (recHash : Hash) (univs : List Level)
    (args : List Expr) (whnfFn : Environment → Expr → Expr) : Option Expr :=
  match env.getRecursorInfo recHash with
  | none => none
  | some recInfo =>
    let nParams := recInfo.nParams
    let nMotives := recInfo.nMotives
    let nMinors := recInfo.nMinors
    let nIndices := recInfo.nIndices
    let expectedArgs := nParams + nMotives + nMinors + nIndices + 1
    if args.length < expectedArgs then none
    else
      -- The major premise is the last required argument
      let majorIdx := nParams + nMotives + nMinors + nIndices
      let major := args[majorIdx]!
      let major' := whnfFn env major
      let (majorFn, majorArgs) := major'.getAppFnArgs
      match majorFn with
      | .const ctorH _ =>
        match env.getConstructorInfo ctorH with
        | some ctorInfo =>
          if ctorInfo.indHash != recInfo.indHash then none
          else
            let minorIdx := nParams + nMotives + ctorInfo.cIdx
            if minorIdx >= args.length then none
            else
              let minor := args[minorIdx]!
              -- The fields are the constructor args after params
              let fields := majorArgs.drop ctorInfo.nParams
              -- Build minor args: interleave fields with IH for recursive fields
              let recPrefix := args.take nParams ++
                (args.drop nParams).take nMotives ++
                (args.drop (nParams + nMotives)).take nMinors
              let minorArgs := buildMinorArgs fields 0 ctorInfo.recursiveFields
                  recInfo.blockHash univs recPrefix
              let result := Expr.mkAppN minor minorArgs
              -- Also apply any remaining args beyond the recursor's expected args
              let extraArgs := args.drop expectedArgs
              some (Expr.mkAppN result extraArgs)
        | none => none
      | _ => none
where
  buildMinorArgs (fields : List Expr) (idx : Nat) (recFields : List (Nat × Nat))
      (blockHash : Hash) (univs : List Level) (recPrefix : List Expr) : List Expr :=
    match fields with
    | [] => []
    | f :: rest =>
      match recFields.find? (fun (fIdx, _) => fIdx == idx) with
      | some (_, targetTypeIdx) =>
        let targetRecHash := hashRec blockHash targetTypeIdx
        let ih := Expr.mkAppN (.const targetRecHash univs) (recPrefix ++ [f])
        f :: ih :: buildMinorArgs rest (idx + 1) recFields blockHash univs recPrefix
      | none =>
        f :: buildMinorArgs rest (idx + 1) recFields blockHash univs recPrefix

/-- Quotient reduction: `Quot.lift f h (Quot.mk r a) → f a` -/
def quotLiftReduce (args : List Expr) (env : Environment)
    (whnfCoreFn : Environment → Expr → Expr) : Option Expr :=
  if args.length < 6 then none
  else
    let f := args[3]!
    let q := args[5]!
    let q' := whnfCoreFn env q
    let (qfn, qargs) := q'.getAppFnArgs
    match qfn with
    | Expr.const h _ =>
      if h == quotientHash .quotMk then
        if qargs.length >= 3 then
          some (.app f (qargs[2]!))
        else none
      else none
    | _ => none

/-- Quotient reduction: `Quot.ind h (Quot.mk r a) → h a` -/
def quotIndReduce (args : List Expr) (env : Environment)
    (whnfCoreFn : Environment → Expr → Expr) : Option Expr :=
  if args.length < 5 then none
  else
    let h := args[3]!
    let q := args[4]!
    let q' := whnfCoreFn env q
    let (qfn, qargs) := q'.getAppFnArgs
    match qfn with
    | Expr.const qh _ =>
      if qh == quotientHash .quotMk then
        if qargs.length >= 3 then
          some (.app h (qargs[2]!))
        else none
      else none
    | _ => none

/-- Try ι-reduction and quotient reduction on an application spine. -/
private def trySpecialReduce (env : Environment) (e : Expr)
    (whnfCoreFn : Environment → Expr → Expr) : Option Expr :=
  let (hd, allArgs) := e.getAppFnArgs
  match hd with
  | .const h univs =>
    -- Try ι-reduction first (recursor application)
    match env.getRecursorInfo h with
    | some _ =>
      match iotaReduce env h univs allArgs whnfCoreFn with
      | some result => some result
      | none =>
        -- Fallback to quotient reduction
        tryQuotientReduce h allArgs env whnfCoreFn
    | none =>
      -- Try quotient reductions
      tryQuotientReduce h allArgs env whnfCoreFn
  | _ => none
where
  tryQuotientReduce (h : Hash) (allArgs : List Expr) (env : Environment)
      (whnfCoreFn : Environment → Expr → Expr) : Option Expr :=
    if h == quotientHash .quotLift then
      quotLiftReduce allArgs env whnfCoreFn
    else if h == quotientHash .quotInd then
      quotIndReduce allArgs env whnfCoreFn
    else none

mutual

/-- Weak head normal form (core reductions: β, ζ, ι, proj, quotient — not δ). -/
partial def whnfCore (env : Environment) (e : Expr) : Expr :=
  match e with
  | .app fn arg =>
    let fn' := whnfCore env fn
    match fn' with
    | .lam _ty body => whnfCore env (betaReduce body arg)
    | _ =>
      let e' := if fn' == fn then e else .app fn' arg
      -- Try quotient and ι-reduction (use whnf to δ-reduce scrutinees)
      match trySpecialReduce env e' whnf with
      | some result => whnfCore env result
      | none => e'
  | .letE _ty val body => whnfCore env (zetaReduce val body)
  | .proj typeName idx struct =>
    let struct' := whnf env struct
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

end

/-- δ-unfold: unfold a single constant if it has a definition. -/
def deltaUnfold (env : Environment) (h : Hash) (univs : List Level) : Option Expr :=
  env.getDeclValue h univs

end HashMath
