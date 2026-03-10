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
  | .const ctorH _ =>
    match env.getInductiveBlockForType typeName with
    | some (block, _) =>
      match env.getConstructorInfo ctorH with
      | some ctorInfo =>
        if ctorInfo.indHash != typeName then none
        else
          match block.types with
          | [_] =>
            let fieldIdx := block.numParams + idx
            args[fieldIdx]?
          | _ => none
      | none => none
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
      let processCtorApp := fun (ctorH : Hash) (majorArgs : List Expr) =>
        match env.getConstructorInfo ctorH with
        | some ctorInfo =>
          if ctorInfo.indHash != recInfo.indHash then none
          else
            let minorIdx := nParams + nMotives + ctorInfo.cIdx
            if minorIdx >= args.length then none
            else
              let minor := args[minorIdx]!
              let fields := majorArgs.drop ctorInfo.nParams
              let recPrefix := args.take nParams ++
                (args.drop nParams).take nMotives ++
                (args.drop (nParams + nMotives)).take nMinors
              let minorArgs := buildMinorArgs fields 0 ctorInfo.recursiveFields
                  recInfo.blockHash univs recPrefix majorArgs ctorInfo.nParams []
              let result := Expr.mkAppN minor minorArgs
              let extraArgs := args.drop expectedArgs
              some (Expr.mkAppN result extraArgs)
        | none => none
      -- Try direct constructor match first
      let ctorResult := match majorFn with
        | .const ctorH _ => processCtorApp ctorH majorArgs
        | _ => none
      match ctorResult with
      | some r => some r
      | none =>
        -- Try K-like synthesis or struct eta expansion
        match env.getInductiveBlockForType recInfo.indHash with
        | some (block, blkIdx) =>
          match block.types with
          | [indTy] =>
            match indTy.ctors with
            | [ctorTy] =>
              let nFields := countForallE ctorTy - block.numParams
              if nFields == 0 then
                -- K-like: single type, single ctor, zero fields
                -- Check if definitively Prop (Sort 0)
                match getTargetSort indTy.type with
                | some l =>
                  match l.normalize.toNat with
                  | some 0 =>
                    -- Synthesize the unique constructor: ctor params
                    let ctorHash := hashCtor recInfo.blockHash blkIdx 0
                    let params := args.take nParams
                    processCtorApp ctorHash params
                  | _ => none
                | none => none
              else
                -- Structure eta: expand major into ctor(params, proj 0 major, ...)
                let ctorHash := hashCtor recInfo.blockHash blkIdx 0
                let params := args.take nParams
                let projections := (List.range nFields).map (fun i =>
                  Expr.proj recInfo.indHash i major)
                let synthArgs := params ++ projections
                processCtorApp ctorHash synthArgs
            | _ => none  -- 0 or 2+ constructors
          | _ => none  -- mutual block
        | none => none
where
  /-- Walk forallE telescope to find the trailing Sort level. -/
  getTargetSort : Expr → Option Level
    | .sort l => some l
    | .forallE _ body => getTargetSort body
    | _ => none
  /-- Count leading forallE binders. -/
  countForallE : Expr → Nat
    | .forallE _ body => 1 + countForallE body
    | _ => 0
  /-- Substitute bvars in an index argument with actual constructor arguments.
      bvar(k) → allCtorArgs[nParams + fieldIdx - 1 - (k - localDepth)]
      Local binders (lambda, forallE, letE) increment localDepth;
      bvars below localDepth are left untouched (they refer to local binders). -/
  substIndexArg (e : Expr) (allCtorArgs : List Expr) (nParams fieldIdx : Nat)
      (localDepth : Nat := 0) : Expr :=
    match e with
    | .bvar k =>
      if k < localDepth then .bvar k
      else
        let adjustedK := k - localDepth
        let targetIdx := nParams + fieldIdx - 1 - adjustedK
        allCtorArgs.getD targetIdx (.sort .zero)
    | .app f a =>
      .app (substIndexArg f allCtorArgs nParams fieldIdx localDepth)
           (substIndexArg a allCtorArgs nParams fieldIdx localDepth)
    | .lam ty body =>
      .lam (substIndexArg ty allCtorArgs nParams fieldIdx localDepth)
           (substIndexArg body allCtorArgs nParams fieldIdx (localDepth + 1))
    | .forallE ty body =>
      .forallE (substIndexArg ty allCtorArgs nParams fieldIdx localDepth)
               (substIndexArg body allCtorArgs nParams fieldIdx (localDepth + 1))
    | .letE ty val body =>
      .letE (substIndexArg ty allCtorArgs nParams fieldIdx localDepth)
            (substIndexArg val allCtorArgs nParams fieldIdx localDepth)
            (substIndexArg body allCtorArgs nParams fieldIdx (localDepth + 1))
    | .proj h i s => .proj h i (substIndexArg s allCtorArgs nParams fieldIdx localDepth)
    | other => other  -- sort, const, iref unchanged
  buildMinorArgs (fields : List Expr) (idx : Nat)
      (recFields : List (Nat × Nat × List Expr))
      (blockHash : Hash) (univs : List Level) (recPrefix : List Expr)
      (allCtorArgs : List Expr) (nParams : Nat) (recNIndices : List Nat) : List Expr :=
    match fields with
    | [] => []
    | f :: rest =>
      match recFields.find? (fun (fIdx, _, _) => fIdx == idx) with
      | some (_, targetTypeIdx, storedIdxArgs) =>
        let targetRecHash := hashRec blockHash targetTypeIdx
        -- Substitute bvars in stored index args with actual constructor args
        let concreteIdxArgs := storedIdxArgs.map (fun e => substIndexArg e allCtorArgs nParams idx)
        -- The target recursor expects: params motives minors indices major
        -- recPrefix already has params ++ motives ++ minors
        let ih := Expr.mkAppN (.const targetRecHash univs) (recPrefix ++ concreteIdxArgs ++ [f])
        f :: ih :: buildMinorArgs rest (idx + 1) recFields blockHash univs recPrefix allCtorArgs nParams recNIndices
      | none =>
        f :: buildMinorArgs rest (idx + 1) recFields blockHash univs recPrefix allCtorArgs nParams recNIndices

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

/-- Full normalization: reduce everywhere (inside constructors, under binders, etc.).
    First reduces to WHNF, then recursively normalizes sub-expressions. -/
partial def normalize (env : Environment) (e : Expr) : Expr :=
  let e' := whnf env e
  match e' with
  | .app _ _ =>
    let (fn, args) := e'.getAppFnArgs
    let fn' := normalize env fn
    let args' := args.map (normalize env)
    Expr.mkAppN fn' args'
  | .lam ty body =>
    .lam (normalize env ty) (normalize env body)
  | .forallE ty body =>
    .forallE (normalize env ty) (normalize env body)
  | .letE ty val body =>
    -- Let bindings should already be reduced by whnf, but handle just in case
    .letE (normalize env ty) (normalize env val) (normalize env body)
  | .proj h i s =>
    .proj h i (normalize env s)
  | _ => e'  -- sort, const (no def), bvar, iref — already in normal form

end HashMath
