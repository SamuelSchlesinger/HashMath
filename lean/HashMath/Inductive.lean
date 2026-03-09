/-
  HashMath.Inductive — Inductive type utilities
-/

import HashMath.Environment

namespace HashMath

/-- Check if an inductive block defines a structure-like type
    (single type with single constructor). -/
def InductiveBlock.isStructureLike (block : InductiveBlock) : Bool :=
  match block.types with
  | [indTy] =>
    match indTy.ctors with
    | [_] => true
    | _ => false
  | _ => false

/-- Get the number of fields in a structure-like inductive. -/
def InductiveBlock.numFields (block : InductiveBlock) : Option Nat :=
  if block.isStructureLike then
    match block.types with
    | [indTy] =>
      match indTy.ctors with
      | [ctorTy] => some (countPiParams ctorTy - block.numParams)
      | _ => none
    | _ => none
  else
    none
where
  countPiParams : Expr → Nat
    | .forallE _ body => 1 + countPiParams body
    | _ => 0

/-- Get constructor types for a given inductive in the block. -/
def InductiveBlock.getCtorTypes (block : InductiveBlock) (typeIdx : Nat) : List Expr :=
  match block.types[typeIdx]? with
  | some indTy => indTy.ctors
  | none => []

/-- Count the number of leading forallE binders in an expression. -/
def countForallE : Expr → Nat
  | .forallE _ body => 1 + countForallE body
  | _ => 0

/-- Build `I` applied to parameter bvars at a given depth below the param binders.
    At `extraDepth` binders below the nP param binders:
    `p_i` is at `bvar (extraDepth + nP - 1 - i)`. -/
private def mkIApplied (typeHash : Hash) (univs : List Level) (nP : Nat) (extraDepth : Nat) : Expr :=
  Expr.mkAppN (.const typeHash univs)
    ((List.range nP).map (fun i => .bvar (extraDepth + nP - 1 - i)))

/-- Extract the first `n` domain types from a Π-telescope. -/
private def extractDomains (ty : Expr) : Nat → List Expr
  | 0 => []
  | n + 1 => match ty with
    | .forallE domTy body => domTy :: extractDomains body n
    | _ => []

/-- Strip the first `n` forallE binders from an expression. -/
private def stripForallE (ty : Expr) : Nat → Expr
  | 0 => ty
  | n + 1 => match ty with
    | .forallE _ body => stripForallE body n
    | _ => ty

/-- Extract constructor index arguments from a constructor's return type.
    Given the return type (e.g., `Eq α a a`) which is `I params... indices...`,
    drop the first `nP` arguments (params) and return the remaining (index args). -/
private def getCtorIndexArgs (retType : Expr) (nP : Nat) : List Expr :=
  retType.getAppArgs.drop nP

/-- Check if a domain type matches any type in the block applied to params (possibly with indices).
    Returns the index of the matching type and the index arguments, or `none`. -/
private def findRecTarget (domTy : Expr) (typeHashes : List Hash)
    (univs : List Level) (nP : Nat) (extraDepth : Nat) : Option (Nat × List Expr) :=
  let (hd, allArgs) := domTy.getAppFnArgs
  match hd with
  | .const h ls =>
    -- Check that universe arguments match
    if ls.length != univs.length then none
    else if !(List.zip ls univs).all (fun (l₁, l₂) => l₁ == l₂) then none
    else
      -- Check that the first nP arguments match the parameter bvars
      if allArgs.length < nP then none
      else
        let paramArgs := allArgs.take nP
        let expectedParams := (List.range nP).map (fun i => Expr.bvar (extraDepth + nP - 1 - i))
        if paramArgs != expectedParams then none
        else
          -- Find which type hash matches
          let indexArgs := allArgs.drop nP
          go typeHashes 0 h indexArgs
  | _ => none
where
  go : List Hash → Nat → Hash → List Expr → Option (Nat × List Expr)
    | [], _, _, _ => none
    | th :: rest, k, h, idxArgs =>
      if h == th then some (k, idxArgs)
      else go rest (k + 1) h idxArgs

/-- Walk the field telescope of a constructor type (after params stripped and shifted),
    inserting IH binders for recursive fields, and producing the minor type.
    Supports mutual inductives: recursive fields may target different types in the block.
    - `ty`: remaining field telescope
    - `depth`: number of binders entered inside this minor type so far
    - `nTypes`: number of types in the mutual block
    - `baseOffset`: `globalMinorIdx + nTypes - 1` — motive₀ is at bvar (depth + baseOffset)
    - `nP`: number of parameters
    - `nIndices`: number of index arguments for the owner type
    - `typeHashes`: hashes of all types in the block
    - `ownerTypeIdx`: which type this constructor belongs to
    - `fieldDepths`: depths at which each field was bound (most recent first)
    At depth `d`:
    - motive_k is at `bvar (d + baseOffset - k)`
    - param p_i is at `bvar (d + baseOffset + nP - i)` -/
private partial def processFields (ty : Expr) (depth : Nat)
    (nTypes : Nat) (baseOffset : Nat) (nP : Nat) (nIndices : Nat)
    (typeHashes : List Hash) (ctorHash : Hash) (univs : List Level)
    (ownerTypeIdx : Nat) (fieldDepths : List Nat) : Expr :=
  match ty with
  | .forallE domTy body =>
    -- Check if this field is recursive against any type in the block
    match findRecTarget domTy typeHashes univs nP (depth + baseOffset + 1) with
    | some (targetIdx, idxArgs) =>
      -- Recursive field targeting type targetIdx
      -- Under field binder (depth+1): motive_targetIdx is at bvar (depth+1+baseOffset-targetIdx)
      let motiveRef := Expr.bvar (depth + 1 + baseOffset - targetIdx)
      -- IH type: motive_target idxArgs... (bvar 0)
      -- idxArgs are from domTy at the current scope (outside the field binder).
      -- The IH type is inside the field binder, so lift idxArgs by 1 to account for
      -- the new bvar 0 (the field value).
      let liftedIdxArgs := idxArgs.map (fun e => e.liftN 1)
      let ihType := Expr.mkAppN motiveRef (liftedIdxArgs ++ [.bvar 0])
      let liftedBody := body.liftN 1
      let rest := processFields liftedBody (depth + 2)
        nTypes baseOffset nP nIndices typeHashes ctorHash univs ownerTypeIdx (depth :: fieldDepths)
      .forallE domTy (.forallE ihType rest)
    | none =>
      -- Non-recursive field: just bind
      let rest := processFields body (depth + 1)
        nTypes baseOffset nP nIndices typeHashes ctorHash univs ownerTypeIdx (depth :: fieldDepths)
      .forallE domTy rest
  | _ =>
    -- End of telescope: return motive_owner indexArgs... (ctor params... fields...)
    let motiveHere := Expr.bvar (depth + baseOffset - ownerTypeIdx)
    let paramArgs := (List.range nP).map (fun i => .bvar (depth + baseOffset + nP - i))
    let fieldArgs := fieldDepths.reverse.map (fun fd => .bvar (depth - fd - 1))
    let ctorApp := Expr.mkAppN (.const ctorHash univs) (paramArgs ++ fieldArgs)
    let indexArgs := getCtorIndexArgs ty nP
    Expr.mkAppN motiveHere (indexArgs ++ [ctorApp])

/-- Walk a type's forallE binders to find the trailing Sort level. -/
def getTargetSort : Expr → Option Level
  | .sort l => some l
  | .forallE _ body => getTargetSort body
  | _ => none

/-- Check if all fields (after params) in a constructor type are in Prop.
    A field is "in Prop" if its domain type is Sort 0.
    For non-Sort domain types, we conservatively allow them (they are term types). -/
private def allFieldsInProp (ctorTy : Expr) (numParams : Nat) : Bool :=
  go ctorTy 0
where
  go : Expr → Nat → Bool
    | .forallE domTy body, depth =>
      if depth < numParams then go body (depth + 1)
      else
        -- Check domain is not a Sort > 0
        match getTargetSort domTy with
        | some l =>
          match l.normalize.toNat with
          | some 0 => go body (depth + 1)  -- Sort 0 = Prop, OK
          | some _ => false                 -- Sort n (n>0), not Prop
          | none => go body (depth + 1)     -- polymorphic, skip
        | none => go body (depth + 1)       -- non-Sort domain, OK
    | _, _ => true

/-- Determine if large elimination is allowed for this inductive type.
    - Non-Prop inductive (target Sort >= 1): true
    - Prop with 0 constructors (empty type): true
    - Prop with 1 constructor where all fields (after params) are in Prop: true
    - Otherwise: false -/
private def computeAllowsLargeElim (block : InductiveBlock) (typeIdx : Nat) : Bool :=
  match block.types[typeIdx]? with
  | none => true
  | some indTy =>
    let targetSort := getTargetSort indTy.type
    match targetSort with
    | some Level.zero =>
      -- Prop type: check conditions
      match indTy.ctors with
      | [] => true              -- empty type: large elim OK
      | [ctorTy] =>             -- single constructor
        allFieldsInProp ctorTy block.numParams
      | _ => false              -- 2+ constructors: no large elim
    | _ => true                 -- non-Prop: large elim OK

/-- Collect minor types for all constructors across all types in the block. -/
private def collectAllMinors (block : InductiveBlock) (blockHash : Hash) (univs : List Level)
    (nP nT : Nat) (typeHashes : List Hash) : List Expr :=
  go block.types 0 0
where
  go : List InductiveType → Nat → Nat → List Expr
    | [], _, _ => []
    | indTy :: rest, i, globalCtorOffset =>
      let nIdx_i := countForallE indTy.type - nP
      let ctorMinors := (List.range indTy.ctors.length).map fun j =>
        let g := globalCtorOffset + j
        let rawCtorTy := match indTy.ctors[j]? with | some t => t | none => .sort .zero
        let ctorTy := Environment.resolveIRef blockHash rawCtorTy
        let ctorHash := hashCtor blockHash i j
        let stripped := stripForallE ctorTy nP
        let lifted := stripped.liftN (nT + g)
        let baseOffset := g + nT - 1
        processFields lifted 0 nT baseOffset nP nIdx_i typeHashes ctorHash univs i []
      ctorMinors ++ go rest (i + 1) (globalCtorOffset + indTy.ctors.length)

/-- Generate the type of the recursor for a type in an inductive block.
    Supports mutual inductives: the recursor has one motive per type in the block,
    and minors for ALL constructors across ALL types.
    The binder layout is:
      `Π (params...) (C₀ : ...) ... (C_{n-1} : ...) (minor₀...) ... (indices...) (major). C_target indices major`
    Recursive fields get an extra IH argument using the motive for their target type.
    When `allowsLargeElim` is false, all motive targets are Sort 0 (Prop only). -/
def generateRecursorType (block : InductiveBlock) (typeIdx : Nat) (blockHash : Hash) (allowsLargeElim : Bool := true) : Expr :=
  match block.types[typeIdx]? with
  | none => .sort .zero
  | some targetIndTy =>
    let nP := block.numParams
    let nU := block.numUnivParams
    let nT := block.types.length
    let nTargetIdx := countForallE targetIndTy.type - nP
    let univs := (List.range nU).map Level.param
    let motiveUniv := if allowsLargeElim then Level.param nU else Level.zero

    -- Type hashes for all types in the block
    let typeHashes := (List.range nT).map (fun i => hashIndType blockHash i)

    -- Parameter binder types (shared by all types, taken from target type former)
    let paramBinderTypes := extractDomains targetIndTy.type nP

    -- Motive types: one per type in the block
    -- motiveType_k is lifted by k to account for the k earlier motive binders
    let motiveTypes := (List.range nT).map fun k =>
      let indTy_k := match block.types[k]? with | some t => t | none => { type := .sort .zero, ctors := [] }
      let nIdx_k := countForallE indTy_k.type - nP
      let indexDomains_k := extractDomains (stripForallE indTy_k.type nP) nIdx_k
      let typeHash_k := typeHashes[k]!
      let iAppliedInMotive := Expr.mkAppN
        (mkIApplied typeHash_k univs nP nIdx_k)
        ((List.range nIdx_k).map (fun j => .bvar (nIdx_k - 1 - j)))
      let motiveInner := Expr.forallE iAppliedInMotive (.sort motiveUniv)
      let rawMotiveType := indexDomains_k.foldr (fun domTy acc => .forallE domTy acc) motiveInner
      rawMotiveType.liftN k

    -- Minor types for all constructors across all types
    let minorTypes := collectAllMinors block blockHash univs nP nT typeHashes
    let totalMinors := minorTypes.length

    -- Index binder types for the target type (between minors and major)
    let indexDomainsInTypeFormer := extractDomains (stripForallE targetIndTy.type nP) nTargetIdx
    let indexBinderTypes := indexDomainsInTypeFormer.map (fun domTy => domTy.liftN (nT + totalMinors))

    -- Major type: I_target applied to params and index bvars
    let targetTypeHash := typeHashes[typeIdx]!
    let majorType := Expr.mkAppN
      (mkIApplied targetTypeHash univs nP (nT + totalMinors + nTargetIdx))
      ((List.range nTargetIdx).map (fun k => .bvar (nTargetIdx - 1 - k)))

    -- Result body: C_target indices major
    -- C_k is at bvar (nTargetIdx + totalMinors + nT - k) from the result position
    let motiveInResult := Expr.bvar (nTargetIdx + totalMinors + nT - typeIdx)
    let indexBvarsInResult := (List.range nTargetIdx).map (fun k => Expr.bvar (nTargetIdx - k))
    let resultBody := Expr.mkAppN motiveInResult (indexBvarsInResult ++ [.bvar 0])

    -- Assemble: fold from inside out
    let innermost := Expr.forallE majorType resultBody
    let withIndices := indexBinderTypes.foldr (fun idxTy acc => .forallE idxTy acc) innermost
    let withMinors := minorTypes.foldr (fun minorTy acc => .forallE minorTy acc) withIndices
    let withMotives := motiveTypes.foldr (fun motTy acc => .forallE motTy acc) withMinors
    paramBinderTypes.foldr (fun paramTy acc => .forallE paramTy acc) withMotives

/-- Generate RecursorInfo for a type in an inductive block. -/
def generateRecursorInfo (block : InductiveBlock) (typeIdx : Nat) (blockHash : Hash) : RecursorInfo :=
  let typeHash := hashIndType blockHash typeIdx
  let nT := block.types.length
  let nIndices := match block.types[typeIdx]? with
    | some indTy => countForallE indTy.type - block.numParams
    | none => 0
  let totalMinors := block.types.foldl (fun acc indTy => acc + indTy.ctors.length) 0
  let largeElim := computeAllowsLargeElim block typeIdx
  { indHash := typeHash
    blockHash := blockHash
    blkIdx := typeIdx
    nParams := block.numParams
    nMotives := nT
    nMinors := totalMinors
    nIndices := nIndices
    recTy := generateRecursorType block typeIdx blockHash largeElim
    allowsLargeElim := largeElim }

/-- Check if an iref with any of the given type indices appears in an expression.
    This operates on pre-resolution expressions (containing `iref`). -/
private def irefOccursIn (targetIndices : List Nat) (e : Expr) : Bool :=
  match e with
  | .bvar _ => false
  | .sort _ => false
  | .const _ _ => false
  | .iref idx _ => targetIndices.any (· == idx)
  | .app f a => irefOccursIn targetIndices f || irefOccursIn targetIndices a
  | .lam ty body => irefOccursIn targetIndices ty || irefOccursIn targetIndices body
  | .forallE ty body => irefOccursIn targetIndices ty || irefOccursIn targetIndices body
  | .letE ty val body => irefOccursIn targetIndices ty || irefOccursIn targetIndices val || irefOccursIn targetIndices body
  | .proj _ _ s => irefOccursIn targetIndices s

/-- Weak head normalize an expression that may contain `iref` nodes.
    Unfolds constants and performs β/ζ-reduction, preserving iref. -/
private partial def whnfWithIRef (env : Environment) (e : Expr) : Expr :=
  match e with
  | .app fn arg =>
    let fn' := whnfWithIRef env fn
    match fn' with
    | .lam _ty body => whnfWithIRef env (body.instantiate arg)
    | _ => if fn' == fn then e else .app fn' arg
  | .letE _ty val body => whnfWithIRef env (body.instantiate val)
  | .const h univs =>
    match env.getDeclValue h univs with
    | some val => whnfWithIRef env val
    | none => e
  | _ => e

/-- Check if a specific de Bruijn index appears in an expression, shifting under binders. -/
private def bvarOccursIn (idx : Nat) (e : Expr) : Bool :=
  match e with
  | .bvar i => i == idx
  | .app f a => bvarOccursIn idx f || bvarOccursIn idx a
  | .forallE ty body => bvarOccursIn idx ty || bvarOccursIn (idx + 1) body
  | .lam ty body => bvarOccursIn idx ty || bvarOccursIn (idx + 1) body
  | .letE ty val body => bvarOccursIn idx ty || bvarOccursIn idx val || bvarOccursIn (idx + 1) body
  | .proj _ _ s => bvarOccursIn idx s
  | _ => false

/-- Check strict positivity of a de Bruijn variable in an expression.
    The variable must not appear in a negative position (domain of a forallE). -/
private def checkBvarStrictPositivity (bvIdx : Nat) (e : Expr) : Bool :=
  match e with
  | .forallE domTy body =>
    if bvarOccursIn bvIdx domTy then false
    else checkBvarStrictPositivity (bvIdx + 1) body
  | _ => true

/-- Check that a parameter is strictly positive in a raw constructor type.
    `ctorTy` starts from parameter binders; `numParams` is the count of params;
    `paramIdx` is 0-indexed from the outermost parameter. -/
private def checkParamPositiveInCtor (ctorTy : Expr) (numParams paramIdx : Nat) : Bool :=
  go ctorTy 0
where
  go (ty : Expr) (depth : Nat) : Bool :=
    match ty with
    | .forallE domTy body =>
      if depth < numParams then go body (depth + 1)
      else
        -- At depth d, parameter paramIdx (0-indexed from outermost) is bvar (d - 1 - paramIdx)
        let pBvar := depth - 1 - paramIdx
        if !checkBvarStrictPositivity pBvar domTy then false
        else go body (depth + 1)
    | _ => true

/-- Check strict positivity of the inductive type in a constructor argument type.
    The inductive must not appear in a negative position (domain of a forallE).
    Normalizes through definitions to detect hidden negative occurrences.
    Operates on pre-resolution expressions (using `iref`). -/
private partial def checkStrictPositivity (env : Environment) (indIndices : List Nat) (e : Expr) : Bool :=
  let e' := whnfWithIRef env e
  match e' with
  | .forallE domTy body =>
    -- The inductive type must NOT appear in the domain (negative position)
    if irefOccursIn indIndices domTy then false
    else checkStrictPositivity env indIndices body
  | _ =>
    if !irefOccursIn indIndices e' then true
    else
      -- Check nested inductive: iref as argument to a previously-defined inductive
      let (hd, args) := e'.getAppFnArgs
      match hd with
      | .const h _ =>
        match env.getInductiveBlockForType h with
        | some (block, typeIdx) =>
          match block.types[typeIdx]? with
          | some containerIndTy =>
            (List.range args.length).all fun argIdx =>
              let arg := args.getD argIdx (.sort .zero)
              if !irefOccursIn indIndices arg then true
              else if argIdx >= block.numParams then false  -- iref in index arg: reject
              else
                containerIndTy.ctors.all fun ctorTy =>
                  checkParamPositiveInCtor ctorTy block.numParams argIdx
          | none => false
        | none => false  -- iref in arg to non-inductive const (axiom): reject conservatively
      | _ => true  -- head is iref itself or bvar: valid recursive occurrence

/-- Check that a constructor argument satisfies strict positivity.
    Normalizes through definitions to detect hidden negative occurrences.
    Operates on pre-resolution expressions (using `iref`). -/
private partial def checkCtorArgPositivity (env : Environment) (indIndices : List Nat)
    (ctorTy : Expr) (numParams : Nat) : Bool :=
  go ctorTy 0
where
  go (ty : Expr) (depth : Nat) : Bool :=
    match ty with
    | .forallE domTy body =>
      if depth < numParams then
        -- Parameter arguments: skip positivity check
        go body (depth + 1)
      else
        -- Non-parameter arguments: check strict positivity
        -- Normalize domain to see through definitions
        if irefOccursIn indIndices domTy then
          -- The domain mentions the inductive type — check it's strictly positive
          checkStrictPositivity env indIndices domTy
        else
          -- Even if iref not syntactically in domTy, the domain itself might normalize
          -- to reveal hidden negative occurrences. Check the whnf-normalized form.
          let domTy' := whnfWithIRef env domTy
          if domTy' != domTy && irefOccursIn indIndices domTy' then
            checkStrictPositivity env indIndices domTy'
          else
            go body (depth + 1)
    | _ => true

/-- Check that an inductive block is well-formed.
    Checks:
    1. Type formers end in a Sort
    2. Constructor return types are consistent
    3. Strict positivity of inductive occurrences in constructor arguments -/
def checkInductiveBlock (env : Environment) (block : InductiveBlock) : Except String Unit := do
  -- Use type indices for positivity checking (pre-resolution, using iref)
  let indIndices := List.range block.types.length
  let mut typeIdx := 0
  for indTy in block.types do
    -- Check type former ends in Sort
    if !endsInSort indTy.type then
      throw "checkInductiveBlock: type former does not end in Sort"
    -- Check each constructor
    for ctorTy in indTy.ctors do
      -- Check strict positivity
      if !checkCtorArgPositivity env indIndices ctorTy block.numParams then
        throw "checkInductiveBlock: strict positivity violation"
      -- Check iref indices are in range
      if hasInvalidIRef ctorTy block.types.length then
        throw "checkInductiveBlock: iref index out of range"
      -- Check constructor returns its own inductive type with correct arguments
      let nBindings := countForallE ctorTy
      let retTy := getResultType ctorTy
      let (retHead, retArgs) := retTy.getAppFnArgs
      match retHead with
      | .iref idx univs =>
        if idx != typeIdx then
          throw s!"checkInductiveBlock: constructor returns wrong type (iref {idx}, expected {typeIdx})"
        -- Check universe arguments match
        let expectedUnivs := (List.range block.numUnivParams).map Level.param
        if univs != expectedUnivs then
          throw "checkInductiveBlock: constructor return type has wrong universe arguments"
        -- Check parameter arguments are correct bvars
        if retArgs.length < block.numParams then
          throw "checkInductiveBlock: constructor return type has too few arguments"
        let paramArgs := retArgs.take block.numParams
        let expectedParams := (List.range block.numParams).map
          (fun i => Expr.bvar (nBindings - 1 - i))
        if paramArgs != expectedParams then
          throw "checkInductiveBlock: constructor return type has wrong parameter arguments"
      | _ => throw "checkInductiveBlock: constructor must return its inductive type"
    typeIdx := typeIdx + 1
  return ()
where
  endsInSort : Expr → Bool
    | .sort _ => true
    | .forallE _ body => endsInSort body
    | _ => false
  getResultType : Expr → Expr
    | .forallE _ body => getResultType body
    | e => e
  hasInvalidIRef : Expr → Nat → Bool
    | .iref idx _, n => idx >= n
    | .app f a, n => hasInvalidIRef f n || hasInvalidIRef a n
    | .lam ty body, n => hasInvalidIRef ty n || hasInvalidIRef body n
    | .forallE ty body, n => hasInvalidIRef ty n || hasInvalidIRef body n
    | .letE ty val body, n => hasInvalidIRef ty n || hasInvalidIRef val n || hasInvalidIRef body n
    | .proj _ _ s, n => hasInvalidIRef s n
    | _, _ => false

end HashMath
