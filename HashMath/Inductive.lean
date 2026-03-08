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

/-- Walk the field telescope of a constructor type (after params stripped and shifted),
    inserting IH binders for recursive fields, and producing the minor type.
    - `ty`: remaining field telescope
    - `depth`: number of binders entered inside this minor type so far
    - `motiveIdx`: bvar index of motive at depth 0 of this minor type
    - `nP`: number of parameters
    - `nIndices`: number of index arguments
    - `fieldDepths`: depths at which each field was bound (most recent first)
    At depth `d`, motive is at `bvar (d + motiveIdx)`,
    and param `p_i` is at `bvar (d + motiveIdx + nP - i)`.
    At the conclusion, the minor produces
      `motive indexArgs... (ctor params... fields...)`. -/
private partial def processFields (ty : Expr) (depth : Nat) (motiveIdx : Nat) (nP : Nat)
    (nIndices : Nat) (typeHash ctorHash : Hash) (univs : List Level)
    (fieldDepths : List Nat) : Expr :=
  match ty with
  | .forallE domTy body =>
    -- Check if this field is recursive (type matches I applied to params at this depth)
    let iApplied := mkIApplied typeHash univs nP (depth + motiveIdx + 1)
    if domTy == iApplied then
      -- Recursive field: add field binder, then IH binder
      -- Under field binder (depth+1): motive is at bvar (depth+1+motiveIdx), field is bvar 0
      let ihType := Expr.app (.bvar (depth + 1 + motiveIdx)) (.bvar 0)
      -- Lift body by 1 to account for the inserted IH binder
      let liftedBody := body.liftN 1
      let rest := processFields liftedBody (depth + 2) motiveIdx nP
        nIndices typeHash ctorHash univs (depth :: fieldDepths)
      .forallE domTy (.forallE ihType rest)
    else
      -- Non-recursive field: just bind
      let rest := processFields body (depth + 1) motiveIdx nP
        nIndices typeHash ctorHash univs (depth :: fieldDepths)
      .forallE domTy rest
  | _ =>
    -- End of telescope: return motive indexArgs... (ctor params... fields...)
    let motiveHere := Expr.bvar (depth + motiveIdx)
    let paramArgs := (List.range nP).map (fun i => .bvar (depth + motiveIdx + nP - i))
    let fieldArgs := fieldDepths.reverse.map (fun fd => .bvar (depth - fd - 1))
    let ctorApp := Expr.mkAppN (.const ctorHash univs) (paramArgs ++ fieldArgs)
    -- Extract index args from the constructor's return type (ty has all IH lifts applied)
    let indexArgs := getCtorIndexArgs ty nP
    Expr.mkAppN motiveHere (indexArgs ++ [ctorApp])

/-- Walk a type's forallE binders to find the trailing Sort level. -/
private def getTargetSort : Expr → Option Level
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

/-- Generate the type of the recursor for a single, non-mutual inductive type.
    Supports both non-indexed and indexed inductives.
    The binder layout is:
      `Π (params...) (motive : Π (indices...) (x : I params indices). Sort v)
         (minor₀...) (indices...) (major : I params indices). motive indices major`
    When nIndices = 0, this reduces to the non-indexed case.
    Recursive fields get an extra IH argument in their minor type.
    When `allowsLargeElim` is false, the motive target is Sort 0 (Prop only). -/
def generateRecursorType (block : InductiveBlock) (typeIdx : Nat) (blockHash : Hash) (allowsLargeElim : Bool := true) : Expr :=
  match block.types[typeIdx]? with
  | none => .sort .zero
  | some indTy =>
    let nP := block.numParams
    let nU := block.numUnivParams
    let nC := indTy.ctors.length
    let nIdx := countForallE indTy.type - nP
    let typeHash := hashIndType blockHash typeIdx
    let univs := (List.range nU).map Level.param
    -- The recursor has one extra universe param for the motive target
    -- When large elimination is restricted, the motive can only target Prop (Sort 0)
    let motiveUniv := if allowsLargeElim then Level.param nU else Level.zero

    -- Parameter binder types (from the type former)
    let paramBinderTypes := extractDomains indTy.type nP

    -- Index binder domain types from the type former (after stripping params)
    let indexDomainsInTypeFormer := extractDomains (stripForallE indTy.type nP) nIdx

    -- Motive type: Π (indices...) (x : I params indices). Sort motiveUniv
    -- Under nP param binders:
    -- Build from inside out: innermost is Sort motiveUniv
    -- Then bind x : I params indices (under nIdx index binders inside the motive)
    -- Then bind each index
    let iAppliedInMotive := Expr.mkAppN
      (mkIApplied typeHash univs nP nIdx)
      ((List.range nIdx).map (fun k => .bvar (nIdx - 1 - k)))
    let motiveInner := Expr.forallE iAppliedInMotive (.sort motiveUniv)
    -- Fold index binders from inside out
    let motiveType := indexDomainsInTypeFormer.foldr
      (fun domTy acc => .forallE domTy acc) motiveInner

    -- Minor types: one per constructor
    let minorTypes := (List.range nC).map fun j =>
      let rawCtorTy := match indTy.ctors[j]? with | some t => t | none => .sort .zero
      let ctorTy := Environment.resolveIRef blockHash rawCtorTy
      let ctorHash := hashCtor blockHash typeIdx j
      -- Strip param binders, lift by (j+1) to align with recursor context
      -- At minor_j position (under nP+1+j binders), motive is at bvar j
      let stripped := stripForallE ctorTy nP
      let lifted := stripped.liftN (j + 1)
      processFields lifted 0 j nP nIdx typeHash ctorHash univs []

    -- Index binder types for the recursor (between minors and major)
    -- These are the same domains from the type former, but lifted by (1 + nC)
    -- to account for the motive and minor binders inserted between params and indices
    let indexBinderTypes := indexDomainsInTypeFormer.map (fun domTy => domTy.liftN (1 + nC))

    -- Major type: I applied to params and index bvars
    -- Under nP + 1 + nC + nIdx binders
    let majorType := Expr.mkAppN
      (mkIApplied typeHash univs nP (1 + nC + nIdx))
      ((List.range nIdx).map (fun k => .bvar (nIdx - 1 - k)))

    -- Result body: motive indices major
    -- Under nP + 1 + nC + nIdx + 1 binders:
    -- bvar 0 = major
    -- bvar k (for 1 ≤ k ≤ nIdx) = index (nIdx - k)
    -- bvar (nIdx + nC + 1) = motive
    let motiveInResult := Expr.bvar (nIdx + nC + 1)
    let indexBvarsInResult := (List.range nIdx).map (fun k => Expr.bvar (nIdx - k))
    let resultBody := Expr.mkAppN motiveInResult (indexBvarsInResult ++ [.bvar 0])

    -- Assemble: fold from inside out
    let innermost := Expr.forallE majorType resultBody
    -- Add index binders (fold from inside out)
    let withIndices := indexBinderTypes.foldr (fun idxTy acc => .forallE idxTy acc) innermost
    let withMinors := minorTypes.foldr (fun minorTy acc => .forallE minorTy acc) withIndices
    let withMotive := Expr.forallE motiveType withMinors
    paramBinderTypes.foldr (fun paramTy acc => .forallE paramTy acc) withMotive

/-- Generate RecursorInfo for a type in an inductive block. -/
def generateRecursorInfo (block : InductiveBlock) (typeIdx : Nat) (blockHash : Hash) : RecursorInfo :=
  let typeHash := hashIndType blockHash typeIdx
  let nIndices := match block.types[typeIdx]? with
    | some indTy => countForallE indTy.type - block.numParams
    | none => 0
  let nMinors := match block.types[typeIdx]? with
    | some indTy => indTy.ctors.length
    | none => 0
  let largeElim := computeAllowsLargeElim block typeIdx
  { indHash := typeHash
    blkIdx := typeIdx
    nParams := block.numParams
    nMotives := 1
    nMinors := nMinors
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

/-- Check strict positivity of the inductive type in a constructor argument type.
    The inductive must not appear in a negative position (domain of a forallE).
    Operates on pre-resolution expressions (using `iref`). -/
private def checkStrictPositivity (indIndices : List Nat) (e : Expr) : Bool :=
  match e with
  | .forallE domTy body =>
    -- The inductive type must NOT appear in the domain (negative position)
    if irefOccursIn indIndices domTy then false
    else checkStrictPositivity indIndices body
  | _ => true  -- In the result position, any occurrence is fine

/-- Check that a constructor argument satisfies strict positivity.
    Operates on pre-resolution expressions (using `iref`). -/
private def checkCtorArgPositivity (indIndices : List Nat) (ctorTy : Expr) (numParams : Nat) : Bool :=
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
        if irefOccursIn indIndices domTy then
          -- The domain mentions the inductive type — check it's strictly positive
          checkStrictPositivity indIndices domTy
        else
          go body (depth + 1)
    | _ => true

/-- Check universe constraints on constructor fields.
    For each field after `numParams` leading binders, if the domain type
    is a `Sort l` (i.e. the field is type-valued), check that `l ≤ targetLevel`.
    This prevents e.g. a `Sort 1` field in a `Sort 0` inductive. -/
private def checkFieldUniverses (ctorTy : Expr) (numParams : Nat) (targetLevel : Level) : Except String Unit :=
  go ctorTy 0
where
  go (ty : Expr) (depth : Nat) : Except String Unit :=
    match ty with
    | .forallE domTy body =>
      if depth < numParams then
        go body (depth + 1)
      else
        match getTargetSort domTy with
        | some fieldLevel =>
          match fieldLevel.normalize.leq targetLevel.normalize with
          | some true => go body (depth + 1)
          | some false =>
            throw s!"checkInductiveBlock: field universe Sort {repr fieldLevel} exceeds target Sort {repr targetLevel}"
          | none => go body (depth + 1)  -- skip check for polymorphic levels
        | none => go body (depth + 1)
    | _ => .ok ()

/-- Check that an inductive block is well-formed.
    Checks:
    1. Type formers end in a Sort
    2. Constructor return types are consistent
    3. Strict positivity of inductive occurrences in constructor arguments
    4. Universe constraints: type-valued fields must live in a universe ≤ the target -/
def checkInductiveBlock (_env : Environment) (block : InductiveBlock) : Except String Unit := do
  -- Use type indices for positivity checking (pre-resolution, using iref)
  let indIndices := List.range block.types.length
  for indTy in block.types do
    -- Check type former ends in Sort
    if !endsInSort indTy.type then
      throw "checkInductiveBlock: type former does not end in Sort"
    -- Check each constructor
    for ctorTy in indTy.ctors do
      -- Check strict positivity
      if !checkCtorArgPositivity indIndices ctorTy block.numParams then
        throw "checkInductiveBlock: strict positivity violation"
      -- Check iref indices are in range
      if hasInvalidIRef ctorTy block.types.length then
        throw "checkInductiveBlock: iref index out of range"
      -- Check constructor returns an inductive type from this block
      match (getResultType ctorTy).getAppFn with
      | .iref _ _ => pure ()
      | _ => throw "checkInductiveBlock: constructor must return its inductive type"
    -- Check universe constraints on type-valued fields
    let targetLevel := match getTargetSort indTy.type with
      | some l => l
      | none => Level.zero
    for ctorTy in indTy.ctors do
      checkFieldUniverses ctorTy block.numParams targetLevel
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
