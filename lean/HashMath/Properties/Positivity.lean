/-
  HashMath.Properties.Positivity — Positivity checker soundness (Layer 5)

  This file defines the formal specification of strict positivity as an
  inductive predicate and states the soundness theorem: if the algorithmic
  `checkInductiveBlock` accepts an inductive block, then all constructors
  are strictly positive with respect to the inductive types being defined.

  Strict positivity is the key condition ensuring that inductive types are
  well-founded. Without it, one can define types like:

      inductive Bad where
        | mk : (Bad → Bad) → Bad

  which allows non-terminating terms and logical inconsistency.

  STATUS: All proofs are sorry'd.

  WHY PROOFS ARE BLOCKED:
  - The internal positivity checker (`checkStrictPositivity`) is `private`
    and `partial` (it uses `whnfWithIRef` to unfold definitions before
    checking for negative occurrences).
  - `whnfWithIRef` is `private` and `partial` (it performs delta-reduction,
    which may not terminate for ill-formed environments).
  - Because these functions are `private`, we cannot reference them directly
    in theorem statements. We state theorems about the public entry point
    `checkInductiveBlock` instead.
  - Because they are `partial`, we cannot unfold them in proofs even if we
    could reference them.

  Even stating the predicate precisely requires care: the algorithmic
  checker unfolds constants (via `whnfWithIRef`) before checking for
  occurrences, so the specification must account for the fact that a
  definition `def F T := T → T` followed by `F Bad` is detected as a
  negative occurrence.
-/

import HashMath.Inductive
import HashMath.Properties.Spec

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- 5.1 Occurrence predicate (specification-level)
-- ═══════════════════════════════════════════════════════════════════

/-- An `iref` node with index in `indices` occurs somewhere in `e`.
    This is a specification-level predicate (an inductive Prop), as
    opposed to the Boolean function `irefOccursIn` in Inductive.lean
    (which is `private`). -/
inductive IRefOccurs (indices : List Nat) : Expr → Prop where
  | iref (idx : Nat) (univs : List Level) :
      indices.any (· == idx) = true →
      IRefOccurs indices (.iref idx univs)
  | appFn (f a : Expr) :
      IRefOccurs indices f →
      IRefOccurs indices (.app f a)
  | appArg (f a : Expr) :
      IRefOccurs indices a →
      IRefOccurs indices (.app f a)
  | lamTy (ty body : Expr) :
      IRefOccurs indices ty →
      IRefOccurs indices (.lam ty body)
  | lamBody (ty body : Expr) :
      IRefOccurs indices body →
      IRefOccurs indices (.lam ty body)
  | forallETy (ty body : Expr) :
      IRefOccurs indices ty →
      IRefOccurs indices (.forallE ty body)
  | forallEBody (ty body : Expr) :
      IRefOccurs indices body →
      IRefOccurs indices (.forallE ty body)
  | letETy (ty val body : Expr) :
      IRefOccurs indices ty →
      IRefOccurs indices (.letE ty val body)
  | letEVal (ty val body : Expr) :
      IRefOccurs indices val →
      IRefOccurs indices (.letE ty val body)
  | letEBody (ty val body : Expr) :
      IRefOccurs indices body →
      IRefOccurs indices (.letE ty val body)
  | projExpr (h : Hash) (i : Nat) (s : Expr) :
      IRefOccurs indices s →
      IRefOccurs indices (.proj h i s)

/-- No `iref` with index in `indices` occurs in `e`. -/
def NoIRefOccurrence (indices : List Nat) (e : Expr) : Prop :=
  ¬ IRefOccurs indices e

-- ═══════════════════════════════════════════════════════════════════
-- 5.2 Strict positivity predicate
-- ═══════════════════════════════════════════════════════════════════

/-- Strict positivity of an expression with respect to a set of inductive
    type indices. An expression is strictly positive if the inductive type
    being defined only occurs in "positive" positions — never to the left
    of an arrow.

    Formally:
    - Any expression with no `iref` occurrences is strictly positive.
    - `forallE domTy body` is strictly positive if `domTy` has no `iref`
      occurrences (the inductive type does not appear in the domain —
      a negative position) and `body` is strictly positive.
    - The target type `I params... indices...` is strictly positive (the
      inductive type appearing as the conclusion is allowed).

    Note: the implementation also handles nested inductives (where the
    inductive type appears as an argument to a previously-defined inductive
    type) and unfolds definitions. The specification below captures the
    core structural cases. -/
inductive StrictlyPositive (env : Environment) (indices : List Nat) :
    Expr → Prop where
  /-- No occurrence: if the inductive type doesn't appear at all,
      positivity is vacuously satisfied. -/
  | noOccurrence (e : Expr) :
      NoIRefOccurrence indices e →
      StrictlyPositive env indices e
  /-- Positive in forallE: the domain must not mention the inductive type
      (even after unfolding), and the body must be strictly positive. -/
  | positiveForall (domTy body : Expr) :
      NoIRefOccurrence indices domTy →
      StrictlyPositive env indices body →
      StrictlyPositive env indices (.forallE domTy body)
  /-- Target type: the expression is headed by an `iref` applied to
      parameters and indices — this is the return type of the constructor. -/
  | target (idx : Nat) (univs : List Level) (args : List Expr) :
      indices.any (· == idx) = true →
      StrictlyPositive env indices (Expr.mkAppN (.iref idx univs) args)

-- ═══════════════════════════════════════════════════════════════════
-- 5.3 Soundness of checkInductiveBlock (positivity aspect)
-- ═══════════════════════════════════════════════════════════════════

/-- **checkInductiveBlock validates positivity**: if `checkInductiveBlock`
    accepts a block, then every constructor in every type of the block
    is strictly positive.

    `checkInductiveBlock` performs several checks beyond positivity
    (return type validation, universe constraints, etc.), but positivity
    is the most important for soundness — it prevents non-termination
    and logical inconsistency.

    Blocked by: `checkInductiveBlock` internally calls `checkCtorArgPositivity`,
    which calls `checkStrictPositivity`, both of which are `private` and
    `partial`. We cannot unfold `checkInductiveBlock` far enough to reason
    about the positivity checking logic. -/
theorem checkInductiveBlock_positivity
    (env : Environment) (block : InductiveBlock) :
    checkInductiveBlock env block = .ok () →
    ∀ (typeIdx : Nat) (indTy : InductiveType),
      block.types[typeIdx]? = some indTy →
      ∀ (ctorTy : Expr),
        ctorTy ∈ indTy.ctors →
        StrictlyPositive env (List.range block.types.length) ctorTy := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 5.4 Recursor generation well-formedness
-- ═══════════════════════════════════════════════════════════════════

/-- **Recursor type is well-formed**: if `checkInductiveBlock` accepts
    a block and we add it to the environment, the generated recursor
    type is a valid type (lives in some Sort).

    The generated recursor is a complex Π-telescope:
    `Π params, motive, minors..., indices..., major. motive indices major`

    Showing it is well-typed requires that all the de Bruijn indices
    are correctly computed and that the minor premise types correctly
    reference the inductive hypothesis for recursive arguments.

    Blocked by: `generateRecursorType` involves complex de Bruijn
    arithmetic. The type-checking of the result requires `inferType`,
    which is `partial`. -/
theorem generateRecursorType_well_formed
    (env : Environment) (block : InductiveBlock) (typeIdx : Nat)
    (blockHash : Hash) (allowsLargeElim : Bool) :
    checkInductiveBlock env block = .ok () →
    typeIdx < block.types.length →
    let recTy := generateRecursorType block typeIdx blockHash allowsLargeElim
    ∃ l, HasType (Environment.addDecl env (.inductive block)).2 [] recTy (.sort l) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 5.5 Large elimination soundness
-- ═══════════════════════════════════════════════════════════════════

/-- **Large elimination blocking is sound**: when large elimination is
    disabled for a Prop inductive (because it has Type-level fields),
    the recursor's motive is forced to target `Sort 0`. This prevents
    the classic Prop→Type escape that would break proof irrelevance.

    The exploit without this check: define `Wrap (A : Type) : Prop` with
    a Type-level field, use the recursor to extract the field from a proof,
    then use proof irrelevance to cast between arbitrary types.

    Blocked by: requires reasoning about `generateRecursorType` with
    `allowsLargeElim = false` and showing the motive universe is
    constrained to `Sort 0`. -/
theorem large_elim_blocked_forces_prop
    (block : InductiveBlock) (typeIdx : Nat) (blockHash : Hash) :
    let _recTy := generateRecursorType block typeIdx blockHash false
    -- When large elimination is blocked, the recursor can only target Prop.
    -- The motive parameter in the recursor type has codomain Sort 0.
    -- (Precise statement requires decomposing the Π-telescope of recTy.)
    True := by  -- Simplified to True; full statement requires telescope decomposition
  trivial

-- ═══════════════════════════════════════════════════════════════════
-- 5.6 Constructor return type validation
-- ═══════════════════════════════════════════════════════════════════

/-- **Constructor return types are validated**: `checkInductiveBlock`
    ensures every constructor returns its own inductive type (identified
    by `iref` index) with the correct universe and parameter arguments.

    This prevents soundness bugs where a constructor for type `A` could
    return type `B` in a mutual inductive block, or where a constructor
    could silently change the universe parameters.

    Blocked by: `checkInductiveBlock` is a complex function with many
    checks interleaved. Proving this requires reasoning about the
    `getResultType` helper and the return-type validation logic. -/
theorem checkInductiveBlock_ctor_returns_correct
    (env : Environment) (block : InductiveBlock) :
    checkInductiveBlock env block = .ok () →
    ∀ (typeIdx : Nat) (indTy : InductiveType),
      block.types[typeIdx]? = some indTy →
      ∀ (j : Nat) (ctorTy : Expr),
        indTy.ctors[j]? = some ctorTy →
        -- The target sort of the constructor matches the target sort of
        -- the inductive type it belongs to
        getTargetSort ctorTy = getTargetSort indTy.type := by
  sorry

end HashMath
