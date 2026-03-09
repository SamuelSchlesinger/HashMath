# HashMath CIC Formal Verification Plan

## Goal

Formally verify that the HashMath type checker is **sound**: if `checkDecl`
accepts a declaration, that declaration is well-typed according to CIC. This
means the environment never contains an inconsistency that wasn't already
present in the axioms the user supplied.

We also want to verify **serialization injectivity**: that distinct terms
produce distinct byte sequences, which is the mathematical foundation
underpinning the content-addressing design.

## A Note on Hashing and Injectivity

**Hash functions are not injective.** SHA-256 maps an infinite domain
(`ByteArray`) to a fixed 256-bit codomain. By the pigeonhole principle,
collisions exist. The existing axiom `sha256_collision_resistant` in `Hash.lean`
is **mathematically false** — it asserts injectivity of SHA-256, which cannot
hold. The theorems `hashLevel_injective`, `hashExpr_injective`, and
`hashDecl_injective` (currently sorry'd) are therefore also false as stated.

What we *can* say:
- **Serialization is injective** (provable, real math). Distinct terms always
  produce distinct byte sequences.
- **Collision resistance is a computational assumption**, not a theorem.
  Finding collisions is infeasible in practice, but collisions exist in
  principle.
- **Type checker soundness does not require hash injectivity.** Soundness is
  about the typing rules, not the addressing scheme.

The verification plan therefore treats hashing and type checking as separate
concerns:
1. Prove serialization injectivity (mathematical content of the Merkle scheme).
2. Prove type checker soundness assuming a well-formed environment.
3. Separately analyze the impact of hypothetical hash collisions on environment
   integrity (an engineering/security argument, not a formal theorem).

**Action item:** The false axiom `sha256_collision_resistant` and the three
`hash*_injective` theorems should be removed or moved behind an explicit
`variable (collision_resistant : ...)` hypothesis, clearly marked as depending
on an unprovable assumption.

## Scope & Non-Goals

**In scope:**
- Soundness of type inference, definitional equality, reduction, subtyping
- Correctness of inductive type validation (positivity, universe constraints,
  recursor generation, large elimination)
- Injectivity of serialization
- De Bruijn infrastructure correctness (lifting, substitution, instantiation)

**Out of scope (axiomatized or non-goals):**
- Hash function injectivity (false; see above)
- Termination of `whnf`/`normalize` (requires a well-founded measure on the
  environment; we use `partial` throughout — proving termination is a separate
  research problem)
- Parser and elaborator correctness (the frontend is untrusted; only the kernel
  matters for soundness)
- Network layer correctness (IPC, DHT)

## Architecture

The verification is organized into **six layers**, ordered from most concrete
(and easiest to verify) to most abstract:

```
Layer 0: Data Structures      — serialization injectivity
Layer 1: De Bruijn Infra      — lifting, substitution, instantiation
Layer 2: Reduction            — determinism, type preservation
Layer 3: Type Inference       — soundness w.r.t. typing judgment
Layer 4: Definitional Equality — equivalence relation, compatibility
Layer 5: Inductive Validation — positivity, recursor, large elim
Layer 6: Full Soundness       — checkDecl preserves consistency
```

Each layer depends on the ones below it. We can make incremental progress and
each layer provides standalone value.

---

## Layer 0: Data Structures — Serialization Injectivity

**Status:** 4 theorems stated in `Properties/SerializeInj.lean`, all sorry'd.
3 hash-injectivity theorems in `Properties/HashInjectivity.lean` are
**false as stated** and should be restructured.

### 0.1 LEB128 Injectivity

```
theorem encodeLEB128_injective :
    encodeLEB128 n = encodeLEB128 m → n = m
```

**Approach:** Induction on `n` and `m`. LEB128 is a prefix-free encoding: the
high bit of each byte indicates whether more bytes follow. Two numbers producing
the same byte sequence must agree byte-by-byte, and the same sequence of 7-bit
groups encodes the same number.

**Difficulty:** Medium. Requires reasoning about `Nat.mod`, `Nat.div`, and
`ByteArray.push`. May need helper lemmas about `UInt8` arithmetic.

**Prerequisite lemmas:**
- `leb128_msb_continuation`: high bit encodes whether more bytes follow
- `leb128_low_bits`: low 7 bits encode `n % 128`

### 0.2 Level Serialization Injectivity

```
theorem serializeLevel_injective :
    serializeLevel l₁ = serializeLevel l₂ → l₁ = l₂
```

**Approach:** Case analysis on the tag byte (first byte determines constructor).
Within each case, use `encodeLEB128_injective` for `Nat` fields and structural
induction for recursive `Level` fields. Since serialization concatenates child
serializations (not child hashes), we need to show the concatenation is
unambiguous. The key is that each constructor's serialized form has a
deterministic structure: the tag determines the layout, and LEB128 is
prefix-free.

**Difficulty:** Medium-Hard. The recursive cases (`succ`, `max`, `imax`) require
showing that the serialized children can be uniquely split apart. For `succ`
this is straightforward (tag + one child). For `max`/`imax` with two children,
we need that `serializeLevel` produces output of deterministic length for a
given level, so the boundary between the two children is recoverable.

**Key helper:**
```
-- The length of serializeLevel l is determined by l
theorem serializeLevel_length_determined :
    serializeLevel l₁ = serializeLevel l₂ → l₁ = l₂
    -- (actually, this IS the injectivity theorem — the approach is mutual
    --  induction showing both byte equality and parsability)
```

### 0.3 Expression & Declaration Serialization Injectivity

```
theorem serializeExpr_injective :
    serializeExpr e₁ = serializeExpr e₂ → e₁ = e₂

theorem serializeDecl_injective :
    serializeDecl d₁ = serializeDecl d₂ → d₁ = d₂
```

**Approach:** Same pattern as Level. Tags 0x10–0x18 for Expr, 0x20–0x23 for
Decl. The Merkle-tree hash scheme uses `hashExpr` (which produces fixed 32-byte
children), but `serializeExpr` produces variable-length output. Injectivity of
serialization follows from tag uniqueness + LEB128 prefix-freeness + structural
induction.

**Difficulty:** Medium-Hard. Expr has 9 constructors with varying structures.
Need a helper lemma about list serialization injectivity.

### 0.4 Cleanup: Remove False Axiom

The axiom `sha256_collision_resistant` in `Hash.lean:81` and the theorems
`hashBytes_injective`, `hashLevel_injective`, `hashExpr_injective`, and
`hashDecl_injective` should be:

- **Option A:** Deleted entirely.
- **Option B:** Moved behind an explicit, clearly-labeled hypothesis:
  ```
  -- This is a computational assumption, not a mathematical truth.
  -- SHA-256 is not injective (pigeonhole principle).
  variable (collision_resistant : ∀ a b, sha256 a = sha256 b → a = b)
  ```
- **Option C:** Restated as a weaker property about serialization:
  ```
  -- If two levels have equal hashes, their serializations collide under SHA-256.
  -- This doesn't imply the levels are equal, but serialization injectivity
  -- means the only way hashes match is via a SHA-256 collision.
  theorem hashLevel_collision :
      hashLevel l₁ = hashLevel l₂ →
      sha256 (serializeLevel l₁) = sha256 (serializeLevel l₂)
  ```

**Recommendation:** Option B — keep the theorems available for reasoning about
the content-addressing design, but make the false assumption explicit and
impossible to miss.

---

## Layer 1: De Bruijn Infrastructure

**Status:** No existing verification. These are the most mechanical proofs and
form the foundation for everything else.

**Files:** `Expr.lean` (functions), new `Properties/DeBruijn.lean` (proofs)

### 1.1 Lifting Properties

```
-- Lifting by 0 is identity
theorem liftN_zero : e.liftN 0 c = e

-- Lifting composes
theorem liftN_liftN :
    (e.liftN n c).liftN m (c + n) = e.liftN (n + m) c

-- Lifting commutes (with appropriate offset)
theorem liftN_comm :
    c₁ ≤ c₂ →
    (e.liftN n₁ c₁).liftN n₂ (c₂ + n₁) = (e.liftN n₂ c₂).liftN n₁ c₁
```

**Difficulty:** Medium. Structural induction on `Expr`, with case splits on
the `bvar` comparison. The binder cases require careful arithmetic.

### 1.2 Substitution Properties

```
-- Substitution into a lifted expression recovers the original
theorem substN_liftN :
    (e.liftN 1 var).substN var s = e

-- Substitution composition (the hard lemma)
theorem substN_substN :
    (e.substN (var+1) (s₁.liftN 1)).substN var s₂ =
    (e.substN var s₂).substN var (s₁.substN var s₂)
```

**Difficulty:** Hard. These are the classic de Bruijn lemmas. The arithmetic
is fiddly but well-understood (see Autosubst, Abella, POPLmark challenge).

### 1.3 Instantiation Properties

```
-- Instantiation is substitution at 0
theorem instantiate_eq_substN_zero : e.instantiate s = e.substN 0 s

-- instantiateRev correctness
theorem instantiateRev_cons : ...
```

**Difficulty:** Easy (follows from substitution properties).

### 1.4 Level Substitution Properties

```
theorem substParams_id :
    (∀ i, i < ls.length → ls[i]? = some (.param i)) →
    l.substParams ls = l

theorem substParams_compose :
    (l.substParams ls₁).substParams ls₂ =
    l.substParams (ls₁.map (Level.substParams ls₂))
```

**Difficulty:** Easy-Medium. Structural induction on `Level`.

### 1.5 hasLooseBVarGe / isClosed Properties

```
theorem liftN_preserves_closed :
    e.isClosed → (e.liftN n c).isClosed

theorem substLevelParams_preserves_structure :
    -- substLevelParams doesn't change de Bruijn structure
    (e.substLevelParams ls).hasLooseBVarGe d = e.hasLooseBVarGe d
```

**Difficulty:** Easy.

---

## Layer 2: Reduction

**Status:** No existing verification. Reduction uses `partial` so we cannot
prove termination, but we can prove correctness properties *assuming
termination* (i.e., "if it returns, then...").

**Files:** `Reduce.lean` (functions), new `Properties/Reduction.lean` (proofs)

### Strategy: Specification-Based Verification

Define an inductive relation `Reduces` capturing one-step reduction, then prove
the implementation agrees with it.

### 2.1 Single-Step Reduction Relation

```
inductive Reduces (env : Environment) : Expr → Expr → Prop where
  | beta    : Reduces env (.app (.lam ty body) arg) (body.instantiate arg)
  | zeta    : Reduces env (.letE ty val body) (body.instantiate val)
  | delta   : env.getDeclValue h univs = some val →
              Reduces env (.const h univs) val
  | deltaApp : env.getDeclValue h univs = some val →
               Reduces env (Expr.mkAppN (.const h univs) args)
                           (Expr.mkAppN val args)
  | iota    : iotaReduce env recHash univs args whnf = some result →
              Reduces env (Expr.mkAppN (.const recHash univs) args) result
  | proj    : projReduce env typeName idx struct' = some result →
              Reduces env (.proj typeName idx struct') result
  | quotLift : ...
  | quotInd  : ...
  | appFn   : Reduces env f f' →
              Reduces env (.app f a) (.app f' a)
```

**Difficulty:** Medium. Defining the relation is straightforward; the iota
rule is the most complex.

### 2.2 whnfCore/whnf Correctness

```
-- whnfCore only performs non-δ reductions
theorem whnfCore_reduces :
    whnfCore env e = e' → e ≠ e' → ReducesStar env e e'

-- whnf performs all reductions including δ
theorem whnf_reduces :
    whnf env e = e' → e ≠ e' → ReducesStar env e e'
```

**Difficulty:** Medium-Hard. Need to trace through the implementation and show
each step corresponds to a valid reduction.

### 2.3 WHNF Characterization

```
-- A WHNF is an expression that cannot reduce at the head
inductive IsWHNF (env : Environment) : Expr → Prop where
  | sort   : IsWHNF env (.sort l)
  | bvar   : IsWHNF env (.bvar i)
  | const  : env.getDeclValue h univs = none →
             IsWHNF env (.const h univs)
  | lam    : IsWHNF env (.lam ty body)
  | forallE : IsWHNF env (.forallE ty body)
  | appNeutral : IsWHNF env head →
                 (∀ result, iotaReduce ... = none) →
                 IsWHNF env (.app head arg)
  ...

theorem whnf_is_whnf :
    whnf env e = e' → IsWHNF env e'
```

**Difficulty:** Medium.

### 2.4 Subject Reduction (Type Preservation)

```
theorem reduces_preserves_type :
    inferType env ctx e = .ok T →
    Reduces env e e' →
    ∃ T', inferType env ctx e' = .ok T' ∧ isDefEq env ctx T T'
```

**Difficulty:** Hard. This is one of the most important metatheoretic properties.
Requires Layers 1, 3, and 4. Naturally mutually dependent with type inference —
may need to prove Layers 2–4 simultaneously or use stratified induction.

---

## Layer 3: Type Inference Soundness

**Status:** No existing verification.

**Files:** `DefEq.lean` (functions), new `Properties/Typing.lean` (proofs)

### 3.1 Typing Judgment Specification

```
inductive HasType (env : Environment) : LocalCtx → Expr → Expr → Prop where
  | bvar  : ctx[i]? = some T →
            HasType env ctx (.bvar i) (T.liftN (i+1))
  | sort  : HasType env ctx (.sort l) (.sort (.succ l))
  | const : env.getDeclType h univs = some T →
            HasType env ctx (.const h univs) T
  | constInd : env.getInductiveBlockForType h = some (block, idx) →
               block.types[idx]? = some indTy →
               HasType env ctx (.const h univs) (indTy.type.substLevelParams univs)
  | constCtor : env.getConstructorInfo h = some info →
                HasType env ctx (.const h univs) (info.ty.substLevelParams univs)
  | constRec : env.getRecursorInfo h = some info →
               HasType env ctx (.const h univs) (info.recTy.substLevelParams univs)
  | app   : HasType env ctx f (.forallE A B) →
            HasType env ctx a A' →
            IsDefEq env ctx A' A →
            HasType env ctx (.app f a) (B.instantiate a)
  | lam   : HasType env ctx ty (.sort l) →
            HasType env (ty :: ctx) body bodyTy →
            HasType env ctx (.lam ty body) (.forallE ty bodyTy)
  | forallE : HasType env ctx ty (.sort l₁) →
              HasType env (ty :: ctx) body (.sort l₂) →
              HasType env ctx (.forallE ty body) (.sort (.imax l₁ l₂))
  | letE  : HasType env ctx ty (.sort _) →
            HasType env ctx val valTy →
            IsDefEq env ctx valTy ty →
            HasType env (ty :: ctx) body bodyTy →
            HasType env ctx (.letE ty val body) (bodyTy.instantiate val)
  | conv  : HasType env ctx e T →
            IsDefEq env ctx T T' →
            HasType env ctx e T'
```

**Difficulty:** Medium to state. This is the reference specification.

### 3.2 Soundness of inferType

```
theorem inferType_sound :
    inferType env ctx e = .ok T →
    HasType env ctx e T
```

**Difficulty:** Hard. Structural induction on `e`, but each case requires
showing the implementation's checks align with the judgment. The `const` case
has many sub-cases (declarations, inductive types, constructors, recursors,
quotients). The `app` case requires relating the `isDefEq` check to the `conv`
rule.

### 3.3 Types are Typed

```
-- Well-typed expressions have well-typed types (types are sorts)
theorem type_of_type :
    inferType env ctx e = .ok T →
    ∃ l, inferType env ctx T = .ok (.sort l)
      ∨ (∃ l', whnf env T = .sort l')
```

**Difficulty:** Hard. Mutual induction with `inferType_sound`.

---

## Layer 4: Definitional Equality

**Status:** No existing verification.

**Files:** `DefEq.lean` (functions), new `Properties/DefEq.lean` (proofs)

### 4.1 Reflexivity

```
theorem isDefEq_refl : isDefEq env ctx e e = true
```

**Difficulty:** Easy. The first line of `isDefEq` checks `t == s`.

### 4.2 Symmetry

```
theorem isDefEq_symm :
    isDefEq env ctx t s = true → isDefEq env ctx s t = true
```

**Difficulty:** Hard. Requires showing every branch of the algorithm is
symmetric. The η-expansion cases and structural η need care.

### 4.3 Transitivity

```
theorem isDefEq_trans :
    isDefEq env ctx t u = true →
    isDefEq env ctx u s = true →
    isDefEq env ctx t s = true
```

**Difficulty:** Very Hard. Transitivity of algorithmic definitional equality
typically requires **confluence** of the reduction system (Church-Rosser
property). This is arguably the hardest single theorem in the entire
verification effort.

**Alternative:** Rather than proving transitivity of the algorithm directly,
prove that the algorithm is sound with respect to a declarative `IsDefEq`
relation that is defined to be an equivalence relation closed under reduction.
Then transitivity holds by definition in the spec, and we only need:

```
theorem isDefEq_sound :
    isDefEq env ctx t s = true → IsDefEq env ctx t s
```

### 4.4 Compatibility with Reduction

```
theorem reduces_implies_defeq :
    ReducesStar env e e' → isDefEq env ctx e e' = true
```

**Difficulty:** Medium.

### 4.5 Proof Irrelevance Correctness

```
theorem proofIrrelCheck_correct :
    proofIrrelCheck env ctx t s = true →
    -- Both terms are proofs of Prop-typed types, and their types are defEq
    ∃ P, inferType env ctx t = .ok P ∧
         (∃ sTy, inferType env ctx s = .ok sTy ∧ isDefEq env ctx P sTy) ∧
         inferType env ctx P = .ok (.sort .zero)
```

**Difficulty:** Medium.

### 4.6 Subtyping Properties

```
theorem isSubtype_refl : isSubtype env ctx T T = true
theorem isDefEq_implies_isSubtype :
    isDefEq env ctx T U = true → isSubtype env ctx T U = true
```

**Difficulty:** Easy (reflexivity), Medium (implication from defEq).

---

## Layer 5: Inductive Type Validation

**Status:** No existing verification. This is the most complex layer.

**Files:** `Inductive.lean`, `TypeChecker.lean`, new `Properties/Inductive.lean`

### 5.1 Positivity Checker Soundness

```
-- Define strict positivity as an inductive predicate
inductive StrictlyPositive (indices : List Nat) : Expr → Nat → Prop where
  | noOccurrence : ¬ irefOccursIn indices e →
                   StrictlyPositive indices e depth
  | positive     : ¬ irefOccursIn indices domTy →
                   StrictlyPositive indices body (depth + 1) →
                   StrictlyPositive indices (.forallE domTy body) depth
  ...

theorem checkCtorArgPositivity_sound :
    checkCtorArgPositivity env indIndices ctorTy numParams = true →
    StrictlyPositive indIndices ctorTy 0
```

**Difficulty:** Hard. The implementation unfolds definitions via `whnfWithIRef`.

### 5.2 Recursor Type Generation Correctness

```
-- The generated recursor type is well-formed
theorem generateRecursorType_well_formed :
    -- Given a well-formed inductive block in the environment...
    checkInductiveBlock env block = .ok () →
    let (h, env') := env.addDecl (.inductive block) →
    let recTy := generateRecursorType block typeIdx h allowLE →
    -- ...the recursor type is a valid type (lives in a Sort)
    ∃ l, inferType env' [] recTy = .ok (.sort l)
```

**Difficulty:** Very Hard. The recursor type is a complex Π-telescope. Need to
show all de Bruijn indices are correctly computed and reference the right types.

### 5.3 Iota Reduction Type Preservation

```
theorem iotaReduce_type_preserves :
    iotaReduce env recHash univs args whnf = some result →
    inferType env ctx (Expr.mkAppN (.const recHash univs) args) = .ok T →
    ∃ T', inferType env ctx result = .ok T' ∧ isDefEq env ctx T T'
```

**Difficulty:** Very Hard. Must show the minor premise application produces
a correctly-typed term, including IH construction for recursive fields.

### 5.4 Large Elimination Soundness

```
-- Blocking large elimination prevents the Prop→Type escape
theorem large_elim_blocked_prevents_cast :
    recInfo.allowsLargeElim = false →
    -- The motive must target Sort 0, so the recursor cannot produce
    -- terms of arbitrary type from proofs
    ∀ univs, (recInfo.recTy.substLevelParams univs) ... → target is Prop
```

**Difficulty:** Hard.

### 5.5 Constructor Return Type Validation

```
theorem checkInductiveBlock_ctor_returns_correct :
    checkInductiveBlock env block = .ok () →
    -- Every constructor returns its own inductive type with correct params
    ∀ i ctorTy, block.types[i]?.bind (fun t => t.ctors[j]?) = some ctorTy →
      getResultType ctorTy = .iref i expectedUnivs expectedParams...
```

**Difficulty:** Medium (this is already checked by the implementation; we're
just showing the check is correct).

---

## Layer 6: Full Soundness

**Status:** The capstone theorem, depending on all previous layers.

**File:** New `Properties/Soundness.lean`

### 6.1 Well-Formed Environment

```
structure WellFormedEnv (env : Environment) : Prop where
  -- Every axiom's type is a Sort
  axioms_typed : ∀ h info, env.lookup h = some info →
    match info.decl with
    | .axiom _ ty => ∃ l, inferType env [] ty = .ok (.sort l)
    | _ => True
  -- Every definition's value has a subtype of the declared type
  defs_typed : ∀ h info, env.lookup h = some info →
    match info.decl with
    | .definition _ ty val =>
      ∃ valTy, inferType env [] val = .ok valTy ∧ isSubtype env [] valTy ty
    | _ => True
  -- Every inductive block passes checkInductiveBlock
  inds_valid : ...
  -- Hash-declaration correspondence
  hash_correct : ∀ h info, env.lookup h = some info →
    hashDecl info.decl = h
```

### 6.2 checkDecl Preserves Well-Formedness

```
theorem checkDecl_preserves_wf :
    WellFormedEnv env →
    checkDecl env d = .ok (h, env') →
    WellFormedEnv env'
```

**Difficulty:** Very Hard. This is the culmination of all other layers.

### 6.3 Consistency (Aspirational)

```
-- In a well-formed environment with no axioms asserting False,
-- there is no closed proof of False.
theorem relative_consistency :
    WellFormedEnv env →
    (∀ h info, env.lookup h = some info →
      match info.decl with
      | .axiom _ _ => -- axiom is "safe" (no False derivable from it alone)
      | _ => True) →
    ¬ ∃ e, inferType env [] e = .ok falseExpr
```

**Difficulty:** Research-level. Requires a normalization argument or model.
This is explicitly out of scope for initial verification but stated here as
the ultimate goal.

---

## Implementation Plan

### Phase 1: Foundation (Layer 0 + Layer 1)

**Goal:** Prove serialization injectivity and de Bruijn infrastructure. Clean
up the false hash-injectivity axiom.

**Deliverables:**
- `Properties/LEB128.lean` — LEB128 injectivity with helper lemmas
- `Properties/SerializeInj.lean` — Fill in sorry'd serialization proofs
- `Properties/DeBruijn.lean` — Lifting, substitution, instantiation lemmas
- `Properties/LevelProperties.lean` — Level substitution, normalization
- Restructure `Hash.lean` — Remove or quarantine false axiom

**Estimated theorem count:** ~25 theorems

**Dependencies:** None (self-contained)

**Priority:** HIGH — Most tractable proofs; serialization injectivity is the
real mathematical content behind content-addressing.

### Phase 2: Specification (Layers 2–4 setup)

**Goal:** Define the typing judgment and reduction relation as inductive types.

**Deliverables:**
- `Properties/Spec.lean` — `HasType`, `Reduces`, `ReducesStar`, `IsDefEq`
  inductive relations
- `Properties/SpecBasic.lean` — Basic properties of the spec

**Estimated theorem count:** ~15 definitions/theorems

**Dependencies:** Layer 1

**Priority:** HIGH — The spec is the reference point for all subsequent proofs.

### Phase 3: Core Metatheory (Layers 2–4)

**Goal:** Prove that `whnf`/`whnfCore` implement the reduction relation,
`inferType` is sound, and `isDefEq` is sound.

**Deliverables:**
- `Properties/Reduction.lean` — Reduction correctness
- `Properties/Typing.lean` — Type inference soundness
- `Properties/DefEq.lean` — Definitional equality properties

**Estimated theorem count:** ~50 theorems

**Dependencies:** Phases 1–2

**Priority:** MEDIUM — This is the hard metatheory. The most valuable single
theorem here is `inferType_sound`.

### Phase 4: Inductive Validation (Layer 5)

**Goal:** Prove positivity, recursor generation, and iota reduction correctness.

**Deliverables:**
- `Properties/Positivity.lean` — Positivity checker soundness
- `Properties/Recursor.lean` — Recursor generation and iota reduction
- `Properties/LargeElim.lean` — Large elimination soundness

**Estimated theorem count:** ~25 theorems

**Dependencies:** Phase 3

**Priority:** MEDIUM-HIGH — Inductive validation has been the source of most
soundness bugs in the implementation.

### Phase 5: Full Soundness (Layer 6)

**Goal:** Prove `checkDecl` preserves well-formedness.

**Deliverables:**
- `Properties/Soundness.lean` — Full soundness theorem

**Estimated theorem count:** ~10 theorems

**Dependencies:** All previous phases

**Priority:** LOW (in terms of when to start) — capstone result.

---

## Technical Considerations

### Handling `partial` Functions

Most core functions (`whnf`, `whnfCore`, `inferType`, `isDefEq`) are `partial`.
This means:

1. We cannot do structural induction on their execution.
2. We must state properties as implications: "if `f x = y`, then ..."
3. Lean 4 treats `partial def` as opaque to the kernel — we cannot unfold them
   in proofs without `@[implemented_by]` or similar mechanisms.

**Practical approach:**
- State all theorems as "if it terminates with result `r`, then `r` satisfies
  property `P`."
- For proofs that need to unfold the function, consider creating a
  `noncomputable def` fuel-bounded version and proving it agrees with the
  `partial` version on terminating inputs.
- Alternatively, refactor key functions to use well-founded recursion (e.g.,
  on expression size + environment size), making them non-`partial`. This is
  a prerequisite for deep Layer 2–4 proofs.

### Avoiding Mathlib

The project has no Mathlib dependency. We should try to maintain this, but may
need basic lemmas about:
- `List` (map, fold, zip, take, drop)
- `Nat` (arithmetic, ordering)
- `ByteArray` (push, size, equality)
- `Option` and `Except`

If too many helpers accumulate, consider a targeted Mathlib import.

### Proof Automation

For repetitive structural induction proofs (especially in Layer 1):
- `simp` with custom lemma sets
- `omega` for Nat arithmetic goals
- `decide` for concrete Boolean goals
- Custom `Expr`/`Level` induction principles if needed

### File Organization

```
lean/HashMath/Properties/
├── LEB128.lean           -- Layer 0: LEB128 injectivity
├── SerializeInj.lean     -- Layer 0: serialization injectivity (existing)
├── HashInjectivity.lean  -- Layer 0: restructured (quarantine false axiom)
├── DeBruijn.lean         -- Layer 1: lifting, substitution, instantiation
├── LevelProperties.lean  -- Layer 1: level substitution, normalization
├── Spec.lean             -- Layers 2-4: typing judgment, reduction relation
├── SpecBasic.lean        -- Layers 2-4: basic spec properties
├── Reduction.lean        -- Layer 2: reduction correctness
├── Typing.lean           -- Layer 3: type inference soundness
├── DefEq.lean            -- Layer 4: definitional equality
├── Positivity.lean       -- Layer 5: positivity checker
├── Recursor.lean         -- Layer 5: recursor generation & iota reduction
├── LargeElim.lean        -- Layer 5: large elimination
└── Soundness.lean        -- Layer 6: full soundness
```

---

## Risk Assessment

| Layer | Difficulty | Risk | Notes |
|-------|-----------|------|-------|
| 0     | Medium    | Low  | Mechanical, well-understood |
| 1     | Medium    | Low  | Classic de Bruijn lemmas |
| 2     | Hard      | Medium | `partial` complicates induction |
| 3     | Hard      | Medium | Large mutual block, many entity cases |
| 4     | Very Hard | High | Transitivity needs confluence or spec trick |
| 5     | Very Hard | High | Recursor generation is intricate |
| 6     | Very Hard | High | Depends on everything else |

### Key Risk: `partial` Functions

The biggest technical risk is that `partial` functions are opaque to Lean's
kernel. Proofs about `whnf`, `inferType`, and `isDefEq` may require either:
- Refactoring to use well-founded recursion (significant implementation work)
- Using `unsafe`/`@[implemented_by]` escape hatches (weakens the guarantee)
- Limiting ourselves to "if it terminates" conditional theorems

**Recommendation:** Start with conditional theorems. If specific proofs are
blocked by opacity, refactor the relevant function on a case-by-case basis.

### Mitigations

- **Start with Layer 0 & 1** — immediate value, builds proof infrastructure
- **State theorems early, prove later** — `sorry` is fine as scaffolding
- **Use the spec trick for transitivity** — define `IsDefEq` as a declarative
  equivalence relation and prove the algorithm is sound w.r.t. it
- **Consider partial verification** — even proving Layers 0–1 alone is valuable

---

## Related Work

- **MetaCoq** (Sozeau et al.) — Verified CIC type checker in Coq. Our system
  is simpler (no metavariables, no opacity, no tactics).
- **Barras' CoqInCoq** — Original verified CIC in Coq.
- **Carneiro's thesis** — Formal specification of Lean's type theory.
- **Autosubst** (Schäfer et al.) — Automated de Bruijn reasoning.

Our system is significantly simpler than full Lean/Coq, making verification
more tractable.

---

## Success Criteria

**Minimum viable verification (Phase 1):**
- Serialization injectivity theorems proven (4 theorems)
- De Bruijn infrastructure lemmas proven (~10 theorems)
- False axiom removed or quarantined
- ~20 theorems total

**Strong verification (Phases 1–3):**
- Typing judgment and reduction relation defined
- `inferType` proven sound for core cases
- ~85 theorems total

**Full verification (Phases 1–5):**
- `checkDecl` soundness theorem
- ~120+ theorems total
- Research-paper-worthy result
