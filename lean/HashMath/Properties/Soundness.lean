/-
  HashMath.Properties.Soundness — Full type checker soundness (Layer 6)

  This file states the capstone theorem: `checkDecl` preserves
  well-formedness of environments. If we start with a well-formed
  environment and `checkDecl` accepts a new declaration, the resulting
  environment is also well-formed.

  This is the single most important theorem in the verification effort.
  It says: the HashMath type checker never introduces an inconsistency
  that wasn't already present in the axioms.

  STATUS: All proofs are sorry'd.

  WHY PROOFS ARE BLOCKED:
  This theorem depends on ALL other verification layers:
  - Layer 1 (De Bruijn): lifting/substitution correctness
  - Layer 2 (Reduction): whnf agrees with reduction relation
  - Layer 3 (Typing): inferType is sound (Properties/Typing.lean)
  - Layer 4 (DefEq): isDefEq is sound (Properties/DefEqProperties.lean)
  - Layer 5 (Positivity): checkInductiveBlock is sound (Properties/Positivity.lean)

  Additionally, ALL core functions (`inferType`, `isDefEq`, `isSubtype`,
  `whnf`, `whnfCore`, `checkStrictPositivity`) are `partial`, making them
  opaque to Lean's proof kernel.

  PROOF STRATEGY (if `partial` is resolved):
  Case-split on the declaration kind:
  - Axiom: show `inferTypeClosed env ty = .ok (Sort l)` implies the
    axiom's type is well-typed. Uses Layer 3.
  - Definition: show type check + value check + subtype check implies
    the definition is well-typed. Uses Layers 3 + 4.
  - Inductive: show `checkInductiveBlock` ensures positivity, universe
    constraints, and constructor well-typedness. Uses Layer 5 + Layer 3.
  - Quotient: quotient declarations are accepted unconditionally (they
    are axiomatic). Show the resulting env still satisfies WellFormedEnv.
-/

import HashMath.Properties.Spec
import HashMath.Properties.Typing
import HashMath.TypeChecker

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- 6.1 checkDecl preserves well-formedness
-- ═══════════════════════════════════════════════════════════════════

/-- **Capstone theorem**: if `env` is well-formed and `checkDecl` accepts
    a declaration `d`, producing a new environment `env'`, then `env'` is
    also well-formed.

    This means the type checker is *sound*: it never allows a declaration
    that violates the typing discipline. Every axiom has a type that is
    a Sort, every definition's value has the declared type, every inductive
    is strictly positive, etc.

    Blocked by: depends on `inferType_sound`, `isDefEq_sound`,
    `checkInductiveBlock_positivity`, and all underlying Layer 1-5
    results. Also blocked by `checkDecl` calling `partial` functions. -/
theorem checkDecl_preserves_wf
    (env : Environment) (d : Decl) (h : Hash) (env' : Environment) :
    WellFormedEnv env →
    checkDecl env d = .ok (h, env') →
    WellFormedEnv env' := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 6.2 checkDecl produces a correct hash
-- ═══════════════════════════════════════════════════════════════════

/-- **Hash correctness**: the hash returned by `checkDecl` is the
    content hash of the declaration.

    This connects the type checker to the content-addressing scheme:
    the hash you get back is deterministically computed from the
    declaration's content.

    Blocked by: requires unfolding `checkDecl` and `Environment.addDecl`
    to see the hash computation. Since `checkDecl` is not `partial`,
    this might actually be provable with enough lemmas about
    `Environment.addDecl`. -/
theorem checkDecl_hash_correct
    (env : Environment) (d : Decl) (h : Hash) (env' : Environment) :
    checkDecl env d = .ok (h, env') →
    hashDecl d = h := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 6.3 checkDecl extends the environment
-- ═══════════════════════════════════════════════════════════════════

/-- **Extension**: the new environment contains everything the old one
    did, plus the new declaration.

    This is a monotonicity property: `checkDecl` only adds to the
    environment, never removes existing declarations.

    Blocked by: requires reasoning about `Environment.addDecl` and the
    HashMap structure. -/
theorem checkDecl_extends
    (env : Environment) (d : Decl) (h : Hash) (env' : Environment) :
    checkDecl env d = .ok (h, env') →
    (∀ k info, env.lookup k = some info → env'.lookup k = some info) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 6.4 Sequential well-formedness (iterated checkDecl)
-- ═══════════════════════════════════════════════════════════════════

/-- **Sequential soundness**: starting from an empty (well-formed)
    environment and repeatedly applying `checkDecl`, every intermediate
    environment is well-formed.

    This is the property that matters for the CLI: when we process a
    file with many declarations, the final environment is well-formed
    if each `checkDecl` succeeds.

    Blocked by: depends on `checkDecl_preserves_wf`. -/
theorem sequential_checkDecl_wf
    (decls : List Decl)
    (envs : List (Hash × Environment))
    (env₀ : Environment) :
    WellFormedEnv env₀ →
    -- envs is the sequence of results from processing each decl
    (∀ i (hi : i < decls.length),
      ∃ h env' d,
        decls[i]? = some d ∧
        envs[i]? = some (h, env') ∧
        checkDecl
          (if i = 0 then env₀ else (envs[i-1]?.map Prod.snd).getD env₀)
          d = .ok (h, env')) →
    -- Then the final environment is well-formed
    (∀ i, i < envs.length →
      ∃ h env', envs[i]? = some (h, env') ∧ WellFormedEnv env') := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 6.5 Empty environment is well-formed
-- ═══════════════════════════════════════════════════════════════════

/-- **Base case**: the empty environment is trivially well-formed.
    Every lookup returns `none`, so the universal quantifiers in
    `WellFormedEnv` are vacuously true.

    This might be provable depending on how `Environment` and `lookup`
    are defined. -/
theorem empty_env_wf : WellFormedEnv Environment.empty := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- 6.6 Consistency (aspirational)
-- ═══════════════════════════════════════════════════════════════════

/-- **Relative consistency** (aspirational): in a well-formed environment
    built from "safe" axioms (none of which directly assert `False`),
    there is no closed term of type `False`.

    Here `False` would be an empty inductive type (no constructors).
    This is the ultimate soundness guarantee: the type system is
    consistent relative to its axioms.

    This is a research-level theorem requiring a normalization argument
    or model construction. It is explicitly out of scope for the current
    verification effort, but stated here as the north-star goal.

    Blocked by: everything above + a normalization/model argument that
    is currently unknown for this system. -/
theorem relative_consistency
    (env : Environment) (falseHash : Hash) :
    WellFormedEnv env →
    -- falseHash is an empty inductive (no constructors)
    (∃ block, env.getInductiveBlockForType falseHash = some (block, 0) ∧
      block.types = [{ ctors := [], type := .sort .zero : InductiveType }]) →
    -- No closed proof of False exists
    ¬ ∃ e, inferTypeClosed env e = .ok (.const falseHash []) := by
  sorry

end HashMath
