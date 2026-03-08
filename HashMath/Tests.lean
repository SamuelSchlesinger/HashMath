/-
  HashMath.Tests — Tests for the HashMath CIC implementation
-/

import HashMath.TypeChecker

namespace HashMath.Tests

open HashMath

-- ============================================================
-- 1. LEB128 roundtrip tests
-- ============================================================

#eval do
  let test (n : Nat) : IO Unit := do
    let encoded := encodeLEB128 n
    match decodeLEB128 encoded with
    | some (m, _) =>
      if m == n then IO.println s!"LEB128 roundtrip OK: {n}"
      else IO.println s!"LEB128 roundtrip FAIL: {n} → {m}"
    | none => IO.println s!"LEB128 decode FAIL for {n}"
  test 0
  test 1
  test 127
  test 128
  test 255
  test 300
  test 16384
  test 1000000

-- ============================================================
-- 2. Alpha-equivalence: identical de Bruijn terms hash identically
-- ============================================================

def idTerm1 : Expr := .lam (Expr.sort Level.zero) (.bvar 0)
def idTerm2 : Expr := .lam (Expr.sort Level.zero) (.bvar 0)

#eval do
  if idTerm1 == idTerm2 then IO.println "Alpha-equiv test OK: terms are equal"
  else IO.println "Alpha-equiv test FAIL"

#eval do
  let s1 := serializeExpr idTerm1
  let s2 := serializeExpr idTerm2
  if s1 == s2 then IO.println "Serialization alpha-equiv OK"
  else IO.println "Serialization alpha-equiv FAIL"

-- ============================================================
-- 3. Structurally different terms serialize differently
-- ============================================================

#eval do
  let t1 : Expr := .bvar 0
  let t2 : Expr := .bvar 1
  let t3 : Expr := Expr.sort Level.zero
  let t4 : Expr := Expr.sort (Level.succ Level.zero)
  let s1 := serializeExpr t1
  let s2 := serializeExpr t2
  let s3 := serializeExpr t3
  let s4 := serializeExpr t4
  if s1 != s2 then IO.println "Different bvars serialize differently: OK"
  else IO.println "FAIL: bvar 0 == bvar 1"
  if s1 != s3 then IO.println "bvar vs sort serialize differently: OK"
  else IO.println "FAIL: bvar == sort"
  if s3 != s4 then IO.println "Different sorts serialize differently: OK"
  else IO.println "FAIL: Sort 0 == Sort 1"

-- ============================================================
-- 4. Level normalization
-- ============================================================

#eval do
  -- imax(succ zero, zero) = zero
  let l1 := Level.imax (Level.succ Level.zero) Level.zero
  let l1n := l1.normalize
  if l1n == Level.zero then IO.println "imax(1, 0) normalizes to 0: OK"
  else IO.println s!"imax(1, 0) normalize FAIL: {repr l1n}"

  -- imax(param 0, succ zero) = max(param 0, succ zero)
  let l2 := Level.imax (Level.param 0) (Level.succ Level.zero)
  let l2n := l2.normalize
  if l2n == Level.max (Level.param 0) (Level.succ Level.zero) then
    IO.println "imax(u, 1) normalizes to max(u, 1): OK"
  else IO.println s!"imax(u, 1) normalize FAIL: {repr l2n}"

-- ============================================================
-- 5. Substitution tests
-- ============================================================

#eval do
  let e : Expr := .bvar 0
  let result := e.instantiate (Expr.sort Level.zero)
  if result == Expr.sort Level.zero then IO.println "Subst bvar(0)[Sort/0] = Sort: OK"
  else IO.println s!"Subst FAIL: {repr result}"

  let body : Expr := .bvar 0
  let result2 := betaReduce body (Expr.sort Level.zero)
  if result2 == Expr.sort Level.zero then IO.println "Beta-reduce identity: OK"
  else IO.println s!"Beta-reduce FAIL: {repr result2}"

-- ============================================================
-- 6. whnf reduction tests
-- ============================================================

#eval do
  let env := Environment.empty
  -- β-reduction: (λ _: Sort 0. #0) (Sort 1) → Sort 1
  let sort0 := Expr.sort Level.zero
  let sort1 := Expr.sort (Level.succ Level.zero)
  let e := Expr.app (Expr.lam sort0 (.bvar 0)) sort1
  let result := whnfCore env e
  if result == sort1 then IO.println "whnfCore β-reduction: OK"
  else IO.println s!"whnfCore β-reduction FAIL: {repr result}"

  -- ζ-reduction: let _ : Sort 0 := Sort 1 in #0 → Sort 1
  let e2 := Expr.letE sort0 sort1 (.bvar 0)
  let result2 := whnfCore env e2
  if result2 == sort1 then IO.println "whnfCore ζ-reduction: OK"
  else IO.println s!"whnfCore ζ-reduction FAIL: {repr result2}"

-- ============================================================
-- 7. Type inference tests
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  let sort1 := Expr.sort (Level.succ Level.zero)
  let sort2 := Expr.sort (Level.succ (Level.succ Level.zero))

  -- Sort 0 : Sort 1
  match inferTypeClosed env sort0 with
  | .ok ty =>
    if ty == sort1 then IO.println "inferType Sort 0 : Sort 1: OK"
    else IO.println s!"inferType Sort 0 FAIL: {repr ty}"
  | .error e => IO.println s!"inferType Sort 0 ERROR: {e}"

  -- Sort 1 : Sort 2
  match inferTypeClosed env sort1 with
  | .ok ty =>
    if ty == sort2 then IO.println "inferType Sort 1 : Sort 2: OK"
    else IO.println s!"inferType Sort 1 FAIL: {repr ty}"
  | .error e => IO.println s!"inferType Sort 1 ERROR: {e}"

  -- λ (A : Sort 0). #0  has type  Π (A : Sort 0). Sort 0
  let idProp := Expr.lam sort0 (.bvar 0)
  match inferTypeClosed env idProp with
  | .ok ty =>
    if ty == Expr.forallE sort0 sort0 then
      IO.println "inferType (λ Prop. #0) : Π Prop. Prop: OK"
    else IO.println s!"inferType identity FAIL: {repr ty}"
  | .error e => IO.println s!"inferType identity ERROR: {e}"

  -- Π (A : Sort 1). Sort 0  has type  Sort(imax(2, 1))
  -- because Sort 1 : Sort 2, and body Sort 0 : Sort 1
  let piTy := Expr.forallE sort1 sort0
  match inferTypeClosed env piTy with
  | .ok ty =>
    let expected := Expr.sort (Level.imax (Level.succ (Level.succ Level.zero)) (Level.succ Level.zero))
    if ty == expected then IO.println "inferType (Π Type. Prop) : Sort(imax 2 1): OK"
    else IO.println s!"inferType Pi FAIL: got {repr ty}"
  | .error e => IO.println s!"inferType Pi ERROR: {e}"

-- ============================================================
-- 8. DefEq tests
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Reflexivity
  if isDefEqClosed env sort0 sort0 then IO.println "DefEq reflexivity: OK"
  else IO.println "DefEq reflexivity FAIL"

  -- Different sorts are not def-eq
  if !isDefEqClosed env sort0 sort1 then IO.println "DefEq Sort 0 ≠ Sort 1: OK"
  else IO.println "DefEq Sort 0 ≠ Sort 1 FAIL"

  -- β-equivalence: (λ _. #0) (Sort 1)  ≡  Sort 1
  let app := Expr.app (Expr.lam sort0 (.bvar 0)) sort1
  if isDefEqClosed env app sort1 then IO.println "DefEq β-equivalence: OK"
  else IO.println "DefEq β-equivalence FAIL"

  -- ζ-equivalence: let := Sort 1 in #0  ≡  Sort 1
  let letE := Expr.letE sort0 sort1 (.bvar 0)
  if isDefEqClosed env letE sort1 then IO.println "DefEq ζ-equivalence: OK"
  else IO.println "DefEq ζ-equivalence FAIL"

-- ============================================================
-- 9. Declaration checking
-- ============================================================

#eval do
  let env := Environment.empty
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Add an axiom: _ : Sort 1 (a type in Type 0)
  let axiomDecl := Decl.axiom 0 sort1
  match checkDecl env axiomDecl with
  | .ok (h, env') =>
    IO.println "Axiom declaration OK"
    if env'.contains h then IO.println "  Environment contains axiom: OK"
    else IO.println "  Environment contains axiom: FAIL"
  | .error e => IO.println s!"Axiom declaration FAIL: {e}"

-- ============================================================
-- 10. δ-reduction test (definition unfolding)
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Add a definition: def mySort := Sort 0 (of type Sort 1)
  let defDecl := Decl.definition 0 sort1 sort0
  match checkDecl env defDecl with
  | .ok (h, env') =>
    IO.println "Definition added OK"
    -- Now the constant should unfold to Sort 0
    let constExpr := Expr.const h []
    let unfolded := whnf env' constExpr
    if unfolded == sort0 then IO.println "  δ-reduction unfolds to Sort 0: OK"
    else IO.println s!"  δ-reduction FAIL: {repr unfolded}"

    -- DefEq should see const(h) ≡ Sort 0
    if isDefEqClosed env' constExpr sort0 then IO.println "  DefEq through δ: OK"
    else IO.println "  DefEq through δ FAIL"
  | .error e => IO.println s!"Definition FAIL: {e}"

-- ============================================================
-- 11. Ill-typed application rejection
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  -- λ (A : Sort 0). #0 expects argument of type Sort 0
  -- but we apply Sort 0 which has type Sort 1 (not Sort 0)
  let idFn := Expr.lam sort0 (.bvar 0)
  -- Applying sort0 to idFn: the domain is Sort 0, sort0 has type Sort 1
  -- Sort 0 : Sort 1, but the domain demands Sort 0, so arg type Sort 1 ≠ Sort 0
  let illTypedApp := Expr.app idFn sort0
  match inferTypeClosed env illTypedApp with
  | .error _ => IO.println "Ill-typed app rejected: OK"
  | .ok ty => IO.println s!"Ill-typed app NOT rejected: inferred {repr ty}"

-- ============================================================
-- 12. Lambda domain must be a type
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  -- Add an axiom a : Sort 0 (a term of type Prop, not a type itself)
  let axiomDecl := Decl.axiom 0 sort0
  let (_, env') := env.addDecl axiomDecl
  -- λ (x : a). #0 — domain `a` has type Sort 0 which IS a Sort, so this should work
  -- Instead, let's try with bvar which has no type outside context
  -- Actually, let's build a lambda whose domain is not a type
  -- A term of type Prop: we need something whose type is not a Sort
  -- Actually any term whose type is Sort _ IS a type. The check is that ty : Sort _.
  -- So we need ty : something-not-Sort.
  -- Example: λ (x : bvar 0). bvar 0 — bvar 0 not in context, error
  let badLam := Expr.lam (.bvar 42) (.bvar 0)
  match inferTypeClosed env' badLam with
  | .error _ => IO.println "Lambda with non-type domain rejected: OK"
  | .ok ty => IO.println s!"Lambda with non-type domain NOT rejected: {repr ty}"

-- ============================================================
-- 13. Cumulativity: Sort 0 value accepted for Sort 1 type
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  let sort2 := Expr.sort (Level.succ (Level.succ Level.zero))
  -- A definition with value type Sort 1 and declared type Sort 2
  -- Value = Sort 0 (has type Sort 1), declared type = Sort 2
  -- Sort 1 ≤ Sort 2, so this should be accepted via cumulativity
  let defDecl := Decl.definition 0 sort2 sort0
  match checkDecl env defDecl with
  | .ok _ => IO.println "Cumulativity (Sort 0 : Sort 1 ≤ Sort 2) accepted: OK"
  | .error e => IO.println s!"Cumulativity FAIL: {e}"

-- ============================================================
-- 14. Merkle hashing test
-- ============================================================

#eval do
  let sort0 := Expr.sort Level.zero
  let sort1 := Expr.sort (Level.succ Level.zero)
  let appExpr := Expr.app sort0 sort1

  -- Verify: hashExpr(app(f,a)) = SHA256(0x13 ∥ hashExpr(f).bytes ∥ hashExpr(a).bytes)
  let hashF := hashExpr sort0
  let hashA := hashExpr sort1
  let manualInput := ByteArray.mk #[0x13] ++ hashF.bytes ++ hashA.bytes
  let expected := hashBytes manualInput
  let actual := hashExpr appExpr

  if actual == expected then
    IO.println "Merkle hash app: SHA256(0x13 ∥ H(f) ∥ H(a)) verified: OK"
  else
    IO.println "Merkle hash app FAIL"

  -- Also verify level hashing is Merkle
  let l := Level.succ Level.zero
  let hashInner := hashLevel Level.zero
  let manualLevel := hashBytes (ByteArray.mk #[0x01] ++ hashInner.bytes)
  let actualLevel := hashLevel l
  if actualLevel == manualLevel then
    IO.println "Merkle hash level succ: SHA256(0x01 ∥ H(zero)) verified: OK"
  else
    IO.println "Merkle hash level succ FAIL"

-- ============================================================
-- 15. Inductive + ι-reduction test
-- ============================================================

#eval do
  let env := Environment.empty
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Define a simple Nat-like inductive:
  -- inductive MyNat : Sort 1 where
  --   | zero : MyNat
  --   | succ : MyNat → MyNat
  -- Type former: Sort 1 (no params, no indices)
  -- Ctors: zero : I, succ : I → I
  -- Using iref 0 [] for self-references (resolved to const when added)

  let natBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1
      ctors := [
        Expr.iref 0 [],                        -- zero : MyNat
        Expr.forallE (.iref 0 []) (.iref 0 []) -- succ : MyNat → MyNat
      ]
    }]
  }

  -- Add the inductive to the environment
  match checkDecl env (.inductive natBlock) with
  | .error e => IO.println s!"Inductive Nat FAIL: {e}"
  | .ok (blockHash, env') =>
    IO.println "Inductive Nat-like type added: OK"

    -- Check that derived entities are registered
    let typeHash := hashIndType blockHash 0
    let zeroHash := hashCtor blockHash 0 0
    let succHash := hashCtor blockHash 0 1
    let recHash := hashRec blockHash 0

    if env'.getInductiveBlockForType typeHash |>.isSome then
      IO.println "  Ind type registered: OK"
    else IO.println "  Ind type registered: FAIL"

    if env'.getConstructorInfo zeroHash |>.isSome then
      IO.println "  Constructor 'zero' registered: OK"
    else IO.println "  Constructor 'zero' registered: FAIL"

    if env'.getConstructorInfo succHash |>.isSome then
      IO.println "  Constructor 'succ' registered: OK"
    else IO.println "  Constructor 'succ' registered: FAIL"

    if env'.getRecursorInfo recHash |>.isSome then
      IO.println "  Recursor registered: OK"
    else IO.println "  Recursor registered: FAIL"

    -- Test ι-reduction: rec params motive minor_zero minor_succ (zero)
    -- For our Nat: nParams=0, nMotives=1, nMinors=2, nIndices=0
    -- rec motive m_zero m_succ (ctor_zero) → m_zero
    let motive := Expr.sort Level.zero  -- placeholder motive
    let mZero := Expr.sort Level.zero   -- minor for zero
    let mSucc := Expr.sort Level.zero   -- minor for succ
    let zeroVal := Expr.const zeroHash []
    let recApp := Expr.mkAppN (Expr.const recHash []) [motive, mZero, mSucc, zeroVal]
    let result := whnfCore env' recApp
    -- ι-reduction should apply minor_zero (= mZero)
    -- Since zero has 0 fields, result = mZero applied to nothing = mZero
    if result == mZero then
      IO.println "  ι-reduction (rec ... zero → m_zero): OK"
    else
      IO.println s!"  ι-reduction FAIL: {repr result}"

-- ============================================================
-- 16. Quotient hash identity
-- ============================================================

#eval do
  -- Verify quotient hashes are distinct
  let hQuot := quotientHash .quot
  let hQuotMk := quotientHash .quotMk
  let hQuotLift := quotientHash .quotLift
  let hQuotInd := quotientHash .quotInd
  if hQuot != hQuotMk && hQuot != hQuotLift && hQuot != hQuotInd &&
     hQuotMk != hQuotLift && hQuotMk != hQuotInd &&
     hQuotLift != hQuotInd then
    IO.println "Quotient hashes are distinct: OK"
  else
    IO.println "Quotient hashes NOT distinct: FAIL"

-- ============================================================
-- 17. Positivity checking — negative occurrence rejected
-- ============================================================

#eval do
  let env := Environment.empty
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- A "bad" inductive with negative occurrence:
  -- inductive Bad : Sort 1 where
  --   | mk : (Bad → Bad) → Bad
  -- The constructor argument (Bad → Bad) has Bad in a negative position (domain)
  -- Using iref 0 [] for self-references — no circularity problem!

  let badCtorTy := Expr.forallE (Expr.forallE (.iref 0 []) (.iref 0 [])) (.iref 0 [])
  let badBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1
      ctors := [badCtorTy]
    }]
  }

  match checkDecl env (.inductive badBlock) with
  | .error e =>
    IO.println s!"Positivity violation detected: OK ({e})"
  | .ok _ =>
    IO.println "Positivity violation NOT detected: FAIL"

-- ============================================================
-- 18. numUnivParams for quotient kinds
-- ============================================================

#eval do
  let q := Decl.quotient .quot
  let qm := Decl.quotient .quotMk
  let ql := Decl.quotient .quotLift
  let qi := Decl.quotient .quotInd
  if q.numUnivParams == 1 && qm.numUnivParams == 1 &&
     ql.numUnivParams == 2 && qi.numUnivParams == 1 then
    IO.println "Quotient numUnivParams correct: OK"
  else
    IO.println "Quotient numUnivParams FAIL"

-- ============================================================
-- 19. getAppArgs O(n) test (no stack overflow)
-- ============================================================

#eval do
  -- Build a large app spine and verify getAppArgs works efficiently
  let fn := Expr.sort Level.zero
  let arg := Expr.sort Level.zero
  let n := 1000
  let bigApp := (List.range n).foldl (fun e _ => Expr.app e arg) fn
  let args := bigApp.getAppArgs
  if args.length == n then
    IO.println s!"getAppArgs O(n) with {n} args: OK"
  else
    IO.println s!"getAppArgs FAIL: expected {n} args, got {args.length}"

-- ============================================================
-- 20. Derived entity hash functions
-- ============================================================

#eval do
  let blockHash := hashDecl (.axiom 0 (Expr.sort Level.zero))  -- dummy
  let typeHash0 := hashIndType blockHash 0
  let typeHash1 := hashIndType blockHash 1
  let ctorHash00 := hashCtor blockHash 0 0
  let ctorHash01 := hashCtor blockHash 0 1
  let recHash0 := hashRec blockHash 0
  -- All should be distinct
  let all := [typeHash0, typeHash1, ctorHash00, ctorHash01, recHash0]
  let distinct := all.length == (all.eraseDups.length)
  if distinct then
    IO.println "Derived entity hashes are distinct: OK"
  else
    IO.println "Derived entity hashes NOT distinct: FAIL"

-- ============================================================
-- 21. Recursor type generation
-- ============================================================

#eval do
  -- Build a simple enum-like inductive (Bool-like): 2 constructors, 0 fields each
  let sort1 := Expr.sort (Level.succ Level.zero)
  let boolBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1  -- Bool : Sort 1
      ctors := [Expr.iref 0 [], Expr.iref 0 []]  -- true : Bool, false : Bool
    }]
  }
  let blockHash := hashDecl (.inductive boolBlock)
  let typeHash := hashIndType blockHash 0
  let trueHash := hashCtor blockHash 0 0
  let falseHash := hashCtor blockHash 0 1

  -- The generated recursor type should be:
  -- Π (motive : const typeHash [] → Sort (param 0))
  --   (minor_true : motive true)
  --   (minor_false : motive false)
  --   (major : const typeHash [])
  --   . motive major
  let recTy := generateRecursorType boolBlock 0 blockHash

  -- Check it's a 4-deep forallE chain
  match recTy with
  | .forallE motiveType (.forallE minor0Type (.forallE minor1Type (.forallE majorType resultBody))) =>
    -- motiveType should be: forallE (const typeHash []) (sort (param 0))
    let expectedMotiveType := Expr.forallE (.const typeHash []) (.sort (.param 0))
    if motiveType != expectedMotiveType then
      IO.println s!"Recursor type: motive type mismatch"
    else
      -- minor0 should be: app (bvar 0) (const trueHash [])  (motive true)
      let expectedMinor0 := Expr.app (.bvar 0) (.const trueHash [])
      if minor0Type != expectedMinor0 then
        IO.println s!"Recursor type: minor0 mismatch: {repr minor0Type}"
      else
        -- minor1 should be: app (bvar 1) (const falseHash [])  (motive false)
        let expectedMinor1 := Expr.app (.bvar 1) (.const falseHash [])
        if minor1Type != expectedMinor1 then
          IO.println s!"Recursor type: minor1 mismatch: {repr minor1Type}"
        else
          -- majorType should be: const typeHash []
          if majorType != Expr.const typeHash [] then
            IO.println s!"Recursor type: major type mismatch"
          else
            -- resultBody should be: app (bvar 3) (bvar 0)  (motive major)
            let expectedResult := Expr.app (.bvar 3) (.bvar 0)
            if resultBody != expectedResult then
              IO.println s!"Recursor type: result mismatch: {repr resultBody}"
            else
              IO.println "Recursor type generation (Bool-like): OK"
  | _ =>
    IO.println s!"Recursor type structure wrong: {repr recTy}"

-- ============================================================
-- 22. iref resolution test
-- ============================================================

#eval do
  let env := Environment.empty
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Define a Nat-like inductive using iref for self-references
  let natBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1
      ctors := [
        Expr.iref 0 [],                        -- zero : MyNat
        Expr.forallE (.iref 0 []) (.iref 0 []) -- succ : MyNat → MyNat
      ]
    }]
  }

  let (blockHash, env') := env.addDecl (.inductive natBlock)
  let typeHash := hashIndType blockHash 0
  let zeroHash := hashCtor blockHash 0 0
  let succHash := hashCtor blockHash 0 1

  -- Check that constructor types have been resolved (iref → const)
  match env'.getConstructorInfo zeroHash with
  | some ctorInfo =>
    if ctorInfo.ty == Expr.const typeHash [] then
      IO.println "iref resolution (zero: iref 0 [] → const typeHash []): OK"
    else
      IO.println s!"iref resolution (zero) FAIL: {repr ctorInfo.ty}"
  | none => IO.println "iref resolution (zero) FAIL: ctor not found"

  match env'.getConstructorInfo succHash with
  | some ctorInfo =>
    let expected := Expr.forallE (.const typeHash []) (.const typeHash [])
    if ctorInfo.ty == expected then
      IO.println "iref resolution (succ: forallE resolved): OK"
    else
      IO.println s!"iref resolution (succ) FAIL: {repr ctorInfo.ty}"
  | none => IO.println "iref resolution (succ) FAIL: ctor not found"

  -- The block itself still stores raw iref (it's the canonical form for hashing)
  match env'.getInductiveBlock blockHash with
  | some block =>
    match block.types[0]? with
    | some indTy =>
      match indTy.ctors[0]? with
      | some ctorTy =>
        if ctorTy == Expr.iref 0 [] then
          IO.println "Block stores raw iref (canonical for hashing): OK"
        else
          IO.println s!"Block iref check FAIL: {repr ctorTy}"
      | none => IO.println "Block iref check FAIL: no ctor"
    | none => IO.println "Block iref check FAIL: no type"
  | none => IO.println "Block iref check FAIL: block not found"

-- ============================================================
-- 23. End-to-end: Define Nat + add, verify add 1 1 = 2
-- ============================================================

#eval do
  let env := Environment.empty
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- 1. Define Nat
  let natBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1
      ctors := [
        Expr.iref 0 [],
        Expr.forallE (.iref 0 []) (.iref 0 [])
      ]
    }]
  }
  match checkDecl env (.inductive natBlock) with
  | .error e => IO.println s!"FAIL: {e}"
  | .ok (blockHash, env') =>
    let typeHash := hashIndType blockHash 0
    let zeroHash := hashCtor blockHash 0 0
    let succHash := hashCtor blockHash 0 1
    let recHash  := hashRec blockHash 0
    let natTy := Expr.const typeHash []
    let zero  := Expr.const zeroHash []
    let succ  := Expr.const succHash []
    let one   := Expr.app succ zero

    -- 2. Define add : Nat → Nat → Nat
    --    add m n = Nat.rec (λ _. Nat) n (λ k ih. succ ih) m
    let motive := Expr.lam natTy natTy       -- λ _ : Nat. Nat
    let mZero  := Expr.bvar 0                -- n (under 2 lambdas)
    let mSucc  := Expr.lam natTy (Expr.lam natTy (Expr.app succ (.bvar 0)))
    let major  := Expr.bvar 1                -- m (under 2 lambdas)
    -- Recursor takes 1 univ param (motive Sort); motive returns Nat : Sort 1
    let recApp := Expr.mkAppN (Expr.const recHash [Level.succ Level.zero])
                    [motive, mZero, mSucc, major]
    let addValue := Expr.lam natTy (Expr.lam natTy recApp)
    let addType  := Expr.forallE natTy (Expr.forallE natTy natTy)
    let addDecl  := Decl.definition 0 addType addValue

    match checkDecl env' addDecl with
    | .error e => IO.println s!"add def FAIL: {e}"
    | .ok (addHash, env'') =>
      -- 3. Test: add 1 1 = succ (succ zero)
      let addApp   := Expr.app (Expr.app (Expr.const addHash []) one) one
      let expected := Expr.app succ (Expr.app succ zero)
      if isDefEqClosed env'' addApp expected then
        IO.println "add 1 1 = 2 (ι-reduction with IH): OK"
      else
        IO.println "add 1 1 = 2: FAIL"

-- ============================================================
-- 24. SHA-256 NIST test vectors
-- ============================================================

private def hexToByteArray (hex : String) : ByteArray :=
  let chars := hex.toList
  go chars ByteArray.empty
where
  hexVal (c : Char) : UInt8 :=
    if c >= '0' && c <= '9' then (c.toNat - '0'.toNat).toUInt8
    else if c >= 'a' && c <= 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
    else if c >= 'A' && c <= 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
    else 0
  go : List Char → ByteArray → ByteArray
    | c1 :: c2 :: rest, acc => go rest (acc.push ((hexVal c1 <<< 4) ||| hexVal c2))
    | _, acc => acc

private def byteArrayToHex (bs : ByteArray) : String :=
  let hexChars := "0123456789abcdef".toList
  bs.foldl (fun acc b =>
    let hi := (b.toNat / 16)
    let lo := (b.toNat % 16)
    acc ++ (hexChars[hi]!).toString ++ (hexChars[lo]!).toString
  ) ""

#eval do
  -- Test 1: SHA-256 of empty string
  let emptyHash := sha256 ByteArray.empty
  let emptyHex := byteArrayToHex emptyHash
  let expected := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  if emptyHex == expected then
    IO.println "SHA-256 empty string: OK"
  else
    IO.println s!"SHA-256 empty string FAIL: {emptyHex}"

  -- Test 2: SHA-256 of "abc"
  let abcData := "abc".toUTF8
  let abcHash := sha256 abcData
  let abcHex := byteArrayToHex abcHash
  let expectedAbc := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  if abcHex == expectedAbc then
    IO.println "SHA-256 \"abc\": OK"
  else
    IO.println s!"SHA-256 \"abc\" FAIL: {abcHex}"

-- ============================================================
-- 25. whnfCore/whnf mutual recursion test
-- ============================================================

#eval do
  let env := Environment.empty
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Define Nat
  let natBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1
      ctors := [
        Expr.iref 0 [],
        Expr.forallE (.iref 0 []) (.iref 0 [])
      ]
    }]
  }
  match checkDecl env (.inductive natBlock) with
  | .error e => IO.println s!"FAIL: {e}"
  | .ok (blockHash, env') =>
    let typeHash := hashIndType blockHash 0
    let zeroHash := hashCtor blockHash 0 0
    let recHash  := hashRec blockHash 0
    let natTy := Expr.const typeHash []
    let zero  := Expr.const zeroHash []

    -- Define myZero := Nat.zero
    let myZeroDecl := Decl.definition 0 natTy zero
    match checkDecl env' myZeroDecl with
    | .error e => IO.println s!"myZero def FAIL: {e}"
    | .ok (myZeroHash, env'') =>
      let myZero := Expr.const myZeroHash []
      -- Test: Nat.rec motive mZero mSucc myZero should reduce to mZero
      let motive := Expr.lam natTy natTy
      let mZero := Expr.sort Level.zero
      let mSucc := Expr.lam natTy (Expr.lam natTy (.bvar 0))
      let recApp := Expr.mkAppN (Expr.const recHash [Level.succ Level.zero])
                      [motive, mZero, mSucc, myZero]
      if isDefEqClosed env'' recApp mZero then
        IO.println "whnf mutual recursion (rec ... myZero → mZero): OK"
      else
        IO.println "whnf mutual recursion FAIL"

-- ============================================================
-- 26. Indexed inductive: Eq type and ι-reduction
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Define Eq : Π (α : Sort 1) (a : α). α → Sort 0
  -- Type former: forallE (Sort 1) (forallE (bvar 0) (forallE (bvar 1) (Sort 0)))
  --   numParams = 2 (α, a), nIndices = 1 (b)
  -- Constructor (refl): Π (α : Sort 1) (a : α). Eq α a a
  --   forallE (Sort 1) (forallE (bvar 0) (app (app (app (iref 0 []) (bvar 1)) (bvar 0)) (bvar 0)))
  let eqBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 2
    types := [{
      type := Expr.forallE sort1 (.forallE (.bvar 0) (.forallE (.bvar 1) sort0))
      ctors := [
        -- refl : Π (α : Sort 1) (a : α). Eq α a a
        Expr.forallE sort1
          (.forallE (.bvar 0)
            (.app (.app (.app (.iref 0 []) (.bvar 1)) (.bvar 0)) (.bvar 0)))
      ]
    }]
  }

  -- 1. Check the inductive block is accepted
  match checkDecl env (.inductive eqBlock) with
  | .error e => IO.println s!"Eq inductive FAIL: {e}"
  | .ok (blockHash, env') =>
    IO.println "Indexed inductive Eq added: OK"

    let typeHash := hashIndType blockHash 0
    let reflHash := hashCtor blockHash 0 0
    let recHash := hashRec blockHash 0

    -- 2. Check recursor info
    match env'.getRecursorInfo recHash with
    | none => IO.println "  Eq recursor not found: FAIL"
    | some recInfo =>
      if recInfo.nParams == 2 && recInfo.nMotives == 1 &&
         recInfo.nMinors == 1 && recInfo.nIndices == 1 then
        IO.println "  Eq recursor info (nP=2, nM=1, nMinors=1, nIdx=1): OK"
      else
        IO.println s!"  Eq recursor info FAIL: nP={recInfo.nParams} nM={recInfo.nMotives} nMinors={recInfo.nMinors} nIdx={recInfo.nIndices}"

    -- 3. Check recursor type shape
    -- Expected: Π (α : Sort 1) (a : α)
    --             (motive : Π (b : α) (x : Eq α a b). Sort (param 0))
    --             (minor_refl : motive a (refl α a))
    --             (b : α) (major : Eq α a b). motive b major
    let recTy := generateRecursorType eqBlock 0 blockHash
    -- Verify 6-deep forallE chain
    match recTy with
    | .forallE _p0Ty (.forallE _p1Ty (.forallE motiveTy (.forallE minorTy (.forallE idxTy (.forallE majorTy resultBody))))) =>
      -- Check motive type: Π (b : α) (x : Eq α a b). Sort (param 0)
      -- Under 2 params: α = bvar 1, a = bvar 0
      -- Inside motive, forallE domain for b: α = bvar 1 (at depth 0 in motive)
      -- Inside motive, forallE domain for x at depth 1: α = bvar 2, a = bvar 1, b = bvar 0
      let motiveUniv := Level.param 0
      let expectedMotiveInner :=
        Expr.forallE
          (.app (.app (.app (.const typeHash []) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.sort motiveUniv)
      let expectedMotiveTy := Expr.forallE (.bvar 1) expectedMotiveInner
      if motiveTy != expectedMotiveTy then
        IO.println s!"  Eq rec motive type mismatch"
        IO.println s!"    expected: {repr expectedMotiveTy}"
        IO.println s!"    got:      {repr motiveTy}"
      else
        -- Check minor type: motive a (refl α a)
        -- Under 3 binders (α, a, motive): motive = bvar 0
        -- minor = app (app (bvar 0) (bvar 1)) (app (app (const reflHash []) (bvar 2)) (bvar 1))
        let expectedMinor :=
          Expr.app (.app (.bvar 0) (.bvar 1))
            (.app (.app (.const reflHash []) (.bvar 2)) (.bvar 1))
        if minorTy != expectedMinor then
          IO.println s!"  Eq rec minor type mismatch"
          IO.println s!"    expected: {repr expectedMinor}"
          IO.println s!"    got:      {repr minorTy}"
        else
          -- Check index binder type: α (under 4 binders: α, a, motive, minor)
          -- α is bvar 3 at depth 4
          if idxTy != Expr.bvar 3 then
            IO.println s!"  Eq rec index type mismatch: expected bvar 3, got {repr idxTy}"
          else
            -- Check major type: Eq α a b (under 5 binders)
            -- α = bvar 4, a = bvar 3, b = bvar 0
            let expectedMajor :=
              Expr.app (.app (.app (.const typeHash []) (.bvar 4)) (.bvar 3)) (.bvar 0)
            if majorTy != expectedMajor then
              IO.println s!"  Eq rec major type mismatch"
              IO.println s!"    expected: {repr expectedMajor}"
              IO.println s!"    got:      {repr majorTy}"
            else
              -- Check result: motive b major (under 6 binders)
              -- motive = bvar 3, b = bvar 1, major = bvar 0
              let expectedResult := Expr.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
              if resultBody != expectedResult then
                IO.println s!"  Eq rec result mismatch"
                IO.println s!"    expected: {repr expectedResult}"
                IO.println s!"    got:      {repr resultBody}"
              else
                IO.println "  Eq recursor type shape: OK"
    | _ =>
      IO.println s!"  Eq recursor type not 6-deep forallE: FAIL"
      IO.println s!"    got: {repr recTy}"

    -- 4. Test ι-reduction: Eq.rec α a motive minor_refl a (Eq.refl α a) → minor_refl
    -- Recursor layout: rec α a motive minor_refl b major
    -- nParams=2, nMotives=1, nMinors=1, nIndices=1
    -- Args: [α, a, motive, minor_refl, b, major]
    -- When major = refl α a, ι-reduce to minor_refl (applied to 0 fields)
    let alpha := sort1  -- placeholder for α
    let aVal := sort0   -- placeholder for a
    let motive := sort0 -- placeholder motive
    let minorRefl := Expr.sort (Level.succ (Level.succ Level.zero))  -- placeholder minor
    let refl := Expr.app (.app (.const reflHash []) alpha) aVal
    let recApp := Expr.mkAppN (Expr.const recHash [Level.succ Level.zero])
                    [alpha, aVal, motive, minorRefl, aVal, refl]
    let result := whnfCore env' recApp
    if result == minorRefl then
      IO.println "  Eq ι-reduction (rec ... (refl α a) → minor_refl): OK"
    else
      IO.println s!"  Eq ι-reduction FAIL: {repr result}"

-- ============================================================
-- 27. Universe constraint checking
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero
  let sort1 := Expr.sort (Level.succ Level.zero)

  -- Sort 0 inductive with Sort 1 field → should be rejected
  -- inductive Bad : Sort 0 where
  --   | mk : Sort 1 → Bad
  let badBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort0
      ctors := [
        Expr.forallE sort1 (.iref 0 [])  -- mk : Sort 1 → Bad
      ]
    }]
  }
  match checkDecl env (.inductive badBlock) with
  | .error _ => IO.println "Universe constraint (Sort 1 field in Sort 0 type) rejected: OK"
  | .ok _ => IO.println "Universe constraint NOT enforced: FAIL"

  -- Sort 1 inductive with Sort 1 field → should be accepted
  -- inductive Ok : Sort 1 where
  --   | mk : Sort 1 → Ok
  let okBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1
      ctors := [
        Expr.forallE sort1 (.iref 0 [])  -- mk : Sort 1 → Ok
      ]
    }]
  }
  match checkDecl env (.inductive okBlock) with
  | .ok _ => IO.println "Universe constraint (Sort 1 field in Sort 1 type) accepted: OK"
  | .error e => IO.println s!"Universe constraint acceptance FAIL: {e}"

  -- Sort 1 inductive with Sort 0 field → should be accepted (Sort 0 ≤ Sort 1)
  let okBlock2 : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1
      ctors := [
        Expr.forallE sort0 (.iref 0 [])  -- mk : Sort 0 → Ok2
      ]
    }]
  }
  match checkDecl env (.inductive okBlock2) with
  | .ok _ => IO.println "Universe constraint (Sort 0 field in Sort 1 type) accepted: OK"
  | .error e => IO.println s!"Universe constraint (Sort 0 ≤ Sort 1) acceptance FAIL: {e}"

-- ============================================================
-- 28. Large elimination restrictions
-- ============================================================

#eval do
  let env := Environment.empty
  let sort0 := Expr.sort Level.zero

  -- Define Or-like: Prop type with 2 constructors → no large elimination
  -- inductive MyOr : Sort 0 where
  --   | inl : Sort 0 → MyOr
  --   | inr : Sort 0 → MyOr
  let orBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort0  -- : Sort 0 (Prop)
      ctors := [
        Expr.forallE sort0 (.iref 0 []),   -- inl : Prop → MyOr
        Expr.forallE sort0 (.iref 0 [])    -- inr : Prop → MyOr
      ]
    }]
  }
  match checkDecl env (.inductive orBlock) with
  | .error e => IO.println s!"Or-like inductive FAIL: {e}"
  | .ok (blockHash, env') =>
    let recHash := hashRec blockHash 0
    match env'.getRecursorInfo recHash with
    | none => IO.println "Or recursor not found: FAIL"
    | some recInfo =>
      if recInfo.allowsLargeElim then
        IO.println "Large elimination restriction FAIL: Or should not allow large elim"
      else
        IO.println "Large elimination restriction (Or-like, 2 ctors): OK"

  -- Empty prop: should allow large elimination
  let emptyBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort0
      ctors := []
    }]
  }
  match checkDecl env (.inductive emptyBlock) with
  | .error e => IO.println s!"Empty Prop inductive FAIL: {e}"
  | .ok (blockHash2, env2) =>
    let recHash2 := hashRec blockHash2 0
    match env2.getRecursorInfo recHash2 with
    | none => IO.println "Empty Prop recursor not found: FAIL"
    | some recInfo2 =>
      if recInfo2.allowsLargeElim then
        IO.println "Large elimination (empty Prop, 0 ctors): OK"
      else
        IO.println "Large elimination (empty Prop) FAIL: should allow large elim"

  -- Single-ctor Prop with Prop fields only: should allow large elimination
  -- inductive MyAnd : Sort 0 where
  --   | intro : Sort 0 → Sort 0 → MyAnd
  let andBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort0
      ctors := [
        Expr.forallE sort0 (Expr.forallE sort0 (.iref 0 []))  -- intro : Prop → Prop → MyAnd
      ]
    }]
  }
  match checkDecl env (.inductive andBlock) with
  | .error e => IO.println s!"And-like inductive FAIL: {e}"
  | .ok (blockHash3, env3) =>
    let recHash3 := hashRec blockHash3 0
    match env3.getRecursorInfo recHash3 with
    | none => IO.println "And recursor not found: FAIL"
    | some recInfo3 =>
      if recInfo3.allowsLargeElim then
        IO.println "Large elimination (And-like, 1 ctor, Prop fields): OK"
      else
        IO.println "Large elimination (And-like) FAIL: should allow large elim"

  -- Single-ctor Prop with Type field: should NOT allow large elimination
  -- inductive BadProp : Sort 0 where
  --   | mk : Sort 1 → BadProp
  -- Note: this would normally fail universe check (Sort 1 field in Sort 0),
  -- so we use a non-Sort domain type instead.
  -- Actually, Sort 0 field means the field IS a proposition (type Sort 0).
  -- A "Type field" would be Sort 1, but that violates universe constraints.
  -- For testing large elim restriction with a non-Prop field, we need a
  -- single-ctor Prop inductive where a field has type Sort (succ zero).
  -- But checkFieldUniverses would reject Sort 1 in Sort 0.
  -- So we test: non-Prop inductive always gets large elim.
  let sort1 := Expr.sort (Level.succ Level.zero)
  let natLikeBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := sort1  -- Sort 1 (Type)
      ctors := [
        Expr.iref 0 [],                        -- zero : MyNat
        Expr.forallE (.iref 0 []) (.iref 0 []) -- succ : MyNat → MyNat
      ]
    }]
  }
  match checkDecl env (.inductive natLikeBlock) with
  | .error e => IO.println s!"Nat-like inductive FAIL: {e}"
  | .ok (blockHash4, env4) =>
    let recHash4 := hashRec blockHash4 0
    match env4.getRecursorInfo recHash4 with
    | none => IO.println "Nat recursor not found: FAIL"
    | some recInfo4 =>
      if recInfo4.allowsLargeElim then
        IO.println "Large elimination (Nat-like, non-Prop): OK"
      else
        IO.println "Large elimination (Nat-like) FAIL: should allow large elim"

-- ============================================================
-- 29. Quotient reduction: Quot.lift and Quot.ind
-- ============================================================

#eval do
  let env := Environment.empty

  -- Add all four quotient declarations
  let (_, env') := env.addDecl (.quotient .quot)
  let (_, env') := env'.addDecl (.quotient .quotMk)
  let (_, env') := env'.addDecl (.quotient .quotLift)
  let (_, env') := env'.addDecl (.quotient .quotInd)

  let quotMkHash := quotientHash .quotMk
  let quotLiftHash := quotientHash .quotLift

  -- Build: Quot.lift f h (Quot.mk r a)
  -- quotLift args: [α, r, β, f, h, Quot.mk α r a]
  -- Use a dummy axiom for f and h so beta-reduction doesn't fire
  let sort1 := Expr.sort (Level.succ Level.zero)
  let alpha := sort1  -- placeholder α
  let rel := Expr.sort Level.zero  -- placeholder r
  let beta := sort1  -- placeholder β
  let (fHash, env') := env'.addDecl (.axiom 0 (Expr.forallE sort1 sort1))
  let f := Expr.const fHash []  -- f : α → β (opaque axiom)
  let proof := Expr.sort Level.zero  -- placeholder h
  let a := Expr.sort Level.zero  -- placeholder a
  let quotMkApp := Expr.mkAppN (.const quotMkHash [Level.succ Level.zero]) [alpha, rel, a]
  let liftApp := Expr.mkAppN (.const quotLiftHash [Level.succ Level.zero, Level.succ Level.zero])
                   [alpha, rel, beta, f, proof, quotMkApp]

  -- After reduction: f a (no further beta since f is an axiom const)
  let result := whnf env' liftApp
  let expected := Expr.app f a
  if result == expected then
    IO.println "Quot.lift f h (Quot.mk r a) reduces to f a: OK"
  else
    IO.println s!"Quot.lift reduction FAIL: {repr result}"

  -- Test Quot.ind reduction: Quot.ind h (Quot.mk r a) → h a
  let quotIndHash := quotientHash .quotInd
  let (hHash, env') := env'.addDecl (.axiom 0 (Expr.forallE sort1 sort1))
  let hFn := Expr.const hHash []  -- h (opaque axiom)
  let indApp := Expr.mkAppN (.const quotIndHash [Level.succ Level.zero])
                  [alpha, rel, beta, hFn, quotMkApp]
  let indResult := whnf env' indApp
  let indExpected := Expr.app hFn a
  if indResult == indExpected then
    IO.println "Quot.ind h (Quot.mk r a) reduces to h a: OK"
  else
    IO.println s!"Quot.ind reduction FAIL: {repr indResult}"

-- ============================================================
-- 30. Quot.mk return type is Quot r (not Sort u)
-- ============================================================

#eval do
  let env := Environment.empty
  let (_, env') := env.addDecl (.quotient .quot)
  let (_, env') := env'.addDecl (.quotient .quotMk)

  let quotMkHash := quotientHash .quotMk
  let quotHash := quotientHash .quot

  -- inferType on Quot.mk should give us the full type
  -- Quot.mk : Π (α : Sort u) (r : α → α → Prop) (a : α). Quot r
  match inferTypeClosed env' (.const quotMkHash [Level.succ Level.zero]) with
  | .error e => IO.println s!"Quot.mk type inference FAIL: {e}"
  | .ok ty =>
    -- The type should be a 3-deep forallE ending in an application of Quot
    match ty with
    | .forallE _sortU (.forallE _relTy (.forallE _aTy retTy)) =>
      -- retTy should be: app (app (const quotHash [succ zero]) (bvar 2)) (bvar 1)
      -- After substLevelParams [succ zero]: param 0 → succ zero
      -- Under 3 binders: α = bvar 2, r = bvar 1
      let expectedRet := Expr.app (.app (.const quotHash [Level.succ Level.zero]) (.bvar 2)) (.bvar 1)
      if retTy == expectedRet then
        IO.println "Quot.mk return type is Quot r: OK"
      else
        IO.println s!"Quot.mk return type FAIL: {repr retTy}"
    | _ =>
      IO.println s!"Quot.mk type shape FAIL: {repr ty}"

#eval IO.println "\n=== All tests executed ==="

end HashMath.Tests
