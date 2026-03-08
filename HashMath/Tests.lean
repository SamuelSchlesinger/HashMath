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

#eval IO.println "\n=== All tests executed ==="

end HashMath.Tests
