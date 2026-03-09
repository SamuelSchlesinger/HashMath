/-
  HashMath.SubtermTests — Tests for subterm hash-consing (shatter/reassemble)

  Tests include:
  1. Round-trip: shatter then reassemble preserves the original expression
  2. Hash preservation: hashExpr of original == hash implied by shattered form
  3. Size threshold: small expressions are NOT shattered
  4. Deduplication: shared subterms produce shared store entries
  5. Serialization round-trip: serializeStoredExpr/deserializeStoredExpr
  6. Fuzz testing: random expression generation + round-trip verification
-/

import HashMath.Subterm
import HashMath.TypeChecker

namespace HashMath.SubtermTests

open HashMath

-- ============================================================
-- Helper: check round-trip shatter → reassemble = original
-- ============================================================

private def checkRoundTrip (name : String) (e : Expr) : IO Unit := do
  let (shattered, store) := shatter e
  match reassemble shattered store with
  | some recovered =>
    if recovered == e then
      IO.println s!"  roundtrip {name}: OK"
    else
      IO.println s!"  roundtrip {name}: FAIL (recovered ≠ original)"
  | none =>
    IO.println s!"  roundtrip {name}: FAIL (reassemble returned none)"

-- ============================================================
-- Helper: check that hashExpr is consistent through shatter
-- ============================================================

private def checkHashPreserved (name : String) (e : Expr) : IO Unit := do
  let originalHash := hashExpr e
  let (shattered, store) := shatter e
  match reassemble shattered store with
  | some recovered =>
    let recoveredHash := hashExpr recovered
    if originalHash == recoveredHash then
      IO.println s!"  hash preservation {name}: OK"
    else
      IO.println s!"  hash preservation {name}: FAIL"
  | none =>
    IO.println s!"  hash preservation {name}: FAIL (reassemble returned none)"

-- ============================================================
-- 1. Basic round-trip tests
-- ============================================================

#eval do
  IO.println "=== Subterm round-trip tests ==="

  -- Small expressions (should NOT be shattered, just embedded)
  checkRoundTrip "bvar" (.bvar 0)
  checkRoundTrip "sort" (.sort .zero)
  checkRoundTrip "sort succ" (.sort (.succ .zero))

  -- Medium expression
  let natSort : Expr := .sort (.succ .zero)
  checkRoundTrip "lam" (.lam natSort (.bvar 0))
  checkRoundTrip "forallE" (.forallE natSort natSort)
  checkRoundTrip "app" (.app (.lam natSort (.bvar 0)) natSort)

  -- Larger expressions that should trigger shatter
  let dummyHash := (hashExpr (.sort .zero))
  let big : Expr := .forallE
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.forallE (.sort (.succ .zero))
      (.app (.const dummyHash [.zero, .succ .zero]) (.bvar 0)))

  checkRoundTrip "big forallE" big

  -- Nested applications
  let nested : Expr := .app (.app (.app (.lam (.sort .zero) (.bvar 0))
    (.sort (.succ .zero))) (.sort (.succ (.succ .zero)))) (.sort .zero)
  checkRoundTrip "nested app" nested

  -- LetE
  let letExpr : Expr := .letE (.sort (.succ .zero)) (.sort .zero)
    (.forallE (.bvar 0) (.sort (.succ .zero)))
  checkRoundTrip "letE" letExpr

  -- Projection
  let projExpr : Expr := .proj dummyHash 2
    (.app (.const dummyHash [.zero]) (.sort .zero))
  checkRoundTrip "proj" projExpr

-- ============================================================
-- 2. Hash preservation tests
-- ============================================================

#eval do
  IO.println "=== Hash preservation tests ==="

  let natSort : Expr := .sort (.succ .zero)
  checkHashPreserved "sort" natSort
  checkHashPreserved "lam" (.lam natSort (.bvar 0))

  let dummyHash := hashExpr (.sort .zero)
  let big : Expr := .forallE
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.forallE (.sort (.succ .zero))
      (.app (.const dummyHash [.zero, .succ .zero]) (.bvar 0)))
  checkHashPreserved "big" big

  -- Deep nesting
  let deep : Expr := (List.range 20).foldl
    (fun acc _ => Expr.lam (.sort .zero) acc) (.bvar 0)
  checkHashPreserved "deep nesting" deep

-- ============================================================
-- 3. Size threshold tests
-- ============================================================

#eval do
  IO.println "=== Size threshold tests ==="

  -- Small expr: should NOT produce any store entries
  let small : Expr := .bvar 0
  let (shattered, store) := shatter small
  if store.isEmpty then
    IO.println "  small expr not shattered: OK"
  else
    IO.println s!"  small expr not shattered: FAIL (store has {store.size} entries)"

  -- Check that shattered small expr has no hrefs
  match shattered with
  | .bvar 0 => IO.println "  small expr identity: OK"
  | _ => IO.println "  small expr identity: FAIL"

  -- Sort is also small
  let (_, store2) := shatter (.sort .zero)
  if store2.isEmpty then
    IO.println "  sort not shattered: OK"
  else
    IO.println s!"  sort not shattered: FAIL"

  -- A large-enough expression SHOULD produce store entries
  let dummyHash := hashExpr (.sort .zero)
  let big : Expr := .forallE
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.forallE (.sort (.succ .zero))
      (.app (.const dummyHash [.zero, .succ .zero]) (.bvar 0)))
  let (_, store3) := shatter big
  if !store3.isEmpty then
    IO.println s!"  big expr shattered ({store3.size} entries): OK"
  else
    IO.println "  big expr shattered: FAIL (no store entries)"

-- ============================================================
-- 4. Deduplication test
-- ============================================================

#eval do
  IO.println "=== Deduplication tests ==="

  -- Build an expression with duplicated subterms
  let shared : Expr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  let dup : Expr := .app shared shared

  let (_, store) := shatter dup

  -- Both `shared` subterms should map to the same hash in the store
  -- The store should have fewer entries than if they were different
  let sharedHash := hashExpr shared
  match store[sharedHash]? with
  | some _ => IO.println "  shared subterm deduplication: OK"
  | none =>
    -- The shared subterm might be inlined if it's small
    if exprSerializedSize shared ≤ 33 then
      IO.println "  shared subterm too small to shatter (expected): OK"
    else
      IO.println "  shared subterm deduplication: FAIL"

  -- Larger shared subterms
  let dummyHash := hashExpr (.sort .zero)
  let bigShared : Expr := .forallE
    (.forallE (.const dummyHash [.zero]) (.sort (.succ .zero)))
    (.app (.const dummyHash [.succ .zero]) (.bvar 0))
  let bigDup : Expr := .app bigShared bigShared
  let (_, store2) := shatter bigDup
  let bigHash := hashExpr bigShared
  match store2[bigHash]? with
  | some _ => IO.println s!"  large shared dedup ({store2.size} entries): OK"
  | none => IO.println "  large shared dedup: FAIL"

-- ============================================================
-- 5. Stored expression serialization round-trip
-- ============================================================

#eval do
  IO.println "=== Stored expression serialization tests ==="

  let dummyHash := hashExpr (.sort .zero)

  -- Test serializeStoredExpr / deserializeStoredExpr round-trip
  let testCases : List (String × Expr Hash) := [
    ("bvar", .bvar 42),
    ("sort", .sort (.succ .zero)),
    ("const", .const dummyHash [.zero]),
    ("href", .href dummyHash),
    ("app href", .app (.href dummyHash) (.bvar 0)),
    ("lam with href body", .lam (.sort .zero) (.href dummyHash)),
    ("forallE", .forallE (.sort .zero) (.sort (.succ .zero))),
    ("letE", .letE (.sort .zero) (.bvar 0) (.bvar 1)),
    ("proj", .proj dummyHash 1 (.bvar 0)),
    ("iref", .iref 0 [.zero])
  ]

  for (name, expr) in testCases do
    let bytes := serializeStoredExpr expr
    match deserializeStoredExpr (DesCursor.ofData bytes) with
    | some (recovered, _) =>
      if recovered == expr then
        IO.println s!"  stored ser/deser {name}: OK"
      else
        IO.println s!"  stored ser/deser {name}: FAIL (mismatch)"
    | none =>
      IO.println s!"  stored ser/deser {name}: FAIL (deser returned none)"

-- ============================================================
-- 6. Fuzz testing: random expression generation + round-trip
-- ============================================================

/-- Simple linear congruential generator for deterministic pseudo-random numbers. -/
private def nextRand (seed : Nat) : Nat × Nat :=
  let next := (seed * 1103515245 + 12345) % (2^31)
  (next, next)

/-- Generate a random expression of bounded depth. -/
private def genExpr (seed : Nat) (depth : Nat) (dummyHash : Hash) : Expr × Nat :=
  match depth with
  | 0 =>
    let (r, seed) := nextRand seed
    match r % 3 with
    | 0 => (.bvar (r % 5), seed)
    | 1 => (.sort (if r % 2 == 0 then .zero else .succ .zero), seed)
    | _ => (.const dummyHash (if r % 2 == 0 then [] else [.zero]), seed)
  | depth' + 1 =>
    let (r, seed) := nextRand seed
    match r % 7 with
    | 0 => -- bvar
      (.bvar (r % 10), seed)
    | 1 => -- sort
      (.sort (if r % 2 == 0 then .zero else .succ .zero), seed)
    | 2 => -- app
      let (f, seed) := genExpr seed depth' dummyHash
      let (a, seed) := genExpr seed depth' dummyHash
      (.app f a, seed)
    | 3 => -- lam
      let (ty, seed) := genExpr seed depth' dummyHash
      let (body, seed) := genExpr seed depth' dummyHash
      (.lam ty body, seed)
    | 4 => -- forallE
      let (ty, seed) := genExpr seed depth' dummyHash
      let (body, seed) := genExpr seed depth' dummyHash
      (.forallE ty body, seed)
    | 5 => -- letE
      let (ty, seed) := genExpr seed depth' dummyHash
      let (val, seed) := genExpr seed depth' dummyHash
      let (body, seed) := genExpr seed depth' dummyHash
      (.letE ty val body, seed)
    | _ => -- const or proj
      let (r2, seed) := nextRand seed
      if r2 % 2 == 0 then
        (.const dummyHash [.zero, .succ .zero], seed)
      else
        let (s, seed) := genExpr seed depth' dummyHash
        (.proj dummyHash (r2 % 3) s, seed)

#eval do
  IO.println "=== Fuzz tests (random expressions) ==="

  let dummyHash := hashExpr (.sort .zero)
  let mut seed := 42
  let mut passed := 0
  let mut failed := 0
  let numTests := 200

  for i in List.range numTests do
    let depth := 2 + (i % 5)  -- depths 2-6
    let (expr, newSeed) := genExpr seed depth dummyHash
    seed := newSeed

    -- Test 1: round-trip
    let (shattered, store) := shatter expr
    match reassemble shattered store with
    | some recovered =>
      if recovered != expr then
        IO.println s!"  fuzz #{i}: round-trip FAIL (mismatch)"
        failed := failed + 1
      else
        -- Test 2: hash preservation
        let origHash := hashExpr expr
        let recHash := hashExpr recovered
        if origHash != recHash then
          IO.println s!"  fuzz #{i}: hash FAIL"
          failed := failed + 1
        else
          -- Test 3: stored expr serialization round-trip
          let storedBytes := serializeStoredExpr shattered
          match deserializeStoredExpr (DesCursor.ofData storedBytes) with
          | some (desShattered, _) =>
            if desShattered != shattered then
              IO.println s!"  fuzz #{i}: stored ser/deser FAIL"
              failed := failed + 1
            else
              -- Test 4: reassemble from deserialized stored expr
              match reassemble desShattered store with
              | some recovered2 =>
                if recovered2 != expr then
                  IO.println s!"  fuzz #{i}: deser-reassemble FAIL"
                  failed := failed + 1
                else
                  passed := passed + 1
              | none =>
                IO.println s!"  fuzz #{i}: deser-reassemble returned none"
                failed := failed + 1
          | none =>
            IO.println s!"  fuzz #{i}: stored deser returned none"
            failed := failed + 1
    | none =>
      IO.println s!"  fuzz #{i}: reassemble returned none"
      failed := failed + 1

  IO.println s!"  fuzz results: {passed}/{numTests} passed, {failed} failed"
  if failed > 0 then
    IO.println "  FUZZ TESTS FAILED"
  else
    IO.println "  All fuzz tests passed!"

-- ============================================================
-- 7. Edge cases
-- ============================================================

#eval do
  IO.println "=== Edge case tests ==="

  -- Empty store reassemble of non-href expression
  let e : Expr Hash := .bvar 0
  match reassemble e {} with
  | some (.bvar 0) => IO.println "  reassemble no-href: OK"
  | _ => IO.println "  reassemble no-href: FAIL"

  -- Missing hash in store
  let dummyHash := hashExpr (.sort .zero)
  let badRef : Expr Hash := .href dummyHash
  match reassemble badRef {} with
  | none => IO.println "  missing hash detection: OK"
  | some _ => IO.println "  missing hash detection: FAIL (should have been none)"

  -- Double shatter (shatter an already-shattered-and-reassembled expression)
  let big : Expr := .forallE
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.forallE (.sort (.succ .zero))
      (.app (.const dummyHash [.zero, .succ .zero]) (.bvar 0)))
  let (s1, store1) := shatter big
  match reassemble s1 store1 with
  | some recovered1 =>
    let (s2, store2) := shatter recovered1
    match reassemble s2 store2 with
    | some recovered2 =>
      if recovered2 == big then
        IO.println "  double shatter round-trip: OK"
      else
        IO.println "  double shatter round-trip: FAIL"
    | none => IO.println "  double shatter reassemble: FAIL"
  | none => IO.println "  first reassemble: FAIL"

  -- Very deep expression
  let deep : Expr := (List.range 50).foldl
    (fun acc _ => Expr.lam (.sort .zero) acc) (.bvar 0)
  checkRoundTrip "very deep (50 lambdas)" deep
  checkHashPreserved "very deep (50 lambdas)" deep

  -- Wide expression (many args)
  let wide : Expr := (List.range 30).foldl
    (fun acc _ => Expr.app acc (.sort .zero)) (.const dummyHash [])
  checkRoundTrip "wide (30 apps)" wide
  checkHashPreserved "wide (30 apps)" wide

-- ============================================================
-- 8. Declaration-level shatter/reassemble (P2P integration)
-- ============================================================

private def checkDeclRoundTrip (name : String) (d : Decl) : IO Unit := do
  let originalHash := hashDecl d
  let (storedBytes, store) := shatterDecl d
  match reassembleStoredDecl storedBytes store with
  | some recovered =>
    let recoveredHash := hashDecl recovered
    if originalHash == recoveredHash then
      IO.println s!"  decl roundtrip {name}: OK (hash preserved)"
    else
      IO.println s!"  decl roundtrip {name}: FAIL (hash mismatch)"
  | none =>
    IO.println s!"  decl roundtrip {name}: FAIL (reassemble returned none)"

#eval do
  IO.println "=== Declaration-level shatter/reassemble tests ==="

  -- Axiom
  let axiomDecl : Decl := .axiom 0 (.sort (.succ .zero))
  checkDeclRoundTrip "simple axiom" axiomDecl

  -- Axiom with larger type
  let bigTy : Expr := .forallE (.sort (.succ .zero))
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
  let axiomDecl2 : Decl := .axiom 0 bigTy
  checkDeclRoundTrip "axiom with forallE" axiomDecl2

  -- Definition
  let idTy : Expr := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.bvar 1))
  let idVal : Expr := .lam (.sort (.succ .zero)) (.lam (.bvar 0) (.bvar 0))
  let defDecl : Decl := .definition 1 idTy idVal
  checkDeclRoundTrip "id definition" defDecl

  -- Quotient
  let quotDecl : Decl := .quotient .quot
  checkDeclRoundTrip "quotient" quotDecl

  -- Inductive (Nat-like)
  let natBlock : InductiveBlock := {
    numUnivParams := 0
    numParams := 0
    types := [{
      type := .sort (.succ .zero)
      ctors := [
        .iref 0 [],                        -- zero : Nat
        .forallE (.iref 0 []) (.iref 0 []) -- succ : Nat → Nat
      ]
    }]
  }
  checkDeclRoundTrip "Nat inductive" (.inductive natBlock)

  -- Inductive with params (List-like)
  let listBlock : InductiveBlock := {
    numUnivParams := 1
    numParams := 1
    types := [{
      type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
      ctors := [
        .forallE (.sort (.succ (.param 0))) (.iref 0 [.param 0]),
        .forallE (.sort (.succ (.param 0)))
          (.forallE (.bvar 0)
            (.forallE (.iref 0 [.param 0]) (.iref 0 [.param 0])))
      ]
    }]
  }
  checkDeclRoundTrip "List inductive" (.inductive listBlock)

-- ============================================================
-- 9. collectStoredDeclHRefs tests
-- ============================================================

#eval do
  IO.println "=== collectStoredDeclHRefs tests ==="

  -- Small declaration (no hrefs expected)
  let smallDecl : Decl := .axiom 0 (.sort .zero)
  let (storedBytes1, store1) := shatterDecl smallDecl
  let hrefs1 := collectStoredDeclHRefs storedBytes1
  if hrefs1.isEmpty == store1.isEmpty then
    IO.println "  small decl href collection: OK"
  else
    IO.println "  small decl href collection: FAIL"

  -- Big declaration (should have hrefs)
  let dummyHash := hashExpr (.sort .zero)
  let bigTy : Expr := .forallE
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.forallE (.sort (.succ .zero))
      (.app (.const dummyHash [.zero, .succ .zero]) (.bvar 0)))
  let bigDecl : Decl := .definition 0 bigTy bigTy
  let (storedBytes2, store2) := shatterDecl bigDecl
  let hrefs2 := collectStoredDeclHRefs storedBytes2
  -- Every href should correspond to a store entry
  let allFound := hrefs2.all (fun h => store2.contains h)
  if allFound then
    IO.println s!"  big decl href collection ({hrefs2.length} hrefs, all in store): OK"
  else
    IO.println "  big decl href collection: FAIL (some hrefs missing from store)"

  -- Verify: fetching with the collected hrefs is sufficient to reassemble
  let mut partialStore : SubtermStore := {}
  for h in hrefs2 do
    match store2[h]? with
    | some bs => partialStore := partialStore.insert h bs
    | none => pure ()
  match reassembleStoredDecl storedBytes2 partialStore with
  | some recovered =>
    if hashDecl recovered == hashDecl bigDecl then
      IO.println "  reassemble from collected hrefs: OK"
    else
      IO.println "  reassemble from collected hrefs: FAIL (hash mismatch)"
  | none =>
    IO.println "  reassemble from collected hrefs: FAIL (reassemble returned none)"

-- ============================================================
-- 10. Full P2P simulation: publish → fetch cycle
-- ============================================================

#eval do
  IO.println "=== P2P simulation tests ==="

  -- Simulate publish then fetch using an in-memory "DHT"
  let mut dht : Std.HashMap Hash ByteArray := {}

  -- Create and typecheck a small codebase
  let env := Environment.empty
  let axiomTy : Expr := .sort (.succ .zero)
  let axiomDecl : Decl := .axiom 0 axiomTy
  let (.ok (axiomHash, env)) := checkDecl env axiomDecl
    | do IO.println "  setup FAIL"; return

  -- "Publish": shatter and store in simulated DHT
  let (storedBytes, store) := shatterDecl axiomDecl
  -- Store subterms
  for (subHash, subBytes) in store.toList do
    dht := dht.insert subHash subBytes
  -- Store stored declaration
  dht := dht.insert axiomHash storedBytes

  -- "Fetch": retrieve and reassemble
  match dht[axiomHash]? with
  | none => IO.println "  P2P fetch: FAIL (not in DHT)"
  | some fetchedBytes =>
    let hrefHashes := collectStoredDeclHRefs fetchedBytes
    let mut fetchedStore : SubtermStore := {}
    for h in hrefHashes do
      match dht[h]? with
      | some bs => fetchedStore := fetchedStore.insert h bs
      | none => IO.println s!"  P2P fetch: FAIL (subterm missing)"
    match reassembleStoredDecl fetchedBytes fetchedStore with
    | none => IO.println "  P2P fetch: FAIL (reassemble failed)"
    | some recoveredDecl =>
      let recoveredHash := hashDecl recoveredDecl
      if recoveredHash != axiomHash then
        IO.println "  P2P fetch: FAIL (hash mismatch)"
      else
        -- Typecheck in a fresh environment
        match checkDecl Environment.empty recoveredDecl with
        | .ok _ => IO.println "  P2P simulation (publish → fetch → verify): OK"
        | .error e => IO.println s!"  P2P fetch: FAIL (typecheck: {e})"

  -- Larger test: definition with deps
  let defTy : Expr := .forallE (.const axiomHash []) (.const axiomHash [])
  let defVal : Expr := .lam (.const axiomHash []) (.bvar 0)
  let defDecl : Decl := .definition 0 defTy defVal
  let (.ok (defHash, _)) := checkDecl env defDecl
    | do IO.println "  setup FAIL"; return

  -- Publish definition
  let (storedDefBytes, defStore) := shatterDecl defDecl
  for (subHash, subBytes) in defStore.toList do
    dht := dht.insert subHash subBytes
  dht := dht.insert defHash storedDefBytes

  -- Fetch definition (needs axiom dep too)
  match dht[defHash]? with
  | none => IO.println "  P2P dep fetch: FAIL (not in DHT)"
  | some fetchedDefBytes =>
    let hrefHashes := collectStoredDeclHRefs fetchedDefBytes
    let mut fetchedStore : SubtermStore := {}
    for h in hrefHashes do
      match dht[h]? with
      | some bs => fetchedStore := fetchedStore.insert h bs
      | none => pure ()
    match reassembleStoredDecl fetchedDefBytes fetchedStore with
    | none => IO.println "  P2P dep fetch: FAIL (reassemble failed)"
    | some recoveredDef =>
      -- Verify hash
      if hashDecl recoveredDef != defHash then
        IO.println "  P2P dep fetch: FAIL (hash mismatch)"
      else
        -- Fetch dep (axiom) and typecheck
        let deps := recoveredDef.constHashes
        let mut fetchEnv := Environment.empty
        for dep in deps do
          match dht[dep]? with
          | some depBytes =>
            let depHRefs := collectStoredDeclHRefs depBytes
            let mut depStore : SubtermStore := {}
            for h in depHRefs do
              match dht[h]? with
              | some bs => depStore := depStore.insert h bs
              | none => pure ()
            match reassembleStoredDecl depBytes depStore with
            | some depDecl =>
              match checkDecl fetchEnv depDecl with
              | .ok (_, env') => fetchEnv := env'
              | .error _ => pure ()
            | none => pure ()
          | none => pure ()
        match checkDecl fetchEnv recoveredDef with
        | .ok _ => IO.println "  P2P simulation with deps (axiom → def): OK"
        | .error e => IO.println s!"  P2P dep fetch: FAIL (typecheck: {e})"

-- ============================================================
-- 11. Fuzz test: declaration-level shatter round-trip
-- ============================================================

#eval do
  IO.println "=== Decl-level fuzz tests ==="

  let dummyHash := hashExpr (.sort .zero)
  let mut seed := 777
  let mut passed := 0
  let mut failed := 0
  let numTests := 100

  for i in List.range numTests do
    let depth := 2 + (i % 4)
    let (ty, newSeed) := genExpr seed depth dummyHash
    let (val, newSeed2) := genExpr newSeed depth dummyHash
    seed := newSeed2

    -- Create axiom or definition based on parity
    let decl : Decl := if i % 2 == 0 then
      .axiom 0 ty
    else
      .definition 0 ty val

    let originalHash := hashDecl decl
    let (storedBytes, store) := shatterDecl decl

    -- Verify href collection is correct
    let hrefs := collectStoredDeclHRefs storedBytes
    let allInStore := hrefs.all (fun h => store.contains h)

    -- Reassemble and verify hash
    match reassembleStoredDecl storedBytes store with
    | some recovered =>
      let recoveredHash := hashDecl recovered
      if originalHash != recoveredHash then
        IO.println s!"  decl fuzz #{i}: hash mismatch"
        failed := failed + 1
      else if !allInStore then
        IO.println s!"  decl fuzz #{i}: hrefs not all in store"
        failed := failed + 1
      else
        passed := passed + 1
    | none =>
      IO.println s!"  decl fuzz #{i}: reassemble failed"
      failed := failed + 1

  IO.println s!"  decl fuzz results: {passed}/{numTests} passed, {failed} failed"
  if failed > 0 then
    IO.println "  DECL FUZZ TESTS FAILED"
  else
    IO.println "  All decl-level fuzz tests passed!"

#eval IO.println "=== All subterm tests executed ==="

end HashMath.SubtermTests
