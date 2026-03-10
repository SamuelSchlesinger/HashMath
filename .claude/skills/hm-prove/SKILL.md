---
name: hm-prove
description: Help prove a theorem in HashMath. Use when the user wants to construct a proof term, define a theorem, or needs help writing .hm proof code.
user-invocable: true
allowed-tools: mcp__hm-mcp__hm_process, mcp__hm-mcp__hm_load_file, mcp__hm-mcp__hm_check, mcp__hm-mcp__hm_eval, mcp__hm-mcp__hm_print, mcp__hm-mcp__hm_env, mcp__hm-mcp__hm_reset, mcp__hm-mcp__hm_read_source, Read, Glob
argument-hint: <theorem statement or description>
---

# Prove a Theorem in HashMath

You are helping the user prove a theorem in the HashMath proof assistant.

## Key Facts About HashMath

HashMath is a Calculus of Inductive Constructions (CIC) kernel. There are NO tactics —
all proofs are explicit proof terms (lambda calculus + recursors).

### Proof Techniques
- **Recursor elimination**: The primary proof method. Each inductive type `T` has `T.rec`.
  Example: `Nat.rec.{1} (fun (_ : Nat) => Nat) base_case step_case n`
- **Eq.rec**: For equality proofs. `Eq.rec.{1} A a (fun (x : A) (_ : Eq A a x) => P x) base_proof b eq_proof`
- **Large elimination**: Some Prop types allow computing Type-valued results (Eq, And, etc.)
- **Definitional reduction**: `#eval` normalizes; use it to check computational behavior

### Universe Gotchas
- Non-large-elim types (Or, Exists): recursor has **0** universe params
- Large-elim types (And, False, Eq, Nat, Bool, List): recursor has **1** universe param
- When motive returns `Prop`, use `.{1}` not `.{0}` (since `Prop : Sort 1`)
- `Nat.add` recurses on **second** arg: `add (succ X) Y ≠ succ (add X Y)` definitionally

### Standard Library
Located in `lean/stdlib/`. Key modules: Logic.hm, Equality.hm, Nat.hm, List.hm, Bool.hm, Prod.hm, Sum.hm, Option.hm, Unit.hm

## Workflow

1. Call `hm_reset` to start clean.
2. Load the stdlib: `hm_load_file` with the project's `lean/stdlib/Prelude.hm`.
3. If the user provides context declarations, process them with `hm_process`.
4. Read relevant stdlib files with `hm_read_source` to understand available lemmas.
5. Construct the proof term step by step:
   a. State the theorem type
   b. Build the proof term using recursors and lambda abstractions
   c. Test with `hm_process` to check if it type-checks
   d. If it fails, analyze the error and adjust
6. Use `hm_eval` to test computational behavior of terms.

## Important: Iterate

If the proof doesn't type-check on the first try, that's expected. Read the error
message carefully, adjust the proof term, and try again. Common issues:
- Wrong number of universe arguments to a recursor
- Motive doesn't match the expected type
- Missing arguments to constructors
- De Bruijn index confusion in nested binders

## Argument: $ARGUMENTS
