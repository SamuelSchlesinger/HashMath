---
name: hm-search
description: Search for declarations in the HashMath environment by name pattern. Use when the user wants to find available definitions, theorems, or types.
user-invocable: true
allowed-tools: mcp__hm-mcp__hm_load_file, mcp__hm-mcp__hm_env, mcp__hm-mcp__hm_check, mcp__hm-mcp__hm_print, mcp__hm-mcp__hm_reset, mcp__hm-mcp__hm_read_source, Read
argument-hint: <search pattern>
---

# Search HashMath Declarations

Search for declarations in the HashMath environment.

## Instructions

1. Call `hm_reset` then load the stdlib:
   `hm_load_file` with the project's `lean/stdlib/Prelude.hm`

2. Use `hm_env` with the user's search pattern to find matching names.

3. For each interesting match, use `hm_check` to show its type.

4. If the user wants more detail about a specific declaration, use `hm_print`.

5. If they want to see the source definition, use `hm_read_source` on the
   relevant stdlib file.

## Standard Library Modules
- `Logic.hm` — True, False, And, Or, Not, Exists, Iff
- `Equality.hm` — Eq, Eq.symm, Eq.trans, Eq.congr, Eq.subst
- `Bool.hm` — Bool, and/or/not/ite/xor
- `Unit.hm` — Unit, Empty, Empty.elim
- `Prod.hm` — Prod, fst/snd/map/swap
- `Sum.hm` — Sum, elim/map/swap
- `Option.hm` — Option, map/bind/getD/isSome
- `Nat.hm` — Nat, add/mul/pred, arithmetic lemmas
- `List.hm` — List, length/append/map/filter/foldr/reverse
- `Prelude.hm` — imports all of the above

## Argument: $ARGUMENTS
