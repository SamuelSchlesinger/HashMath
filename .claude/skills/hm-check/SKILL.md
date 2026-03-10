---
name: hm-check
description: Type-check HashMath (.hm) source code or files. Use when the user wants to verify that .hm code type-checks correctly.
user-invocable: true
allowed-tools: mcp__hm-mcp__hm_process, mcp__hm-mcp__hm_load_file, mcp__hm-mcp__hm_check, mcp__hm-mcp__hm_env, mcp__hm-mcp__hm_reset, Read, Glob
argument-hint: [source code or file path]
---

# Type-check HashMath Code

You are helping the user type-check HashMath (.hm) source code.

## Instructions

1. First, call `hm_reset` to start with a clean environment.

2. If the argument looks like a file path (ends in `.hm`), use `hm_load_file` with the path.
   Otherwise, treat the argument as inline source code and use `hm_process`.

3. If the code uses standard library types (Nat, List, Bool, Eq, etc.), load the stdlib first:
   ```
   hm_load_file with path: "<project_root>/lean/stdlib/Prelude.hm"
   ```
   where `<project_root>` is the HashMath project root directory.

4. Report the results clearly:
   - For each successfully declared name, show it with a checkmark
   - For type errors, show the full error message
   - For `#check` results, show the inferred type
   - For `#eval` results, show the normalized value

5. If there are errors, suggest fixes based on common issues:
   - Universe parameter mismatches (e.g., `Nat.rec.{1}` not `Nat.rec.{1,1}`)
   - Missing imports
   - Positivity violations in inductive types
   - Type mismatches in definitions

## Argument: $ARGUMENTS
