---
name: hm-test
description: Run the HashMath test suite. Use when the user wants to run tests, check if examples pass, or verify the type checker.
user-invocable: true
allowed-tools: Bash(cd /Users/samuelschlesinger/projects/formalization/HashMath/lean && bash test.sh:*), Bash(cd /Users/samuelschlesinger/projects/formalization/HashMath/lean && lake build hm:*), Read
argument-hint: [optional: "build" to rebuild first]
---

# Run HashMath Tests

Run the HashMath type-checker test suite.

## Instructions

1. If the argument includes "build", first rebuild the `hm` binary:
   ```
   cd /Users/samuelschlesinger/projects/formalization/HashMath/lean && lake build hm
   ```

2. Run the test suite:
   ```
   cd /Users/samuelschlesinger/projects/formalization/HashMath/lean && bash test.sh
   ```

3. Report results:
   - How many examples/ files passed (should all pass)
   - How many wrong/ files were correctly rejected (should all be rejected)
   - Any unexpected failures or passes

## Argument: $ARGUMENTS
