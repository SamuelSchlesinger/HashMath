#!/bin/bash
# HashMath test runner
# Runs all examples/ (should pass) and wrong/ (should fail) files
# Reports any unexpected outcomes

set -euo pipefail

HM=".lake/build/bin/hm"
PASS=0
FAIL=0
ERRORS=""

echo "=== Correct examples (should all pass) ==="
for f in examples/*.hm; do
  name=$(basename "$f")
  output=$("$HM" "$f" 2>&1) && status=0 || status=1
  if [ $status -eq 0 ] && ! echo "$output" | grep -qi "error"; then
    echo "  PASS: $name"
    PASS=$((PASS + 1))
  else
    echo "  FAIL: $name"
    echo "    $output" | head -3
    FAIL=$((FAIL + 1))
    ERRORS="$ERRORS\n  UNEXPECTED FAIL: $name"
  fi
done

echo ""
echo "=== Wrong examples (should all be rejected) ==="
for f in wrong/*.hm; do
  name=$(basename "$f")
  output=$("$HM" "$f" 2>&1) && status=0 || status=1
  if echo "$output" | grep -qi "error"; then
    # Extract the specific error message
    errmsg=$(echo "$output" | grep -i "error" | head -1 | sed 's/.*error[^:]*: //')
    echo "  PASS: $name → $errmsg"
    PASS=$((PASS + 1))
  else
    echo "  FAIL: $name (should have been rejected)"
    echo "    $output" | head -3
    FAIL=$((FAIL + 1))
    ERRORS="$ERRORS\n  UNEXPECTED ACCEPT: $name"
  fi
done

echo ""
echo "=== Summary ==="
echo "  Passed: $PASS"
echo "  Failed: $FAIL"
if [ -n "$ERRORS" ]; then
  echo ""
  echo "Issues:"
  echo -e "$ERRORS"
fi

exit $FAIL
