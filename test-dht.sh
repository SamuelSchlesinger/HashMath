#!/usr/bin/env bash
# Integration test: two DHT nodes, publish on one, fetch from the other.
#
# Usage: ./test-dht.sh
# Requires: hm (cd lean && lake build hm) and hm-net (cd hm-net && cargo build) already built.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_DIR="$SCRIPT_DIR/lean"
HM="$LEAN_DIR/.lake/build/bin/hm"
HM_NET="$SCRIPT_DIR/hm-net/target/debug/hm-net"

if [ ! -f "$HM" ]; then
  echo "ERROR: hm not built. Run: cd lean && lake build hm"
  exit 1
fi
if [ ! -f "$HM_NET" ]; then
  echo "ERROR: hm-net not built. Run: cd hm-net && cargo build"
  exit 1
fi

export HM_NET_PATH="$HM_NET"

TMPDIR=$(mktemp -d)
NODE_A_PID=""
NODE_B_PID=""
cleanup() {
  rm -rf "$TMPDIR"
  [ -n "$NODE_A_PID" ] && kill "$NODE_A_PID" 2>/dev/null || true
  [ -n "$NODE_B_PID" ] && kill "$NODE_B_PID" 2>/dev/null || true
}
trap cleanup EXIT

FIFO_A_IN="$TMPDIR/a_in"
FIFO_B_IN="$TMPDIR/b_in"
mkfifo "$FIFO_A_IN" "$FIFO_B_IN"

FAILED=0
pass() { echo "  PASS: $1"; }
fail() { echo "  FAIL: $1"; FAILED=1; }

# ─── Test 1: IPC ping/pong ───────────────────────────────────────
echo "=== Test 1: IPC ping/pong ==="
"$HM" --test-ipc 2>/dev/null
echo ""

# ─── Test 2: Two-node publish & fetch ────────────────────────────
echo "=== Test 2: Two-node DHT propagation ==="

# Start node A on port 4260
# Redirect stderr to a file so we can parse the peer ID
echo "Starting node A (port 4260)..."
"$HM_NET" --ephemeral --listen /ip4/127.0.0.1/tcp/4260 < "$FIFO_A_IN" > "$TMPDIR/a_out" 2>"$TMPDIR/a_err" &
NODE_A_PID=$!

# Keep the fifo open for writing (otherwise node A gets EOF immediately)
exec 3>"$FIFO_A_IN"

# Wait for node A to print its peer ID
for i in $(seq 1 20); do
  if grep -q "PEER_ID=" "$TMPDIR/a_err" 2>/dev/null; then
    break
  fi
  sleep 0.25
done

PEER_ID_A=$(grep "PEER_ID=" "$TMPDIR/a_err" | head -1 | sed 's/PEER_ID=//')
if [ -z "$PEER_ID_A" ]; then
  fail "could not get node A peer ID"
  cat "$TMPDIR/a_err"
  exit 1
fi
echo "  Node A peer ID: $PEER_ID_A"

# Start node B on port 4261, bootstrapped from node A
echo "Starting node B (port 4261, bootstrap from A)..."
"$HM_NET" --ephemeral --listen /ip4/127.0.0.1/tcp/4261 \
  --bootstrap "/ip4/127.0.0.1/tcp/4260/p2p/$PEER_ID_A" \
  < "$FIFO_B_IN" > "$TMPDIR/b_out" 2>"$TMPDIR/b_err" &
NODE_B_PID=$!
exec 4>"$FIFO_B_IN"

# Wait for node B to start
for i in $(seq 1 20); do
  if grep -q "PEER_ID=" "$TMPDIR/b_err" 2>/dev/null; then
    break
  fi
  sleep 0.25
done

PEER_ID_B=$(grep "PEER_ID=" "$TMPDIR/b_err" | head -1 | sed 's/PEER_ID=//')
if [ -z "$PEER_ID_B" ]; then
  fail "could not get node B peer ID"
  cat "$TMPDIR/b_err"
  exit 1
fi
echo "  Node B peer ID: $PEER_ID_B"

# Give nodes time to discover each other
sleep 2

# --- Publish a record to node A via IPC ---
# We'll write raw IPC frames to node A's stdin.
# Format: [4-byte BE length][0x51 PUBLISH][32-byte hash][LEB128 len][data]
#
# Use a small python script to generate the binary IPC message.
echo "Publishing test record to node A..."
python3 -c "
import sys, struct

# Build a PUBLISH request: tag=0x51, hash=32 zero bytes, data=b'hello hashmath'
data = b'hello hashmath'
hash_bytes = b'\\x42' * 32  # test hash

# LEB128 encode
def leb128(n):
    out = bytearray()
    while True:
        byte = n & 0x7f
        n >>= 7
        if n:
            byte |= 0x80
        out.append(byte)
        if not n:
            break
    return bytes(out)

payload = bytes([0x51]) + hash_bytes + leb128(len(data)) + data
frame = struct.pack('>I', len(payload)) + payload
sys.stdout.buffer.write(frame)
sys.stdout.buffer.flush()
" >&3

# Read the response from node A
sleep 1
if [ -s "$TMPDIR/a_out" ]; then
  # Response is [4-byte BE length][tag][...], tag is byte 5 (index 4)
  RESP_TAG=$(xxd -p -s 4 -l 1 "$TMPDIR/a_out")
  if [ "$RESP_TAG" = "61" ]; then
    pass "node A accepted publish (tag=0x61)"
  else
    fail "unexpected response tag from node A: $RESP_TAG (full: $(xxd -p -l 10 "$TMPDIR/a_out"))"
  fi
else
  fail "no response from node A"
fi

# Give DHT time to propagate
sleep 2

# --- Fetch the same record from node B via IPC ---
echo "Fetching test record from node B..."
python3 -c "
import sys, struct

# Build a FETCH request: tag=0x52, hash=32 x 0x42 bytes (same as published)
hash_bytes = b'\\x42' * 32
payload = bytes([0x52]) + hash_bytes
frame = struct.pack('>I', len(payload)) + payload
sys.stdout.buffer.write(frame)
sys.stdout.buffer.flush()
" >&4

# Wait for response
sleep 3
if [ -s "$TMPDIR/b_out" ]; then
  # Response is [4-byte BE length][tag][...], tag is byte 5 (index 4)
  RESP_TAG=$(xxd -p -s 4 -l 1 "$TMPDIR/b_out")
  if [ "$RESP_TAG" = "62" ]; then
    pass "node B found the record (tag=0x62) — DHT propagation works!"
  elif [ "$RESP_TAG" = "63" ]; then
    fail "node B returned NotFound (tag=0x63) — record did not propagate"
  else
    fail "unexpected response tag from node B: $RESP_TAG (full: $(xxd -p -l 10 "$TMPDIR/b_out"))"
  fi
else
  fail "no response from node B"
fi

# Clean up
exec 3>&-
exec 4>&-

echo ""
echo "=== Summary ==="
if [ $FAILED -eq 0 ]; then
  echo "All tests passed."
else
  echo "Some tests FAILED."
  echo "Node A stderr:"
  cat "$TMPDIR/a_err"
  echo ""
  echo "Node B stderr:"
  cat "$TMPDIR/b_err"
  exit 1
fi
