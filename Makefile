# HashMath — build, test, and install
#
# Usage:
#   make            Build both hm and hm-net
#   make install    Install to PREFIX/bin (default: ~/.local)
#   make test       Run the type-checker test suite
#   make test-dht   Run the DHT integration test
#   make clean      Remove build artifacts
#   make uninstall  Remove installed binaries

PREFIX ?= $(HOME)/.local

# Derived paths
BINDIR     := $(PREFIX)/bin
HM_BIN     := lean/.lake/build/bin/hm
HM_NET_BIN := hm-net/target/release/hm-net

.PHONY: all build install uninstall test test-dht clean check-deps

all: build

# ── Prerequisites ────────────────────────────────────────────────

check-deps:
	@command -v lake >/dev/null 2>&1 || \
		{ echo "Error: 'lake' not found. Install Lean 4: https://leanprover.github.io/lean4/doc/setup.html"; exit 1; }
	@command -v cargo >/dev/null 2>&1 || \
		{ echo "Error: 'cargo' not found. Install Rust: https://rustup.rs/"; exit 1; }

# ── Build ────────────────────────────────────────────────────────

build: check-deps build-hm build-hm-net

build-hm:
	cd lean && lake build hm

build-hm-net:
	cd hm-net && cargo build --release

# ── Install ──────────────────────────────────────────────────────

install: build
	@mkdir -p $(BINDIR)
	cp $(HM_BIN) $(BINDIR)/hm
	cp $(HM_NET_BIN) $(BINDIR)/hm-net
	@echo ""
	@echo "Installed hm and hm-net to $(BINDIR)."
	@echo "Make sure $(BINDIR) is on your PATH."

uninstall:
	rm -f $(BINDIR)/hm $(BINDIR)/hm-net
	@echo "Removed hm and hm-net from $(BINDIR)."

# ── Test ─────────────────────────────────────────────────────────

test: build-hm
	cd lean && bash test.sh

test-dht: build
	bash test-dht.sh

# ── Clean ────────────────────────────────────────────────────────

clean:
	cd lean && lake clean
	cd hm-net && cargo clean
