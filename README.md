# HashMath

**A content-addressed Calculus of Inductive Constructions for permissionless formal mathematics.**

> **Note:** This project is a work in progress and under active construction. The design and implementation may change significantly.

## What is this?

Mathematical proofs, when formalized in a computer, are currently organized
like library books: every theorem gets a human-chosen name, lives in a specific
library, and can only be found if you know where to look. Different communities
pick different names for the same thing, and contributing a new result requires
navigating review processes, naming conventions, and import hierarchies.

HashMath takes a different approach. Instead of naming theorems, we *hash*
them. Every definition, theorem, and proof is identified by a cryptographic
fingerprint (SHA-256) of its actual content. Two people who independently prove
the same theorem produce the same hash — automatically, without coordination.
Dependencies between results are tracked by hash, not by name.

The result is a global, append-only knowledge base where:

- **Correctness is guaranteed** — every entry is mechanically type-checked before it's accepted, and after it's retrieved.
- **Names are optional** — they're useful metadata, not identity.
- **No coordination is required** — anyone (human or AI) can contribute, and duplicates are free.
- **Discovery is by type** — you can search for all proofs of a given statement by its type signature.

## Why does this matter?

Formalized mathematics is at an inflection point. AI systems can now generate
thousands of correct proofs per hour, but the infrastructure for *storing and
sharing* those proofs hasn't kept up. Today's proof libraries (Lean's Mathlib,
Rocq's standard library) are curated by small teams who review contributions,
enforce naming conventions, and maintain coherence. This works well at human
scale, but becomes a bottleneck when AI enters the picture.

HashMath removes the bottleneck. A thousand AI agents and a hundred
mathematicians can contribute simultaneously, building on each other's work by
hash, without a single naming conflict. The vision is closer to how Git and
content-addressable storage work in software than to how traditional libraries
organize books.

## How it works

HashMath implements a variant of the **Calculus of Inductive Constructions**
(CIC) — the same type theory that underlies Lean 4 and Rocq (formerly Coq). The
key differences are:

1. **No names in the kernel.** Binder names, module paths, and human-readable
   identifiers are stripped. Terms use de Bruijn indices for bound variables
   and SHA-256 hashes for references to other declarations.

2. **Merkle-tree hashing.** Every term's hash is computed recursively from its
   structure: `H(app(f, a)) = SHA256(0x13 || H(f) || H(a))`. This creates a
   Merkle DAG where each hash transitively encodes the entire dependency tree
   down to the axioms.

3. **Full transparency.** All definitions are always unfolded during type
   checking — there is no opacity mechanism. This simplifies the kernel and
   ensures that definitional equality is purely structural.

4. **Inductive types with derived entities.** Inductive type declarations (like
   `Nat` or `List`) generate derived hashes for each constructor and recursor,
   all deterministically computed from the block hash.

## What's implemented

The reference implementation is written in Lean 4 with no external dependencies
(no Mathlib). It includes:

| Module | Purpose |
|--------|---------|
| `Basic` | 32-byte hash type, LEB128 encoding |
| `Level` | Universe levels (zero, succ, max, imax, param) |
| `Expr` | 9 expression constructors with de Bruijn indices |
| `Decl` | Declaration types (axiom, definition, inductive, quotient) |
| `Serialize` | Binary serialization with domain-separating tags |
| `SHA256` | Pure Lean SHA-256 (FIPS 180-4), verified against NIST test vectors |
| `Hash` | Merkle-tree hashing for all CIC terms |
| `Quotient` | Built-in quotient types (Quot, Quot.mk, Quot.lift, Quot.ind) |
| `Environment` | HashMap-based environment with auto-registration of derived entities |
| `Reduce` | Weak-head normal form (beta, delta, iota, zeta, projection, quotient reduction) |
| `Inductive` | Positivity checking, universe constraints, recursor generation |
| `DefEq` | Mutual type inference, definitional equality, subtype checking, structural eta |
| `TypeChecker` | Top-level declaration checking |
| `Tests` | 30 test groups covering all features |

## The trust model

The system's correctness rests on a small trusted computing base:

1. The CIC type checker is correct.
2. The SHA-256 implementation is correct.
3. The serialization format faithfully represents terms.

Everything above the kernel — elaboration, name registries, search, UI — is
untrusted. A buggy pretty printer can't make an ill-typed term appear valid. A
malicious name registry can't alter what a hash points to. The cryptographic
hash pins the content.

## Further reading

The full technical specification is in the [whitepaper](whitepaper.pdf).
