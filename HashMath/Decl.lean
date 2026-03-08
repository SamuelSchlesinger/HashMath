/-
  HashMath.Decl — Declaration types for HashMath CIC
-/

import HashMath.Expr

namespace HashMath

/-- A single inductive type within a mutual block. -/
structure InductiveType where
  type : Expr
  ctors : List Expr  -- each constructor's type
  deriving Repr, BEq

/-- A mutual inductive block. -/
structure InductiveBlock where
  numUnivParams : Nat
  numParams : Nat
  types : List InductiveType
  isUnsafe : Bool := false
  deriving Repr, BEq

/-- The four quotient constants. -/
inductive QuotKind where
  | quot      -- Quot : {α : Sort u} → (α → α → Prop) → Sort u
  | quotMk    -- Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r
  | quotLift  -- Quot.lift : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} →
               --   (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
  | quotInd   -- Quot.ind : {α : Sort u} → {r : α → α → Prop} → {β : Quot r → Prop} →
               --   (∀ a, β (Quot.mk r a)) → ∀ q, β q
  deriving Repr, BEq

/-- A declaration in HashMath CIC. -/
inductive Decl where
  | axiom      (numUnivParams : Nat) (type : Expr)
  | definition (numUnivParams : Nat) (type : Expr) (value : Expr)
  | inductive  (block : InductiveBlock)
  | quotient   (kind : QuotKind)
  deriving Repr, BEq

namespace Decl

def numUnivParams : Decl → Nat
  | .axiom n _ => n
  | .definition n _ _ => n
  | .inductive block => block.numUnivParams
  | .quotient kind =>
    match kind with
    | .quot => 1
    | .quotMk => 1
    | .quotLift => 2
    | .quotInd => 1

def type? : Decl → Option Expr
  | .axiom _ ty => some ty
  | .definition _ ty _ => some ty
  | .inductive _ => none  -- type comes from the block, need index
  | .quotient _ => none   -- fixed known types

end Decl

/-- Information about a constructor derived from an inductive block. -/
structure ConstructorInfo where
  indHash : Hash
  blkIdx : Nat        -- which type in the mutual block
  cIdx : Nat          -- which constructor of that type
  nParams : Nat
  nFields : Nat
  recursiveFields : List (Nat × Nat)  -- (fieldIdx, targetTypeIdx) pairs for recursive fields
  ty : Expr
  deriving Repr

/-- Information about a recursor derived from an inductive block. -/
structure RecursorInfo where
  indHash : Hash
  blockHash : Hash      -- hash of the inductive block (for computing mutual rec hashes)
  blkIdx : Nat
  nParams : Nat
  nMotives : Nat         -- = number of types in the mutual block
  nMinors : Nat          -- = total constructors across ALL types in the block
  nIndices : Nat         -- = indices for THIS type
  recTy : Expr
  allowsLargeElim : Bool := true  -- default to true for backward compat
  deriving Repr

end HashMath
