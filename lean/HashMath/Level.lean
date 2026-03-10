/-
  HashMath.Level — Universe levels for HashMath CIC
-/

import HashMath.Basic

namespace HashMath

/-- Universe levels with 5 constructors.
    `param` uses de Bruijn index instead of a name. -/
inductive Level where
  | zero : Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  | param : Nat → Level
  deriving Repr, BEq, Inhabited

namespace Level

/-- Substitute universe parameters. `subst ls l` replaces `param i` with `ls[i]`. -/
def substParams (ls : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (substParams ls l)
  | .max l₁ l₂ => .max (substParams ls l₁) (substParams ls l₂)
  | .imax l₁ l₂ => .imax (substParams ls l₁) (substParams ls l₂)
  | .param n => ls.getD n (.param n)

/-- Build a level from a natural number: `nSucc n = succ^n(zero)`. -/
def nSucc : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (nSucc n)

/-- Check if a level has no free universe parameters. -/
def isClosed : Level → Bool
  | .zero => true
  | .succ l => isClosed l
  | .max l₁ l₂ => isClosed l₁ && isClosed l₂
  | .imax l₁ l₂ => isClosed l₁ && isClosed l₂
  | .param _ => false

/-- Evaluate a closed level to a natural number. -/
def toNat : Level → Option Nat
  | .zero => some 0
  | .succ l => l.toNat.map (· + 1)
  | .max l₁ l₂ => do
    let n₁ ← l₁.toNat
    let n₂ ← l₂.toNat
    return Nat.max n₁ n₂
  | .imax l₁ l₂ => do
    let n₁ ← l₁.toNat
    let n₂ ← l₂.toNat
    if n₂ = 0 then return 0
    else return Nat.max n₁ n₂
  | .param _ => none

/-- Normalize `max l₁ l₂`, simplifying trivial cases. -/
private def mkMaxNorm (l₁ l₂ : Level) : Level :=
  if l₁ == l₂ then l₁
  else match l₁, l₂ with
  | .zero, _ => l₂
  | _, .zero => l₁
  | .succ a, .succ b => .succ (mkMaxNorm a b)
  | _, _ => match l₁.toNat, l₂.toNat with
    | some a, some b => nSucc (Nat.max a b)
    | _, _ => .max l₁ l₂

/-- Normalize a level to a canonical form.
    `imax u 0 = 0` and `imax u (succ v) = max u (succ v)`.
    `max l l = l`, `max 0 l = l`, `max l 0 = l`, and
    `max (succ^a zero) (succ^b zero) = succ^(max a b) zero`. -/
def normalize : Level → Level
  | .zero => .zero
  | .succ l => .succ (normalize l)
  | .max l₁ l₂ => mkMaxNorm (normalize l₁) (normalize l₂)
  | .imax l₁ l₂ =>
    match normalize l₂ with
    | .zero => .zero
    | .succ l₂' => mkMaxNorm (normalize l₁) (.succ l₂')
    | l₂' => .imax (normalize l₁) l₂'
  | .param n => .param n

/-- Check `l₁ ≤ l₂` for universe levels, including symbolic params.
    Returns `some true` if provably ≤, `some false` if provably >,
    `none` if indeterminate. Handles:
    - `zero ≤ x` (always true)
    - `succ a ≤ succ b` iff `a ≤ b`
    - `a ≤ succ b` if `a ≤ b` (monotonicity)
    - `a ≤ max b₁ b₂` if `a ≤ b₁` or `a ≤ b₂`
    - `max a₁ a₂ ≤ b` if `a₁ ≤ b` and `a₂ ≤ b` -/
partial def leq (l₁ l₂ : Level) : Option Bool :=
  leqCore l₁.normalize l₂.normalize
where
  leqCore (a b : Level) : Option Bool :=
    if a == b then some true
    else match a with
    | .zero => some true
    | .max a₁ a₂ =>
      -- max a₁ a₂ ≤ b iff a₁ ≤ b and a₂ ≤ b
      match leqCore a₁ b, leqCore a₂ b with
      | some true, some true => some true
      | some false, _ => some false
      | _, some false => some false
      | _, _ => none
    | .imax ia ib =>
      -- imax ia ib = 0 when ib=0, max ia ib when ib>0
      match ib.toNat with
      | some 0 => some true  -- imax ia 0 = 0 ≤ anything
      | some _ => leqCore (mkMaxNorm ia ib) b  -- ib definitely positive
      | none =>
        -- Conservative: max ia ib ≤ b iff ia ≤ b ∧ ib ≤ b
        match leqCore ia b, leqCore ib b with
        | some true, some true => some true
        | some false, _ => some false
        | _, some false => some false
        | _, _ => none
    | _ =>  -- a is succ or param
      match b with
      | .succ b' =>
        -- a ≤ b' implies a ≤ succ b'  (monotonicity)
        match leqCore a b' with
        | some true => some true
        | _ =>
          -- succ a' ≤ succ b' iff a' ≤ b'
          match a with
          | .succ a' => leqCore a' b'
          | _ => none
      | .max b₁ b₂ =>
        -- a ≤ max b₁ b₂ if a ≤ b₁ or a ≤ b₂
        match leqCore a b₁ with
        | some true => some true
        | _ => leqCore a b₂
      | .imax ib1 ib2 =>
        match ib2.toNat with
        | some 0 => leqCore a .zero  -- imax ib1 0 = 0
        | some _ => leqCore a (mkMaxNorm ib1 ib2)  -- definitely positive
        | none => none  -- conservative: can't determine
      | _ =>
        match a.toNat, b.toNat with
        | some n₁, some n₂ => some (n₁ ≤ n₂)
        | _, _ => none

/-- Structural equality of levels (syntactic, after normalization). -/
def beqNorm (l₁ l₂ : Level) : Bool :=
  l₁.normalize == l₂.normalize

end Level

end HashMath
