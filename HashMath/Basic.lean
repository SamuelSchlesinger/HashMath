/-
  HashMath.Basic — Foundational types and utilities
-/

namespace HashMath

/-- A 256-bit hash value, stored as a ByteArray of length 32. -/
structure Hash where
  bytes : ByteArray
  hsize : bytes.size = 32
instance : BEq Hash where
  beq a b := a.bytes == b.bytes

instance : Hashable Hash where
  hash h := hash h.bytes

instance : Repr Hash where
  reprPrec h _ := Std.Format.text s!"Hash({h.bytes.toList.map UInt8.toNat})"

instance : Inhabited Hash where
  default := ⟨⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩, by native_decide⟩

instance : DecidableEq Hash := fun a b =>
  if h : a.bytes = b.bytes then
    isTrue (by cases a; cases b; simp at h; subst h; rfl)
  else
    isFalse (by intro heq; cases heq; exact h rfl)

/-- Encode a natural number as unsigned LEB128. -/
def encodeLEB128 (n : Nat) : ByteArray :=
  if n < 128 then
    ByteArray.mk #[n.toUInt8]
  else
    let byte := (n % 128 + 128).toUInt8  -- set high bit
    let rest := encodeLEB128 (n / 128)
    ByteArray.mk #[byte] ++ rest
termination_by n
decreasing_by
  omega

/-- Decode an unsigned LEB128 value from the beginning of a ByteArray.
    Returns the decoded value and the number of bytes consumed. -/
def decodeLEB128 (bs : ByteArray) (offset : Nat := 0) : Option (Nat × Nat) :=
  go bs offset 0 0
where
  go (bs : ByteArray) (offset : Nat) (result : Nat) (shift : Nat) : Option (Nat × Nat) :=
    if offset >= bs.size then
      none
    else
      let byte := bs.get! offset
      let value := result + (byte.toNat % 128) * (2 ^ shift)
      if byte.toNat < 128 then
        some (value, offset + 1)
      else
        go bs (offset + 1) value (shift + 7)
  termination_by bs.size - offset

/-- Append a single byte to a ByteArray. -/
def ByteArray.pushByte (bs : ByteArray) (b : UInt8) : ByteArray :=
  bs ++ ByteArray.mk #[b]

/-- Concatenate a list of ByteArrays. -/
def ByteArray.concatList (bss : List ByteArray) : ByteArray :=
  bss.foldl (· ++ ·) ByteArray.empty

end HashMath
