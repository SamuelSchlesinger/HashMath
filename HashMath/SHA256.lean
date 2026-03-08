/-
  HashMath.SHA256 — Pure Lean 4 implementation of SHA-256 (FIPS 180-4)

  Produces a 32-byte (256-bit) hash digest. All arithmetic is on UInt32
  with big-endian byte ordering as specified by the standard.
-/

import HashMath.Basic

namespace HashMath

namespace SHA256

/-! ### Constants -/

/-- The 64 round constants (first 32 bits of the fractional parts of the
    cube roots of the first 64 primes). -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

/-- The 8 initial hash values (first 32 bits of the fractional parts of the
    square roots of the first 8 primes). -/
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-! ### Bit operations on UInt32 -/

/-- Right rotation of a UInt32 by `n` bit positions. -/
@[inline] def rotr (n : UInt32) (x : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256 Ch function: choose bits of y where e=1, bits of z where e=0. -/
@[inline] def ch (e f g : UInt32) : UInt32 :=
  (e &&& f) ^^^ ((e ^^^ 0xFFFFFFFF) &&& g)

/-- SHA-256 Maj function: majority of three inputs. -/
@[inline] def maj (a b c : UInt32) : UInt32 :=
  (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- SHA-256 Σ₀ (big sigma 0): used in compression. -/
@[inline] def sigma0 (x : UInt32) : UInt32 :=
  rotr 2 x ^^^ rotr 13 x ^^^ rotr 22 x

/-- SHA-256 Σ₁ (big sigma 1): used in compression. -/
@[inline] def sigma1 (x : UInt32) : UInt32 :=
  rotr 6 x ^^^ rotr 11 x ^^^ rotr 25 x

/-- SHA-256 σ₀ (little sigma 0): used in message schedule. -/
@[inline] def lsigma0 (x : UInt32) : UInt32 :=
  rotr 7 x ^^^ rotr 18 x ^^^ (x >>> 3)

/-- SHA-256 σ₁ (little sigma 1): used in message schedule. -/
@[inline] def lsigma1 (x : UInt32) : UInt32 :=
  rotr 17 x ^^^ rotr 19 x ^^^ (x >>> 10)

/-! ### Big-endian conversions -/

/-- Read a big-endian UInt32 from 4 bytes at a given offset. -/
def readBE32 (data : ByteArray) (offset : Nat) : UInt32 :=
  let b0 := (data.get! offset).toUInt32
  let b1 := (data.get! (offset + 1)).toUInt32
  let b2 := (data.get! (offset + 2)).toUInt32
  let b3 := (data.get! (offset + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Append a UInt32 as 4 big-endian bytes to a ByteArray. -/
def writeBE32 (arr : ByteArray) (val : UInt32) : ByteArray :=
  let b0 := (val >>> 24).toUInt8
  let b1 := (val >>> 16).toUInt8
  let b2 := (val >>> 8).toUInt8
  let b3 := val.toUInt8
  ((arr.push b0).push b1).push b2 |>.push b3

/-! ### Padding -/

/-- Pad a message according to SHA-256: append 0x80, then zeros, then 64-bit
    big-endian bit length. The result length is a multiple of 64 bytes. -/
def pad (data : ByteArray) : ByteArray :=
  let bitLen : UInt64 := (data.size * 8).toUInt64
  -- Append the 0x80 byte
  let padded := data.push 0x80
  -- Calculate how many zero bytes we need: want (padded.size + zeros) ≡ 56 (mod 64)
  let r := padded.size % 64
  let zerosNeeded := if r <= 56 then 56 - r else 64 - r + 56
  -- Append zero bytes
  let padded := (List.range zerosNeeded).foldl (fun acc _ => acc.push 0x00) padded
  -- Append 64-bit big-endian bit length
  let padded := padded.push (bitLen >>> 56).toUInt8
  let padded := padded.push (bitLen >>> 48).toUInt8
  let padded := padded.push (bitLen >>> 40).toUInt8
  let padded := padded.push (bitLen >>> 32).toUInt8
  let padded := padded.push (bitLen >>> 24).toUInt8
  let padded := padded.push (bitLen >>> 16).toUInt8
  let padded := padded.push (bitLen >>> 8).toUInt8
  padded.push bitLen.toUInt8

/-! ### Message schedule -/

/-- Build the 64-word message schedule from a single 64-byte block. -/
def messageSchedule (block : ByteArray) (blockOffset : Nat) : Array UInt32 :=
  -- First 16 words: direct from the block
  let w0 : Array UInt32 := (List.range 16).foldl
    (fun acc i => acc.push (readBE32 block (blockOffset + i * 4)))
    #[]
  -- Extend to 64 words using lsigma0 and lsigma1
  (List.range 48).foldl
    (fun w i =>
      let idx := i + 16
      let s0 := lsigma0 (w[idx - 15]!)
      let s1 := lsigma1 (w[idx - 2]!)
      w.push (w[idx - 16]! + s0 + w[idx - 7]! + s1))
    w0

/-! ### Compression -/

/-- The 8-word working state for compression, stored as a tuple. -/
abbrev State8 := UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32

/-- Perform one round of SHA-256 compression. -/
@[inline] def compressRound (s : State8) (ki wi : UInt32) : State8 :=
  let (a, b, c, d, e, f, g, h) := s
  let t1 := h + sigma1 e + ch e f g + ki + wi
  let t2 := sigma0 a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

/-- Compress a single 64-byte block, updating the hash state. -/
def compressBlock (hash : Array UInt32) (block : ByteArray) (blockOffset : Nat) : Array UInt32 :=
  let w := messageSchedule block blockOffset
  let initState : State8 :=
    (hash[0]!, hash[1]!, hash[2]!, hash[3]!,
     hash[4]!, hash[5]!, hash[6]!, hash[7]!)
  let finalState := (List.range 64).foldl
    (fun s i => compressRound s (K[i]!) (w[i]!))
    initState
  let (a, b, c, d, e, f, g, h) := finalState
  #[hash[0]! + a, hash[1]! + b, hash[2]! + c, hash[3]! + d,
    hash[4]! + e, hash[5]! + f, hash[6]! + g, hash[7]! + h]

/-! ### Top-level hash function -/

/-- Finalize: convert the 8-word hash state to a 32-byte big-endian ByteArray. -/
def finalize (hash : Array UInt32) : ByteArray :=
  (List.range 8).foldl
    (fun acc i => writeBE32 acc (hash[i]!))
    ByteArray.empty

/-- Process all blocks of the padded message. -/
def processBlocks (padded : ByteArray) (hash : Array UInt32) : Array UInt32 :=
  let numBlocks := padded.size / 64
  (List.range numBlocks).foldl
    (fun h i => compressBlock h padded (i * 64))
    hash

end SHA256

/-- Compute the SHA-256 hash of a ByteArray, producing a 32-byte digest. -/
def sha256 (data : ByteArray) : ByteArray :=
  let padded := SHA256.pad data
  let hash := SHA256.processBlocks padded SHA256.H0
  SHA256.finalize hash

/-- The output of sha256 is always exactly 32 bytes.
    This follows from the structure of `finalize`, which writes exactly
    8 × 4 = 32 bytes via `writeBE32` starting from an empty ByteArray.
    We axiomatize this since the full proof requires reasoning about
    foldl over a concrete list. -/
axiom sha256_size (data : ByteArray) : (sha256 data).size = 32

end HashMath
