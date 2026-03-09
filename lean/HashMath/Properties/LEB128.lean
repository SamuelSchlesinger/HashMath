/-
  HashMath.Properties.LEB128 — LEB128 encoding injectivity

  The key insight: LEB128 is prefix-free. The high bit of each byte
  indicates continuation (1) or termination (0). This makes the encoding
  unambiguous and injective.

  Strategy: define a List UInt8 version, prove it injective via strong
  induction on n (4 cases: both small, both large, two mixed), then
  connect to the ByteArray version via data.toList.
-/

import HashMath.Basic

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- List-based LEB128 encoding
-- ═══════════════════════════════════════════════════════════════════

/-- LEB128 encoding as a list of bytes (mirrors encodeLEB128 but easier
    to reason about than ByteArray). -/
def encodeLEB128List (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else (n % 128 + 128).toUInt8 :: encodeLEB128List (n / 128)
termination_by n
decreasing_by omega

theorem encodeLEB128List_lt_128 (n : Nat) (h : n < 128) :
    encodeLEB128List n = [n.toUInt8] := by
  rw [encodeLEB128List.eq_1]; simp [h]

theorem encodeLEB128List_ge_128 (n : Nat) (h : ¬ n < 128) :
    encodeLEB128List n = (n % 128 + 128).toUInt8 :: encodeLEB128List (n / 128) := by
  rw [encodeLEB128List.eq_1]; simp [h]

-- ═══════════════════════════════════════════════════════════════════
-- Core injectivity proof (List version)
-- ═══════════════════════════════════════════════════════════════════

/-- LEB128 list encoding is injective. Proof by strong induction on n with
    4 cases based on whether n, m are < 128 or ≥ 128:
    - Both small: single bytes, UInt8 injective in [0,128)
    - Both large: first byte gives n%128 = m%128, tail gives n/128 = m/128 by IH
    - Mixed: first byte has different high bit (< 128 vs ≥ 128), contradiction -/
theorem encodeLEB128List_injective : ∀ n m : Nat,
    encodeLEB128List n = encodeLEB128List m → n = m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m h
    by_cases hn : n < 128
    · by_cases hm : m < 128
      · -- Both small: [n.toUInt8] = [m.toUInt8]
        rw [encodeLEB128List_lt_128 n hn, encodeLEB128List_lt_128 m hm] at h
        have := List.cons.inj h
        have h2 : n.toUInt8.toNat = m.toUInt8.toNat := by rw [this.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2; omega
      · -- n small, m large: high bits of first byte differ
        rw [encodeLEB128List_lt_128 n hn, encodeLEB128List_ge_128 m hm] at h
        have := List.cons.inj h
        have h2 : n.toUInt8.toNat = (m % 128 + 128).toUInt8.toNat := by rw [this.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2; omega
    · by_cases hm : m < 128
      · -- n large, m small: symmetric
        rw [encodeLEB128List_ge_128 n hn, encodeLEB128List_lt_128 m hm] at h
        have := List.cons.inj h
        have h2 : (n % 128 + 128).toUInt8.toNat = m.toUInt8.toNat := by rw [this.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2; omega
      · -- Both large: first bytes → n%128 = m%128, tails → n/128 = m/128 by IH
        rw [encodeLEB128List_ge_128 n hn, encodeLEB128List_ge_128 m hm] at h
        have hcons := List.cons.inj h
        have h2 : (n % 128 + 128).toUInt8.toNat = (m % 128 + 128).toUInt8.toNat := by
          rw [hcons.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2
        have hdiv : n / 128 = m / 128 := ih (n / 128) (by omega) (m / 128) hcons.2
        omega

-- ═══════════════════════════════════════════════════════════════════
-- Prefix-free property (stronger than injectivity)
-- ═══════════════════════════════════════════════════════════════════

/-- LEB128 encoding is prefix-free: if encode(n) ++ rest₁ = encode(m) ++ rest₂,
    then n = m and rest₁ = rest₂. This is stronger than injectivity and is
    needed for splitting concatenated serializations. -/
theorem encodeLEB128List_prefix_free : ∀ n m : Nat,
    ∀ rest₁ rest₂ : List UInt8,
    encodeLEB128List n ++ rest₁ = encodeLEB128List m ++ rest₂ →
    n = m ∧ rest₁ = rest₂ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m rest₁ rest₂ h
    by_cases hn : n < 128
    · by_cases hm : m < 128
      · rw [encodeLEB128List_lt_128 n hn, encodeLEB128List_lt_128 m hm] at h
        have hcons := List.cons.inj (List.singleton_append ▸ List.singleton_append ▸ h)
        have h2 : n.toUInt8.toNat = m.toUInt8.toNat := by rw [hcons.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2
        exact ⟨by omega, hcons.2⟩
      · rw [encodeLEB128List_lt_128 n hn, encodeLEB128List_ge_128 m hm] at h
        have hcons := List.cons.inj (List.singleton_append ▸ h)
        have h2 : n.toUInt8.toNat = (m % 128 + 128).toUInt8.toNat := by rw [hcons.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2; omega
    · by_cases hm : m < 128
      · rw [encodeLEB128List_ge_128 n hn, encodeLEB128List_lt_128 m hm] at h
        have hcons := List.cons.inj (List.singleton_append ▸ h.symm).symm
        have h2 : (n % 128 + 128).toUInt8.toNat = m.toUInt8.toNat := by rw [hcons.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2; omega
      · rw [encodeLEB128List_ge_128 n hn, encodeLEB128List_ge_128 m hm] at h
        have hcons := List.cons.inj h
        have h2 : (n % 128 + 128).toUInt8.toNat = (m % 128 + 128).toUInt8.toNat := by
          rw [hcons.1]
        simp [Nat.toUInt8, UInt8.toNat, UInt8.ofNat] at h2
        have ⟨hdiv, hrest⟩ := ih (n / 128) (by omega) (m / 128) rest₁ rest₂ hcons.2
        exact ⟨by omega, hrest⟩

-- ═══════════════════════════════════════════════════════════════════
-- Connecting ByteArray and List versions
-- ═══════════════════════════════════════════════════════════════════

/-- The ByteArray encoding's data matches the list encoding. -/
theorem encodeLEB128_toList (n : Nat) :
    (encodeLEB128 n).data.toList = encodeLEB128List n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [encodeLEB128.eq_1, encodeLEB128List.eq_1]
    by_cases hn : n < 128
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      have key : (ByteArray.mk #[(n % 128 + 128).toUInt8] ++ encodeLEB128 (n / 128)).data.toList
        = [(n % 128 + 128).toUInt8] ++ (encodeLEB128 (n / 128)).data.toList := rfl
      rw [key, ih (n / 128) (by omega), List.singleton_append]

-- ═══════════════════════════════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════════════════════════════

/-- LEB128 encoding (ByteArray version) is injective.
    Derived from the list version via data.toList. -/
theorem encodeLEB128_injective (n m : Nat) :
    encodeLEB128 n = encodeLEB128 m → n = m := by
  intro h
  have h1 : (encodeLEB128 n).data.toList = (encodeLEB128 m).data.toList := by rw [h]
  rw [encodeLEB128_toList, encodeLEB128_toList] at h1
  exact encodeLEB128List_injective n m h1

end HashMath
