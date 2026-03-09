/-
  HashMath.Properties.DeBruijn — Properties of de Bruijn lifting and substitution

  These are the foundational lemmas that underpin all metatheory about
  the type checker: reduction preserves types, substitution commutes, etc.
-/

import HashMath.Expr

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- Lifting properties
-- ═══════════════════════════════════════════════════════════════════

/-- Lifting by 0 is the identity. -/
theorem Expr.liftN_zero (e : Expr) : ∀ c, e.liftN 0 c = e := by
  induction e with
  | bvar i => intro c; simp [Expr.liftN]
  | sort l => intro _; rfl
  | const h ls => intro _; rfl
  | app f a ihf iha => intro c; simp [Expr.liftN, ihf c, iha c]
  | lam ty body iht ihb => intro c; simp [Expr.liftN, iht c, ihb (c + 1)]
  | forallE ty body iht ihb => intro c; simp [Expr.liftN, iht c, ihb (c + 1)]
  | letE ty val body iht ihv ihb =>
    intro c; simp [Expr.liftN, iht c, ihv c, ihb (c + 1)]
  | proj h i s ihs => intro c; simp [Expr.liftN, ihs c]
  | iref idx ls => intro _; rfl

/-- Convenience: lifting by 0 at default cutoff. -/
theorem Expr.liftN_zero' (e : Expr) : e.liftN 0 = e :=
  Expr.liftN_zero e 0

-- ═══════════════════════════════════════════════════════════════════
-- Substitution / instantiation basics
-- ═══════════════════════════════════════════════════════════════════

/-- Substituting into a sort is the identity. -/
@[simp] theorem Expr.substN_sort (l : Level) (var : Nat) (s : Expr) :
    (Expr.sort l).substN var s = .sort l := rfl

/-- Substituting into a const is the identity. -/
@[simp] theorem Expr.substN_const (h : Hash) (ls : List Level) (var : Nat) (s : Expr) :
    (Expr.const h ls).substN var s = .const h ls := rfl

/-- Substituting into an iref is the identity. -/
@[simp] theorem Expr.substN_iref (idx : Nat) (ls : List Level) (var : Nat) (s : Expr) :
    (Expr.iref idx ls).substN var s = .iref idx ls := rfl

/-- Lifting a sort is the identity. -/
@[simp] theorem Expr.liftN_sort (l : Level) (n c : Nat) :
    (Expr.sort l).liftN n c = .sort l := rfl

/-- Lifting a const is the identity. -/
@[simp] theorem Expr.liftN_const (h : Hash) (ls : List Level) (n c : Nat) :
    (Expr.const h ls).liftN n c = .const h ls := rfl

/-- Lifting an iref is the identity. -/
@[simp] theorem Expr.liftN_iref (idx : Nat) (ls : List Level) (n c : Nat) :
    (Expr.iref idx ls).liftN n c = .iref idx ls := rfl

/-- Substituting a variable for itself. -/
theorem Expr.substN_bvar_eq (var : Nat) (s : Expr) :
    (Expr.bvar var).substN var s = s := by
  simp [Expr.substN]

/-- Substituting at a lower variable doesn't affect higher bvars. -/
theorem Expr.substN_bvar_gt (i var : Nat) (s : Expr) (h : i > var) :
    (Expr.bvar i).substN var s = .bvar (i - 1) := by
  simp [Expr.substN]
  split
  · omega
  · rfl

/-- Substituting at a higher variable doesn't affect lower bvars. -/
theorem Expr.substN_bvar_lt (i var : Nat) (s : Expr) (h : i < var) :
    (Expr.bvar i).substN var s = .bvar i := by
  simp [Expr.substN]
  split
  · omega
  · split
    · omega
    · rfl

-- ═══════════════════════════════════════════════════════════════════
-- Key lemma: substitution cancels lifting
-- ═══════════════════════════════════════════════════════════════════

/-- Substituting at `var` into an expression lifted at `var` recovers
    the original expression. This is the key lemma for beta reduction. -/
theorem Expr.substN_liftN (e : Expr) : ∀ var s, (e.liftN 1 var).substN var s = e := by
  induction e with
  | bvar i =>
    intro var s
    simp only [Expr.liftN]
    split
    · -- i >= var: liftN gives bvar (i+1), which is > var
      rename_i h
      rw [substN_bvar_gt (i + 1) var s (by omega)]
      simp
    · -- i < var: liftN gives bvar i, which is < var
      rename_i h
      exact substN_bvar_lt i var s (by omega)
  | sort _ => intros; rfl
  | const _ _ => intros; rfl
  | app f a ihf iha =>
    intro var s; simp only [Expr.liftN, Expr.substN, ihf var s, iha var s]
  | lam ty body iht ihb =>
    intro var s
    simp only [Expr.liftN, Expr.substN, iht var s, ihb (var + 1) (s.liftN 1)]
  | forallE ty body iht ihb =>
    intro var s
    simp only [Expr.liftN, Expr.substN, iht var s, ihb (var + 1) (s.liftN 1)]
  | letE ty val body iht ihv ihb =>
    intro var s
    simp only [Expr.liftN, Expr.substN, iht var s, ihv var s, ihb (var + 1) (s.liftN 1)]
  | proj _ _ struct ihs =>
    intro var s; simp only [Expr.liftN, Expr.substN, ihs var s]
  | iref _ _ => intros; rfl

/-- Corollary: instantiating into a lifted expression at cutoff 0 recovers
    the original. Used directly for beta reduction. -/
theorem Expr.instantiate_liftN (e : Expr) (s : Expr) :
    (e.liftN 1).instantiate s = e := by
  exact Expr.substN_liftN e 0 s

-- ═══════════════════════════════════════════════════════════════════
-- Lifting composition
-- ═══════════════════════════════════════════════════════════════════

/-- Lifting composes: lifting by n then by m at an adjusted cutoff is
    the same as lifting by (n + m). -/
theorem Expr.liftN_liftN (e : Expr) :
    ∀ n m c, (e.liftN n c).liftN m (c + n) = e.liftN (n + m) c := by
  induction e with
  | bvar i =>
    intro n m c
    simp only [Expr.liftN]
    split
    · -- i >= c: first liftN gives bvar (i + n)
      rename_i h
      simp only [Expr.liftN]
      split
      · congr 1; omega -- i + n >= c + n, result is i + n + m = i + (n + m)
      · omega          -- i + n < c + n: contradiction with i >= c
    · -- i < c: first liftN gives bvar i
      rename_i h
      simp only [Expr.liftN]
      split
      · omega  -- i >= c + n: impossible since i < c
      · rfl
  | sort _ => intros; rfl
  | const _ _ => intros; rfl
  | app f a ihf iha =>
    intro n m c; simp only [Expr.liftN, ihf n m c, iha n m c]
  | lam ty body iht ihb =>
    intro n m c
    simp only [Expr.liftN]
    have hc : c + 1 + n = c + n + 1 := by omega
    rw [iht n m c, show (body.liftN n (c + 1)).liftN m (c + n + 1) =
      (body.liftN n (c + 1)).liftN m (c + 1 + n) from by rw [hc], ihb n m (c + 1)]
  | forallE ty body iht ihb =>
    intro n m c
    simp only [Expr.liftN]
    have hc : c + 1 + n = c + n + 1 := by omega
    rw [iht n m c, show (body.liftN n (c + 1)).liftN m (c + n + 1) =
      (body.liftN n (c + 1)).liftN m (c + 1 + n) from by rw [hc], ihb n m (c + 1)]
  | letE ty val body iht ihv ihb =>
    intro n m c
    simp only [Expr.liftN]
    have hc : c + 1 + n = c + n + 1 := by omega
    rw [iht n m c, ihv n m c, show (body.liftN n (c + 1)).liftN m (c + n + 1) =
      (body.liftN n (c + 1)).liftN m (c + 1 + n) from by rw [hc], ihb n m (c + 1)]
  | proj _ _ struct ihs =>
    intro n m c
    simp only [Expr.liftN]
    rw [ihs n m c]
  | iref _ _ => intros; rfl

-- ═══════════════════════════════════════════════════════════════════
-- instantiate = substN 0
-- ═══════════════════════════════════════════════════════════════════

/-- Instantiation is substitution at index 0. -/
theorem Expr.instantiate_eq_substN (e s : Expr) :
    e.instantiate s = e.substN 0 s := rfl

-- ═══════════════════════════════════════════════════════════════════
-- substLevelParams preserves de Bruijn structure
-- ═══════════════════════════════════════════════════════════════════

/-- substLevelParams on bvar is identity. -/
@[simp] theorem Expr.substLevelParams_bvar (i : Nat) (ls : List Level) :
    (Expr.bvar i).substLevelParams ls = .bvar i := rfl

/-- substLevelParams on iref. -/
theorem Expr.substLevelParams_iref (idx : Nat) (univs : List Level) (ls : List Level) :
    (Expr.iref idx univs).substLevelParams ls =
      .iref idx (univs.map (Level.substParams ls)) := rfl

-- ═══════════════════════════════════════════════════════════════════
-- getAppFn / getAppArgs / mkAppN properties
-- ═══════════════════════════════════════════════════════════════════

/-- mkAppN with empty args is identity. -/
@[simp] theorem Expr.mkAppN_nil (fn : Expr) : Expr.mkAppN fn [] = fn := by
  simp [Expr.mkAppN, List.foldl]

/-- mkAppN with a singleton. -/
theorem Expr.mkAppN_singleton (fn arg : Expr) :
    Expr.mkAppN fn [arg] = .app fn arg := by
  simp [Expr.mkAppN, List.foldl]

/-- getAppArgs of a non-app is empty. -/
theorem Expr.getAppArgs_non_app (e : Expr) (h : ∀ f a, e ≠ .app f a) :
    e.getAppArgs = [] := by
  unfold Expr.getAppArgs Expr.getAppArgs.go
  cases e <;> simp <;> exact absurd rfl (h _ _)

-- ═══════════════════════════════════════════════════════════════════
-- Level substitution properties
-- ═══════════════════════════════════════════════════════════════════

/-- Substituting with an empty parameter list is the identity. -/
theorem Level.substParams_zero_list (l : Level) :
    l.substParams [] = l := by
  induction l with
  | zero => rfl
  | succ l ih => simp [Level.substParams, ih]
  | max l₁ l₂ ih₁ ih₂ => simp [Level.substParams, ih₁, ih₂]
  | imax l₁ l₂ ih₁ ih₂ => simp [Level.substParams, ih₁, ih₂]
  | param n => simp [Level.substParams, List.getD]

/-- Looking up a param that hits in the substitution list. -/
theorem Level.substParams_param_hit (n : Nat) (ls : List Level) (l : Level)
    (h : ls[n]? = some l) :
    (Level.param n).substParams ls = l := by
  simp [Level.substParams]
  simp [h]

-- ═══════════════════════════════════════════════════════════════════
-- Lifting commutativity
-- ═══════════════════════════════════════════════════════════════════

/-- Lifting commutes with adjusted cutoffs: when c₁ ≤ c₂,
    lifting by n₁ at c₁ then by n₂ at (c₂ + n₁) equals
    lifting by n₂ at c₂ then by n₁ at c₁. -/
theorem Expr.liftN_comm (e : Expr) :
    ∀ n₁ n₂ c₁ c₂, c₁ ≤ c₂ →
    (e.liftN n₁ c₁).liftN n₂ (c₂ + n₁) = (e.liftN n₂ c₂).liftN n₁ c₁ := by
  induction e with
  | bvar i =>
    intro n₁ n₂ c₁ c₂ hc
    simp only [Expr.liftN]
    split
    · -- i >= c₁
      rename_i h1
      simp only [Expr.liftN]
      split
      · -- i + n₁ >= c₂ + n₁, so i >= c₂
        split
        · -- i >= c₂
          simp only [Expr.liftN]
          split
          · congr 1; omega
          · omega
        · omega
      · -- i + n₁ < c₂ + n₁, so i < c₂
        rename_i h2
        split
        · -- i >= c₂: contradiction
          omega
        · -- i < c₂
          simp only [Expr.liftN]
          split
          · rfl
          · omega
    · -- i < c₁
      rename_i h1
      simp only [Expr.liftN]
      split
      · omega -- i >= c₂ + n₁: impossible since i < c₁ ≤ c₂
      · split
        · omega -- i >= c₂: impossible since i < c₁ ≤ c₂
        · simp only [Expr.liftN]
          split
          · omega
          · rfl
  | sort _ => intros; rfl
  | const _ _ => intros; rfl
  | app f a ihf iha =>
    intro n₁ n₂ c₁ c₂ hc
    simp only [Expr.liftN, ihf n₁ n₂ c₁ c₂ hc, iha n₁ n₂ c₁ c₂ hc]
  | lam ty body iht ihb =>
    intro n₁ n₂ c₁ c₂ hc
    simp only [Expr.liftN]
    congr 1
    · exact iht n₁ n₂ c₁ c₂ hc
    · have hc' : c₁ + 1 ≤ c₂ + 1 := by omega
      have h := ihb n₁ n₂ (c₁ + 1) (c₂ + 1) hc'
      rw [show c₂ + 1 + n₁ = c₂ + n₁ + 1 from by omega] at h
      exact h
  | forallE ty body iht ihb =>
    intro n₁ n₂ c₁ c₂ hc
    simp only [Expr.liftN]
    congr 1
    · exact iht n₁ n₂ c₁ c₂ hc
    · have hc' : c₁ + 1 ≤ c₂ + 1 := by omega
      have h := ihb n₁ n₂ (c₁ + 1) (c₂ + 1) hc'
      rw [show c₂ + 1 + n₁ = c₂ + n₁ + 1 from by omega] at h
      exact h
  | letE ty val body iht ihv ihb =>
    intro n₁ n₂ c₁ c₂ hc
    simp only [Expr.liftN]
    congr 1
    · exact iht n₁ n₂ c₁ c₂ hc
    · exact ihv n₁ n₂ c₁ c₂ hc
    · have hc' : c₁ + 1 ≤ c₂ + 1 := by omega
      have h := ihb n₁ n₂ (c₁ + 1) (c₂ + 1) hc'
      rw [show c₂ + 1 + n₁ = c₂ + n₁ + 1 from by omega] at h
      exact h
  | proj _ _ struct ihs =>
    intro n₁ n₂ c₁ c₂ hc
    simp only [Expr.liftN, ihs n₁ n₂ c₁ c₂ hc]
  | iref _ _ => intros; rfl

-- ═══════════════════════════════════════════════════════════════════
-- Lifting past substitution
-- ═══════════════════════════════════════════════════════════════════

/-- Lifting past a substitution at a higher variable:
    when c ≤ var, lifting by n at c commutes with substitution at var,
    adjusting the variable and the substitute. -/
theorem Expr.liftN_substN_high (e : Expr) :
    ∀ n c var s, c ≤ var →
    (e.substN var s).liftN n c = (e.liftN n c).substN (var + n) (s.liftN n c) := by
  induction e with
  | bvar i =>
    intro n c var s hcv
    simp only [Expr.substN, Expr.liftN]
    -- Three cases for substN: i == var, i > var, i < var
    split
    · -- i == var → LHS is s.liftN n c
      rename_i heq
      simp only [beq_iff_eq] at heq; subst heq
      -- RHS: if i ≥ c then bvar (i+n) else bvar i; then substN (var+n)
      -- Since i ≥ c (from hcv after subst), RHS becomes bvar (i+n).substN (i+n) (s.liftN n c) = s.liftN n c
      split
      · simp [Expr.substN]
      · omega
    · -- i ≠ var
      rename_i hne
      have hne' : i ≠ var := by intro h; simp [h] at hne
      -- Split on i > var (LHS)
      split
      · -- i > var → LHS is (bvar (i-1)).liftN n c
        rename_i hgt
        -- Since i > var ≥ c, we have i ≥ c + 1, so i - 1 ≥ c
        -- LHS liftN: i - 1 ≥ c → bvar (i - 1 + n)
        simp only [Expr.liftN]
        split
        · -- i - 1 ≥ c: OK
          -- RHS: i ≥ c → bvar (i + n), substN: i + n ≠ var + n, i + n > var + n → bvar (i+n-1)
          split
          · -- i ≥ c
            simp only [Expr.substN]
            split
            · rename_i h; simp only [beq_iff_eq] at h; omega
            · split
              · congr 1; omega
              · omega
          · omega  -- ¬(i ≥ c) contradicts i > var ≥ c
        · -- ¬(i - 1 ≥ c): contradicts i > var ≥ c (since i ≥ var + 1 ≥ c + 1)
          omega
      · -- i ≤ var (so i < var) → LHS is (bvar i).liftN n c
        rename_i hle
        have hlt : i < var := by omega
        simp only [Expr.liftN]
        split
        · -- i ≥ c → LHS is bvar (i + n)
          rename_i hge
          -- RHS: bvar (i + n), substN (var+n): i+n ≠ var+n, i+n < var+n → bvar (i+n)
          simp only [Expr.substN]
          split
          · rename_i h; simp only [beq_iff_eq] at h; omega
          · split
            · omega
            · rfl
        · -- i < c → LHS is bvar i
          rename_i hlt2
          -- RHS: bvar i, substN (var+n): i ≠ var+n, i < var+n → bvar i
          simp only [Expr.substN]
          split
          · rename_i h; simp only [beq_iff_eq] at h; omega
          · split
            · omega
            · rfl
  | sort _ => intros; rfl
  | const _ _ => intros; rfl
  | app f a ihf iha =>
    intro n c var s hcv
    simp only [Expr.liftN, Expr.substN, ihf n c var s hcv, iha n c var s hcv]
  | lam ty body iht ihb =>
    intro n c var s hcv
    simp only [Expr.liftN, Expr.substN]
    have hcv' : c + 1 ≤ var + 1 := by omega
    congr 1
    · exact iht n c var s hcv
    · have h := ihb n (c + 1) (var + 1) (s.liftN 1) hcv'
      rw [show var + 1 + n = var + n + 1 from by omega] at h
      rw [show (s.liftN 1).liftN n (c + 1) = (s.liftN n c).liftN 1 from
        Expr.liftN_comm s 1 n 0 c (by omega)] at h
      exact h
  | forallE ty body iht ihb =>
    intro n c var s hcv
    simp only [Expr.liftN, Expr.substN]
    have hcv' : c + 1 ≤ var + 1 := by omega
    congr 1
    · exact iht n c var s hcv
    · have h := ihb n (c + 1) (var + 1) (s.liftN 1) hcv'
      rw [show var + 1 + n = var + n + 1 from by omega] at h
      rw [show (s.liftN 1).liftN n (c + 1) = (s.liftN n c).liftN 1 from
        Expr.liftN_comm s 1 n 0 c (by omega)] at h
      exact h
  | letE ty val body iht ihv ihb =>
    intro n c var s hcv
    simp only [Expr.liftN, Expr.substN]
    have hcv' : c + 1 ≤ var + 1 := by omega
    congr 1
    · exact iht n c var s hcv
    · exact ihv n c var s hcv
    · have h := ihb n (c + 1) (var + 1) (s.liftN 1) hcv'
      rw [show var + 1 + n = var + n + 1 from by omega] at h
      rw [show (s.liftN 1).liftN n (c + 1) = (s.liftN n c).liftN 1 from
        Expr.liftN_comm s 1 n 0 c (by omega)] at h
      exact h
  | proj _ _ struct ihs =>
    intro n c var s hcv
    simp only [Expr.liftN, Expr.substN, ihs n c var s hcv]
  | iref _ _ => intros; rfl

-- ═══════════════════════════════════════════════════════════════════
-- Substitution composition
-- ═══════════════════════════════════════════════════════════════════

/-- Substitution composition: performing two substitutions in sequence
    can be expressed as a single-pass combination. This is the hardest
    standard de Bruijn lemma. -/
-- NOTE: This lemma requires intricate reasoning about the interaction
-- between liftN and substN at different levels. The bvar case has
-- many sub-cases depending on the relationship between i, v₁, and v₂.
-- The binder cases additionally need liftN_substN_high and liftN_comm
-- as auxiliary lemmas. Left sorry'd pending further development.
theorem Expr.substN_substN (e : Expr) :
    ∀ (v₁ v₂ : Nat) (s₁ s₂ : Expr), v₁ ≤ v₂ →
    (e.substN (v₂ + 1) (s₁.liftN 1 v₁)).substN v₁ s₂ =
    (e.substN v₁ s₂).substN v₂ (s₁.substN v₁ s₂) := by
  sorry

end HashMath
