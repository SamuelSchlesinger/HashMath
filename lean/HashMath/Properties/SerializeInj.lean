/-
  HashMath.Properties.SerializeInj — Serialization injectivity

  Proves that serializeLevel, serializeExpr, and serializeDecl are injective.
  The key insight: each serialization is PREFIX-FREE. If serialize(x) ++ rest₁ =
  serialize(y) ++ rest₂, then x = y and rest₁ = rest₂.

  This is proved using List UInt8 versions of the serialization functions
  (easier to reason about than ByteArray), then connected to the ByteArray
  versions via data.toList.

  Combined with SHA-256 collision resistance (a computational assumption),
  this gives hash injectivity (see HashInjectivity.lean).
-/

import HashMath.Serialize
import HashMath.Properties.LEB128

namespace HashMath

-- ═══════════════════════════════════════════════════════════════════
-- Generic prefix-free helpers
-- ═══════════════════════════════════════════════════════════════════

/-- Fixed-length lists are prefix-free: equal-length prefixes that
    produce equal concatenations must be equal. -/
theorem fixed_length_prefix_free {α : Type} (a b : List α) (rest₁ rest₂ : List α)
    (hlen : a.length = b.length) (h : a ++ rest₁ = b ++ rest₂) :
    a = b ∧ rest₁ = rest₂ := by
  induction a generalizing b with
  | nil => cases b with
    | nil => exact ⟨rfl, h⟩
    | cons _ _ => simp at hlen
  | cons x xs ihx => cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp [List.cons_append] at h hlen
      have ⟨hxs, hrest⟩ := ihx ys hlen h.2
      exact ⟨by rw [h.1, hxs], hrest⟩

/-- Hash byte lists are prefix-free (fixed 32 bytes). -/
theorem hash_prefix_free (h₁ h₂ : Hash) (rest₁ rest₂ : List UInt8)
    (heq : h₁.bytes.data.toList ++ rest₁ = h₂.bytes.data.toList ++ rest₂) :
    h₁ = h₂ ∧ rest₁ = rest₂ := by
  have hlen : h₁.bytes.data.toList.length = h₂.bytes.data.toList.length := by
    have h1 := h₁.hsize; have h2 := h₂.hsize
    change h₁.bytes.data.toList.length = 32 at h1
    change h₂.bytes.data.toList.length = 32 at h2
    rw [h1, h2]
  have ⟨hdata, hrest⟩ := fixed_length_prefix_free _ _ _ _ hlen heq
  refine ⟨?_, hrest⟩
  cases h₁ with | mk bytes₁ hsize₁ =>
  cases h₂ with | mk bytes₂ hsize₂ =>
  simp at hdata
  cases bytes₁; cases bytes₂; simp at hdata; subst hdata; rfl

/-- Helper for flattening mapped cons lists with appended rest. -/
private theorem map_flatten_cons_append {α β : Type} (f : α → List β)
    (x : α) (xs : List α) (rest : List β) :
    ((x :: xs).map f).flatten ++ rest = f x ++ ((xs.map f).flatten ++ rest) := by
  simp [List.map, List.flatten, List.append_assoc]

-- ═══════════════════════════════════════════════════════════════════
-- ByteArray.concatList ↔ List.flatten helper
-- ═══════════════════════════════════════════════════════════════════

private theorem foldl_append_toList (acc : ByteArray) (bss : List ByteArray) :
    (bss.foldl (· ++ ·) acc).data.toList =
      acc.data.toList ++ (bss.map (·.data.toList)).flatten := by
  induction bss generalizing acc with
  | nil => simp
  | cons b bss ih =>
    simp only [List.foldl, List.map, List.flatten]
    rw [ih (acc ++ b)]
    simp [List.append_assoc]

theorem ByteArray_concatList_toList (bss : List ByteArray) :
    (ByteArray.concatList bss).data.toList = (bss.map (·.data.toList)).flatten := by
  unfold ByteArray.concatList
  rw [foldl_append_toList]
  simp

-- ═══════════════════════════════════════════════════════════════════
-- List-based Level serialization
-- ═══════════════════════════════════════════════════════════════════

/-- Level serialization as List UInt8 (mirrors serializeLevel). -/
def serializeLevelList : Level → List UInt8
  | .zero => [Tag.levelZero]
  | .succ l => Tag.levelSucc :: serializeLevelList l
  | .max l₁ l₂ => Tag.levelMax :: (serializeLevelList l₁ ++ serializeLevelList l₂)
  | .imax l₁ l₂ => Tag.levelIMax :: (serializeLevelList l₁ ++ serializeLevelList l₂)
  | .param n => Tag.levelParam :: encodeLEB128List n

/-- Level serialization is prefix-free. -/
theorem serializeLevelList_prefix_free :
    ∀ l₁ l₂ : Level, ∀ rest₁ rest₂ : List UInt8,
    serializeLevelList l₁ ++ rest₁ = serializeLevelList l₂ ++ rest₂ →
    l₁ = l₂ ∧ rest₁ = rest₂ := by
  intro l₁
  induction l₁ with
  | zero =>
    intro l₂ rest₁ rest₂ h
    cases l₂ with
    | zero => simp [serializeLevelList] at h; exact ⟨rfl, h⟩
    | _ => all_goals {
        simp only [serializeLevelList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | succ l ih =>
    intro l₂ rest₁ rest₂ h
    cases l₂ with
    | succ l' =>
      simp only [serializeLevelList, List.cons_append] at h
      have ⟨heq, hrest⟩ := ih l' rest₁ rest₂ (List.cons.inj h).2
      exact ⟨congrArg Level.succ heq, hrest⟩
    | _ => all_goals {
        simp only [serializeLevelList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | max l₁ l₂ ih₁ ih₂ =>
    intro l₂' rest₁ rest₂ h
    cases l₂' with
    | max l₁' l₂'' =>
      simp only [serializeLevelList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨h1, hrest1⟩ := ih₁ l₁' _ _ htail
      have ⟨h2, hrest2⟩ := ih₂ l₂'' _ _ hrest1
      exact ⟨by rw [h1, h2], hrest2⟩
    | _ => all_goals {
        simp only [serializeLevelList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | imax l₁ l₂ ih₁ ih₂ =>
    intro l₂' rest₁ rest₂ h
    cases l₂' with
    | imax l₁' l₂'' =>
      simp only [serializeLevelList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨h1, hrest1⟩ := ih₁ l₁' _ _ htail
      have ⟨h2, hrest2⟩ := ih₂ l₂'' _ _ hrest1
      exact ⟨by rw [h1, h2], hrest2⟩
    | _ => all_goals {
        simp only [serializeLevelList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | param n =>
    intro l₂ rest₁ rest₂ h
    cases l₂ with
    | param m =>
      simp only [serializeLevelList, List.cons_append] at h
      have ⟨heq, hrest⟩ := encodeLEB128List_prefix_free n m rest₁ rest₂ (List.cons.inj h).2
      exact ⟨congrArg Level.param heq, hrest⟩
    | _ => all_goals {
        simp only [serializeLevelList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }

/-- A list of levels is prefix-free when the count is known. -/
theorem serializeLevelListList_prefix_free :
    ∀ (ls₁ ls₂ : List Level), ls₁.length = ls₂.length →
    ∀ (rest₁ rest₂ : List UInt8),
    (ls₁.map serializeLevelList).flatten ++ rest₁ =
    (ls₂.map serializeLevelList).flatten ++ rest₂ →
    ls₁ = ls₂ ∧ rest₁ = rest₂ := by
  intro ls₁
  induction ls₁ with
  | nil => intro ls₂ hlen; cases ls₂ with
    | nil => intro rest₁ rest₂ h; simp at h; exact ⟨rfl, h⟩
    | cons _ _ => simp at hlen
  | cons l₁ ls₁ ih => intro ls₂ hlen; cases ls₂ with
    | nil => simp at hlen
    | cons l₂ ls₂ =>
      intro rest₁ rest₂ h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [map_flatten_cons_append, map_flatten_cons_append] at h
      have ⟨hl, hrest⟩ := serializeLevelList_prefix_free l₁ l₂ _ _ h
      have ⟨hls, hrest'⟩ := ih ls₂ hlen _ _ hrest
      exact ⟨by rw [hl, hls], hrest'⟩

-- ═══════════════════════════════════════════════════════════════════
-- List-based Expr serialization
-- ═══════════════════════════════════════════════════════════════════

/-- Expr serialization as List UInt8 (mirrors serializeExpr). -/
def serializeExprList : Expr → List UInt8
  | .bvar n => Tag.exprBvar :: encodeLEB128List n
  | .sort l => Tag.exprSort :: serializeLevelList l
  | .const h ls =>
    Tag.exprConst :: (h.bytes.data.toList ++ encodeLEB128List ls.length ++
      (ls.map serializeLevelList).flatten)
  | .app f a => Tag.exprApp :: (serializeExprList f ++ serializeExprList a)
  | .lam ty body => Tag.exprLam :: (serializeExprList ty ++ serializeExprList body)
  | .forallE ty body => Tag.exprForallE :: (serializeExprList ty ++ serializeExprList body)
  | .letE ty val body =>
    Tag.exprLetE :: (serializeExprList ty ++ serializeExprList val ++ serializeExprList body)
  | .proj h i s => Tag.exprProj :: (h.bytes.data.toList ++ encodeLEB128List i ++ serializeExprList s)
  | .iref idx ls =>
    Tag.exprIRef :: (encodeLEB128List idx ++ encodeLEB128List ls.length ++
      (ls.map serializeLevelList).flatten)

/-- Expr serialization is prefix-free. -/
theorem serializeExprList_prefix_free :
    ∀ e₁ e₂ : Expr, ∀ rest₁ rest₂ : List UInt8,
    serializeExprList e₁ ++ rest₁ = serializeExprList e₂ ++ rest₂ →
    e₁ = e₂ ∧ rest₁ = rest₂ := by
  intro e₁
  induction e₁ with
  | bvar n =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | bvar m =>
      simp only [serializeExprList, List.cons_append] at h
      have ⟨heq, hrest⟩ := encodeLEB128List_prefix_free n m rest₁ rest₂ (List.cons.inj h).2
      exact ⟨congrArg Expr.bvar heq, hrest⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | sort l =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | sort l' =>
      simp only [serializeExprList, List.cons_append] at h
      have ⟨heq, hrest⟩ := serializeLevelList_prefix_free l l' rest₁ rest₂ (List.cons.inj h).2
      exact ⟨congrArg Expr.sort heq, hrest⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | const hash ls =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | const hash' ls' =>
      simp only [serializeExprList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hhash, hrest1⟩ := hash_prefix_free hash hash' _ _ htail
      have ⟨hlen, hrest2⟩ := encodeLEB128List_prefix_free ls.length ls'.length _ _ hrest1
      have ⟨hls, hrest3⟩ := serializeLevelListList_prefix_free ls ls' (by omega) _ _ hrest2
      exact ⟨by rw [hhash, hls], hrest3⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | app f a ihf iha =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | app f' a' =>
      simp only [serializeExprList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hf, hrest1⟩ := ihf f' _ _ htail
      have ⟨ha, hrest2⟩ := iha a' _ _ hrest1
      exact ⟨by rw [hf, ha], hrest2⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | lam ty body ihty ihbody =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | lam ty' body' =>
      simp only [serializeExprList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hty, hrest1⟩ := ihty ty' _ _ htail
      have ⟨hbody, hrest2⟩ := ihbody body' _ _ hrest1
      exact ⟨by rw [hty, hbody], hrest2⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | forallE ty body ihty ihbody =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | forallE ty' body' =>
      simp only [serializeExprList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hty, hrest1⟩ := ihty ty' _ _ htail
      have ⟨hbody, hrest2⟩ := ihbody body' _ _ hrest1
      exact ⟨by rw [hty, hbody], hrest2⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | letE ty val body ihty ihval ihbody =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | letE ty' val' body' =>
      simp only [serializeExprList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hty, hrest1⟩ := ihty ty' _ _ htail
      have ⟨hval, hrest2⟩ := ihval val' _ _ hrest1
      have ⟨hbody, hrest3⟩ := ihbody body' _ _ hrest2
      exact ⟨by rw [hty, hval, hbody], hrest3⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | proj hash i s ihs =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | proj hash' i' s' =>
      simp only [serializeExprList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hhash, hrest1⟩ := hash_prefix_free hash hash' _ _ htail
      have ⟨hi, hrest2⟩ := encodeLEB128List_prefix_free i i' _ _ hrest1
      have ⟨hs, hrest3⟩ := ihs s' _ _ hrest2
      exact ⟨by rw [hhash, hi, hs], hrest3⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | iref idx ls =>
    intro e₂ rest₁ rest₂ h
    cases e₂ with
    | iref idx' ls' =>
      simp only [serializeExprList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hidx, hrest1⟩ := encodeLEB128List_prefix_free idx idx' _ _ htail
      have ⟨hlen, hrest2⟩ := encodeLEB128List_prefix_free ls.length ls'.length _ _ hrest1
      have ⟨hls, hrest3⟩ := serializeLevelListList_prefix_free ls ls' (by omega) _ _ hrest2
      exact ⟨by rw [hidx, hls], hrest3⟩
    | _ => all_goals {
        simp only [serializeExprList, List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }

/-- A list of exprs is prefix-free when the count is known. -/
theorem serializeExprListList_prefix_free :
    ∀ (es₁ es₂ : List Expr), es₁.length = es₂.length →
    ∀ (rest₁ rest₂ : List UInt8),
    (es₁.map serializeExprList).flatten ++ rest₁ =
    (es₂.map serializeExprList).flatten ++ rest₂ →
    es₁ = es₂ ∧ rest₁ = rest₂ := by
  intro es₁
  induction es₁ with
  | nil => intro es₂ hlen; cases es₂ with
    | nil => intro rest₁ rest₂ h; simp at h; exact ⟨rfl, h⟩
    | cons _ _ => simp at hlen
  | cons e₁ es₁ ih => intro es₂ hlen; cases es₂ with
    | nil => simp at hlen
    | cons e₂ es₂ =>
      intro rest₁ rest₂ h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [map_flatten_cons_append, map_flatten_cons_append] at h
      have ⟨he, hrest⟩ := serializeExprList_prefix_free e₁ e₂ _ _ h
      have ⟨hes, hrest'⟩ := ih es₂ hlen _ _ hrest
      exact ⟨by rw [he, hes], hrest'⟩

-- ═══════════════════════════════════════════════════════════════════
-- List-based Decl serialization
-- ═══════════════════════════════════════════════════════════════════

/-- Bool serialization as List UInt8. -/
def serBoolList (b : Bool) : List UInt8 := [if b then 0x01 else 0x00]

/-- InductiveType serialization as List UInt8. -/
def serializeInductiveTypeList (it : InductiveType) : List UInt8 :=
  serializeExprList it.type ++ encodeLEB128List it.ctors.length ++
  (it.ctors.map serializeExprList).flatten

/-- InductiveBlock serialization as List UInt8. -/
def serializeInductiveBlockList (block : InductiveBlock) : List UInt8 :=
  encodeLEB128List block.numUnivParams ++
  encodeLEB128List block.numParams ++
  encodeLEB128List block.types.length ++
  (block.types.map serializeInductiveTypeList).flatten ++
  serBoolList block.isUnsafe

/-- QuotKind serialization (same as ByteArray version). -/
def serializeQuotKindList (k : QuotKind) : List UInt8 := [serializeQuotKind k]

/-- Decl serialization as List UInt8 (mirrors serializeDecl). -/
def serializeDeclList : Decl → List UInt8
  | .axiom n ty =>
    Tag.declAxiom :: (encodeLEB128List n ++ serializeExprList ty)
  | .definition n ty val =>
    Tag.declDefinition :: (encodeLEB128List n ++ serializeExprList ty ++ serializeExprList val)
  | .inductive block =>
    Tag.declInductive :: serializeInductiveBlockList block
  | .quotient kind =>
    Tag.declQuotient :: serializeQuotKindList kind

/-- InductiveType serialization is prefix-free. -/
theorem serializeInductiveTypeList_prefix_free
    (it₁ it₂ : InductiveType) (rest₁ rest₂ : List UInt8)
    (h : serializeInductiveTypeList it₁ ++ rest₁ = serializeInductiveTypeList it₂ ++ rest₂) :
    it₁ = it₂ ∧ rest₁ = rest₂ := by
  simp only [serializeInductiveTypeList, List.append_assoc] at h
  have ⟨hty, hr1⟩ := serializeExprList_prefix_free it₁.type it₂.type _ _ h
  have ⟨hlen, hr2⟩ := encodeLEB128List_prefix_free it₁.ctors.length it₂.ctors.length _ _ hr1
  have ⟨hctors, hr3⟩ := serializeExprListList_prefix_free it₁.ctors it₂.ctors (by omega) _ _ hr2
  exact ⟨by cases it₁; cases it₂; simp_all, hr3⟩

/-- A list of InductiveTypes is prefix-free when the count is known. -/
theorem serializeInductiveTypeListList_prefix_free :
    ∀ (ts₁ ts₂ : List InductiveType), ts₁.length = ts₂.length →
    ∀ (rest₁ rest₂ : List UInt8),
    (ts₁.map serializeInductiveTypeList).flatten ++ rest₁ =
    (ts₂.map serializeInductiveTypeList).flatten ++ rest₂ →
    ts₁ = ts₂ ∧ rest₁ = rest₂ := by
  intro ts₁
  induction ts₁ with
  | nil => intro ts₂ hlen; cases ts₂ with
    | nil => intro rest₁ rest₂ h; simp at h; exact ⟨rfl, h⟩
    | cons _ _ => simp at hlen
  | cons t₁ ts₁ ih => intro ts₂ hlen; cases ts₂ with
    | nil => simp at hlen
    | cons t₂ ts₂ =>
      intro rest₁ rest₂ h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [map_flatten_cons_append, map_flatten_cons_append] at h
      have ⟨ht, hrest⟩ := serializeInductiveTypeList_prefix_free t₁ t₂ _ _ h
      have ⟨hts, hrest'⟩ := ih ts₂ hlen _ _ hrest
      exact ⟨by rw [ht, hts], hrest'⟩

/-- Bool serialization is prefix-free. -/
theorem serBoolList_prefix_free (b₁ b₂ : Bool) (rest₁ rest₂ : List UInt8)
    (h : serBoolList b₁ ++ rest₁ = serBoolList b₂ ++ rest₂) :
    b₁ = b₂ ∧ rest₁ = rest₂ := by
  simp [serBoolList] at h
  cases b₁ <;> cases b₂ <;> simp_all

/-- InductiveBlock serialization is prefix-free. -/
theorem serializeInductiveBlockList_prefix_free
    (bl₁ bl₂ : InductiveBlock) (rest₁ rest₂ : List UInt8)
    (h : serializeInductiveBlockList bl₁ ++ rest₁ = serializeInductiveBlockList bl₂ ++ rest₂) :
    bl₁ = bl₂ ∧ rest₁ = rest₂ := by
  simp only [serializeInductiveBlockList, List.append_assoc] at h
  have ⟨h1, hr1⟩ := encodeLEB128List_prefix_free bl₁.numUnivParams bl₂.numUnivParams _ _ h
  have ⟨h2, hr2⟩ := encodeLEB128List_prefix_free bl₁.numParams bl₂.numParams _ _ hr1
  have ⟨h3, hr3⟩ := encodeLEB128List_prefix_free bl₁.types.length bl₂.types.length _ _ hr2
  have ⟨h4, hr4⟩ := serializeInductiveTypeListList_prefix_free
    bl₁.types bl₂.types (by omega) _ _ hr3
  have ⟨h5, hr5⟩ := serBoolList_prefix_free bl₁.isUnsafe bl₂.isUnsafe _ _ hr4
  exact ⟨by cases bl₁; cases bl₂; simp_all, hr5⟩

/-- QuotKind serialization is prefix-free. -/
theorem serializeQuotKindList_prefix_free (k₁ k₂ : QuotKind) (rest₁ rest₂ : List UInt8)
    (h : serializeQuotKindList k₁ ++ rest₁ = serializeQuotKindList k₂ ++ rest₂) :
    k₁ = k₂ ∧ rest₁ = rest₂ := by
  simp [serializeQuotKindList, serializeQuotKind] at h
  cases k₁ <;> cases k₂ <;> simp_all

/-- Decl serialization is prefix-free. -/
theorem serializeDeclList_prefix_free :
    ∀ d₁ d₂ : Decl, ∀ rest₁ rest₂ : List UInt8,
    serializeDeclList d₁ ++ rest₁ = serializeDeclList d₂ ++ rest₂ →
    d₁ = d₂ ∧ rest₁ = rest₂ := by
  intro d₁ d₂ rest₁ rest₂ h
  cases d₁ with
  | «axiom» n₁ ty₁ => cases d₂ with
    | «axiom» n₂ ty₂ =>
      simp only [serializeDeclList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hn, hr1⟩ := encodeLEB128List_prefix_free n₁ n₂ _ _ htail
      have ⟨hty, hr2⟩ := serializeExprList_prefix_free ty₁ ty₂ _ _ hr1
      exact ⟨by rw [hn, hty], hr2⟩
    | _ => all_goals {
        simp only [serializeDeclList, serializeQuotKindList, serializeInductiveBlockList,
          List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | definition n₁ ty₁ val₁ => cases d₂ with
    | definition n₂ ty₂ val₂ =>
      simp only [serializeDeclList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hn, hr1⟩ := encodeLEB128List_prefix_free n₁ n₂ _ _ htail
      have ⟨hty, hr2⟩ := serializeExprList_prefix_free ty₁ ty₂ _ _ hr1
      have ⟨hval, hr3⟩ := serializeExprList_prefix_free val₁ val₂ _ _ hr2
      exact ⟨by rw [hn, hty, hval], hr3⟩
    | _ => all_goals {
        simp only [serializeDeclList, serializeQuotKindList, serializeInductiveBlockList,
          List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | «inductive» bl₁ => cases d₂ with
    | «inductive» bl₂ =>
      simp only [serializeDeclList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hbl, hrest⟩ := serializeInductiveBlockList_prefix_free bl₁ bl₂ _ _ htail
      exact ⟨by rw [hbl], hrest⟩
    | _ => all_goals {
        simp only [serializeDeclList, serializeQuotKindList, serializeInductiveBlockList,
          List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }
  | quotient k₁ => cases d₂ with
    | quotient k₂ =>
      simp only [serializeDeclList, List.cons_append, List.append_assoc] at h
      have htail := (List.cons.inj h).2
      have ⟨hk, hrest⟩ := serializeQuotKindList_prefix_free k₁ k₂ _ _ htail
      exact ⟨by rw [hk], hrest⟩
    | _ => all_goals {
        simp only [serializeDeclList, serializeQuotKindList, serializeInductiveBlockList,
          List.cons_append, List.nil_append, List.append_assoc] at h
        exact absurd (List.cons.inj h).1 (by native_decide) }

-- ═══════════════════════════════════════════════════════════════════
-- Injectivity (derived from prefix-free with empty rest)
-- ═══════════════════════════════════════════════════════════════════

/-- Level serialization (List version) is injective. -/
theorem serializeLevelList_injective (l₁ l₂ : Level) :
    serializeLevelList l₁ = serializeLevelList l₂ → l₁ = l₂ := by
  intro h
  have h' : serializeLevelList l₁ ++ [] = serializeLevelList l₂ ++ [] := by simp [h]
  exact (serializeLevelList_prefix_free l₁ l₂ [] [] h').1

/-- Expr serialization (List version) is injective. -/
theorem serializeExprList_injective (e₁ e₂ : Expr) :
    serializeExprList e₁ = serializeExprList e₂ → e₁ = e₂ := by
  intro h
  have h' : serializeExprList e₁ ++ [] = serializeExprList e₂ ++ [] := by simp [h]
  exact (serializeExprList_prefix_free e₁ e₂ [] [] h').1

/-- Decl serialization (List version) is injective. -/
theorem serializeDeclList_injective (d₁ d₂ : Decl) :
    serializeDeclList d₁ = serializeDeclList d₂ → d₁ = d₂ := by
  intro h
  have h' : serializeDeclList d₁ ++ [] = serializeDeclList d₂ ++ [] := by simp [h]
  exact (serializeDeclList_prefix_free d₁ d₂ [] [] h').1

-- ═══════════════════════════════════════════════════════════════════
-- Connecting List and ByteArray versions
-- ═══════════════════════════════════════════════════════════════════

/-- serializeLevel and serializeLevelList produce the same bytes. -/
theorem serializeLevel_toList (l : Level) :
    (serializeLevel l).data.toList = serializeLevelList l := by
  induction l with
  | zero => rfl
  | succ l ih => simp [serializeLevel, serializeLevelList, serByte, ih]
  | max l₁ l₂ ih₁ ih₂ => simp [serializeLevel, serializeLevelList, serByte, ih₁, ih₂]
  | imax l₁ l₂ ih₁ ih₂ => simp [serializeLevel, serializeLevelList, serByte, ih₁, ih₂]
  | param n => simp [serializeLevel, serializeLevelList, serByte, serNat, encodeLEB128_toList]

/-- Helper: map of serializeLevel toList equals map of serializeLevelList. -/
private theorem map_serializeLevel_toList (ls : List Level) :
    (ls.map serializeLevel).map (·.data.toList) = ls.map serializeLevelList := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [List.map, serializeLevel_toList, ih]

/-- serializeExpr and serializeExprList produce the same bytes. -/
theorem serializeExpr_toList (e : Expr) :
    (serializeExpr e).data.toList = serializeExprList e := by
  induction e with
  | bvar n => simp [serializeExpr, serializeExprList, serByte, serNat, encodeLEB128_toList]
  | sort l => simp [serializeExpr, serializeExprList, serByte, serializeLevel_toList]
  | const h ls =>
    simp [serializeExpr, serializeExprList, serByte, serHash, serNat, encodeLEB128_toList]
    rw [ByteArray_concatList_toList, map_serializeLevel_toList]
  | app f a ihf iha => simp [serializeExpr, serializeExprList, serByte, ihf, iha]
  | lam ty body iht ihb => simp [serializeExpr, serializeExprList, serByte, iht, ihb]
  | forallE ty body iht ihb => simp [serializeExpr, serializeExprList, serByte, iht, ihb]
  | letE ty val body iht ihv ihb =>
    simp [serializeExpr, serializeExprList, serByte, iht, ihv, ihb]
  | proj h i s ihs =>
    simp [serializeExpr, serializeExprList, serByte, serHash, serNat, encodeLEB128_toList, ihs]
  | iref idx ls =>
    simp [serializeExpr, serializeExprList, serByte, serNat, encodeLEB128_toList]
    rw [ByteArray_concatList_toList, map_serializeLevel_toList]

/-- Helper: map of serializeExpr toList equals map of serializeExprList. -/
private theorem map_serializeExpr_toList (es : List Expr) :
    (es.map serializeExpr).map (·.data.toList) = es.map serializeExprList := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [List.map, serializeExpr_toList, ih]

/-- serializeInductiveType and serializeInductiveTypeList produce the same bytes. -/
theorem serializeInductiveType_toList (it : InductiveType) :
    (serializeInductiveType it).data.toList = serializeInductiveTypeList it := by
  simp [serializeInductiveType, serializeInductiveTypeList, serNat,
    serializeExpr_toList, encodeLEB128_toList]
  rw [ByteArray_concatList_toList, map_serializeExpr_toList]

/-- Helper: map of serializeInductiveType toList. -/
private theorem map_serializeInductiveType_toList (ts : List InductiveType) :
    (ts.map serializeInductiveType).map (·.data.toList) = ts.map serializeInductiveTypeList := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.map, serializeInductiveType_toList, ih]

/-- serializeInductiveBlock and serializeInductiveBlockList produce the same bytes. -/
theorem serializeInductiveBlock_toList (block : InductiveBlock) :
    (serializeInductiveBlock block).data.toList = serializeInductiveBlockList block := by
  simp [serializeInductiveBlock, serializeInductiveBlockList, serNat, serBool,
    serBoolList, encodeLEB128_toList]
  rw [ByteArray_concatList_toList, map_serializeInductiveType_toList]

/-- serializeDecl and serializeDeclList produce the same bytes. -/
theorem serializeDecl_toList (d : Decl) :
    (serializeDecl d).data.toList = serializeDeclList d := by
  cases d with
  | «axiom» n ty =>
    simp [serializeDecl, serializeDeclList, serByte, serNat,
      encodeLEB128_toList, serializeExpr_toList]
  | definition n ty val =>
    simp [serializeDecl, serializeDeclList, serByte, serNat,
      encodeLEB128_toList, serializeExpr_toList]
  | «inductive» block =>
    simp [serializeDecl, serializeDeclList, serByte, serializeInductiveBlock_toList]
  | quotient kind =>
    simp [serializeDecl, serializeDeclList, serByte, serializeQuotKindList, serializeQuotKind]

-- ═══════════════════════════════════════════════════════════════════
-- ByteArray injectivity
-- ═══════════════════════════════════════════════════════════════════

/-- Level serialization is injective. -/
theorem serializeLevel_injective (l₁ l₂ : Level) :
    serializeLevel l₁ = serializeLevel l₂ → l₁ = l₂ := by
  intro h
  have h1 : (serializeLevel l₁).data.toList = (serializeLevel l₂).data.toList := by rw [h]
  rw [serializeLevel_toList, serializeLevel_toList] at h1
  exact serializeLevelList_injective l₁ l₂ h1

/-- Expression serialization is injective. -/
theorem serializeExpr_injective (e₁ e₂ : Expr) :
    serializeExpr e₁ = serializeExpr e₂ → e₁ = e₂ := by
  intro h
  have h1 : (serializeExpr e₁).data.toList = (serializeExpr e₂).data.toList := by rw [h]
  rw [serializeExpr_toList, serializeExpr_toList] at h1
  exact serializeExprList_injective e₁ e₂ h1

/-- Declaration serialization is injective. -/
theorem serializeDecl_injective (d₁ d₂ : Decl) :
    serializeDecl d₁ = serializeDecl d₂ → d₁ = d₂ := by
  intro h
  have h1 : (serializeDecl d₁).data.toList = (serializeDecl d₂).data.toList := by rw [h]
  rw [serializeDecl_toList, serializeDecl_toList] at h1
  exact serializeDeclList_injective d₁ d₂ h1

end HashMath
