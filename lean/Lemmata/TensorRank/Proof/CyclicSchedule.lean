module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.CyclicSchedule
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.CyclicSchedule

variable {k : ℕ} [NeZero k]

private theorem ite_decidable_eq (P : Prop) (d₁ d₂ : Decidable P) (a b : ℕ) :
    @ite ℕ P d₁ a b = @ite ℕ P d₂ a b := by
  cases Subsingleton.elim d₁ d₂
  rfl

private theorem cast_injective_below {u v : ℕ} (hu : u < k) (hv : v < k)
    (h : (u : ZMod k) = (v : ZMod k)) : u = v := by
  have hvv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] using hvv

private theorem positive_cast_ne_zero {u : ℕ} (hu : 0 < u) (huk : u < k) :
    (u : ZMod k) ≠ 0 := by
  intro h
  have := cast_injective_below (v := 0) huk (NeZero.pos k) (by simpa using h)
  omega

@[simp] theorem interval_zero (a : ZMod k) : interval a 0 = ∅ := by
  simp [interval]

theorem interval_succ (a : ZMod k) (l : ℕ) :
    interval a (l + 1) = insert (rightReader a l) (interval a l) := by
  simp [interval, Finset.range_add_one, rightReader]

theorem interval_prepend (a : ZMod k) (l : ℕ) :
    interval (a - 1) (l + 1) = insert a (interval a l) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have ht' := Finset.mem_range.mp ht
    cases t with
    | zero => simp
    | succ t =>
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        refine ⟨t, Finset.mem_range.mpr (by omega), ?_⟩
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        abel
  · intro hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      apply Finset.mem_image.mpr
      refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simp
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      apply Finset.mem_image.mpr
      refine ⟨t + 1, Finset.mem_range.mpr (by have := Finset.mem_range.mp ht; omega), ?_⟩
      simp only [Nat.cast_add, Nat.cast_one]
      abel

theorem self_not_mem_interval (a : ZMod k) {l : ℕ} (hl : l < k) :
    a ∉ interval a l := by
  intro hp
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hp
  have ht' := Finset.mem_range.mp ht
  have he' : ((t + 1 : ℕ) : ZMod k) = 0 := by
    apply add_left_cancel (a := a)
    simpa using he
  exact positive_cast_ne_zero (by omega) (by omega) he'

theorem rightReader_not_mem_interval (a : ZMod k) {l : ℕ} (hl : l + 1 < k) :
    rightReader a l ∉ interval a l := by
  intro hp
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hp
  have ht' := Finset.mem_range.mp ht
  have he' : ((t + 1 : ℕ) : ZMod k) = ((l + 1 : ℕ) : ZMod k) :=
    add_left_cancel he
  have := cast_injective_below (by omega) hl he'
  omega

theorem readers_distinct (a : ZMod k) {l : ℕ} (hl : l < k - 1) :
    a ≠ rightReader a l := by
  intro h
  have he : ((l + 1 : ℕ) : ZMod k) = 0 := by
    apply add_left_cancel (a := a)
    simpa [rightReader] using h.symm
  exact positive_cast_ne_zero (by omega) (by omega) he

theorem interval_full (a : ZMod k) : interval a (k - 1) = Finset.univ.erase a := by
  ext p
  constructor
  · intro hp
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst p
    exact self_not_mem_interval a (by have := NeZero.pos k; omega) hp
  · intro hp
    have hpa : p ≠ a := (Finset.mem_erase.mp hp).1
    have hd : 0 < (p - a).val := by
      by_contra hn
      have hz : (p - a).val = 0 := by omega
      have hz' : p - a = 0 := by
        rw [← ZMod.natCast_zmod_val (p - a), hz]
        simp
      exact hpa (sub_eq_zero.mp hz')
    apply Finset.mem_image.mpr
    refine ⟨(p - a).val - 1, Finset.mem_range.mpr ?_, ?_⟩
    · have := ZMod.val_lt (p - a)
      omega
    · rw [Nat.sub_add_cancel hd, ZMod.natCast_zmod_val]
      abel

@[simp] theorem shortened_false (a : ZMod k) (l : ℕ) :
    shortened l (a, false) = interval a l := rfl

@[simp] theorem shortened_true (a : ZMod k) (l : ℕ) :
    shortened l (a, true) = interval (a - ((l + 1 : ℕ) : ZMod k)) l := rfl

theorem paired_shortened (a : ZMod k) (l : ℕ) :
    shortened l (rightReader a l, true) = shortened l (a, false) := by
  simp [shortened, rightReader]

theorem paired_inputLength (a : ZMod k) (b l : ℕ) :
    inputLength b l (rightReader a l, true) = inputLength b l (a, false) := by
  funext p
  simp only [inputLength, paired_shortened]

theorem token_card : Fintype.card (Token k) = 2 * k := by
  simp [Token, Nat.mul_comm]

/-- Regrouping the tokens into pairs preserves every commutative product. -/
theorem prod_pairs {M : Type*} [CommMonoid M] (F : Token k → M) (l : ℕ) :
    (∏ t, F t) = ∏ a : ZMod k, F (a, false) * F (rightReader a l, true) := by
  calc
    (∏ t, F t) = ∏ t, F (pairingEquiv l t) := ((pairingEquiv l).prod_comp F).symm
    _ = ∏ a : ZMod k, F (a, false) * F (rightReader a l, true) := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro a _
      rw [Fintype.prod_bool]
      exact mul_comm _ _

theorem shortened_false_succ (a : ZMod k) (l : ℕ) :
    shortened (l + 1) (a, false) =
      insert (rightReader a l) (shortened l (a, false)) := interval_succ a l

theorem shortened_true_succ (a : ZMod k) (l : ℕ) :
    shortened (l + 1) (a, true) =
      insert (a - ((l + 1 : ℕ) : ZMod k)) (shortened l (a, true)) := by
  change interval (a - ((l + 1 + 1 : ℕ) : ZMod k)) (l + 1) =
    insert (a - ((l + 1 : ℕ) : ZMod k))
      (interval (a - ((l + 1 : ℕ) : ZMod k)) l)
  have he : a - ((l + 1 + 1 : ℕ) : ZMod k) =
      (a - ((l + 1 : ℕ) : ZMod k)) - 1 := by
    simp only [Nat.cast_add, Nat.cast_one]
    abel
  rw [he, interval_prepend]

theorem paired_shortened_succ (a : ZMod k) (l : ℕ) :
    shortened (l + 1) (rightReader a l, true) =
      insert a (shortened l (a, false)) := by
  rw [shortened_true_succ, paired_shortened]
  simp [rightReader]

theorem inputLength_false_succ (a : ZMod k) (b l : ℕ) :
    inputLength b (l + 1) (a, false) =
      Function.update (inputLength b l (a, false)) (rightReader a l) b := by
  funext p
  change (if p ∈ shortened (l + 1) (a, false) then b else b + 1) = _
  rw [shortened_false_succ]
  by_cases hp : p = rightReader a l
  · subst p
    simp
  · simp [inputLength, hp]
    exact ite_decidable_eq _ _ _ _ _

theorem inputLength_paired_true_succ (a : ZMod k) (b l : ℕ) :
    inputLength b (l + 1) (rightReader a l, true) =
      Function.update (inputLength b l (a, false)) a b := by
  funext p
  change (if p ∈ shortened (l + 1) (rightReader a l, true) then b else b + 1) = _
  rw [paired_shortened_succ]
  by_cases hp : p = a
  · subst p
    simp
  · simp [inputLength, hp]
    exact ite_decidable_eq _ _ _ _ _

@[simp] theorem inputLength_zero (b : ℕ) (t : Token k) (p : ZMod k) :
    inputLength b 0 t p = b + 1 := by
  rcases t with ⟨a, q⟩
  cases q <;> simp [inputLength, shortened]

theorem shortened_full (t : Token k) :
    shortened (k - 1) t = Finset.univ.erase t.1 := by
  rcases t with ⟨a, q⟩
  cases q
  · exact interval_full a
  · have hk : k - 1 + 1 = k := by have := NeZero.pos k; omega
    simp only [shortened_true, hk, ZMod.natCast_self, sub_zero]
    exact interval_full a

theorem inputLength_full (b : ℕ) (t : Token k) (p : ZMod k) (hp : p ≠ t.1) :
    inputLength b (k - 1) t p = b := by
  simp [inputLength, shortened_full, hp]

theorem inputLength_le (b l : ℕ) (t : Token k) (p : ZMod k) :
    inputLength b l t p ≤ b + 1 := by
  unfold inputLength
  split <;> omega

theorem inputLength_pos {b : ℕ} (hb : 0 < b) (l : ℕ) (t : Token k) (p : ZMod k) :
    0 < inputLength b l t p := by
  unfold inputLength
  split <;> omega

theorem paired_readers_long (a : ZMod k) (b : ℕ) {l : ℕ} (hl : l < k - 1) :
    inputLength b l (a, false) a = b + 1 ∧
      inputLength b l (a, false) (rightReader a l) = b + 1 := by
  constructor
  · simp [inputLength, self_not_mem_interval a (l := l) (by omega)]
  · simp [inputLength, rightReader_not_mem_interval a (l := l) (by omega)]

theorem shared_card (a z : ZMod k) (h : a ≠ z) : Fintype.card (Shared a z) = k - 2 := by
  have hc := Fintype.card_congr (readerPartiesEquiv a z h)
  simp only [ZMod.card, Fintype.card_sum, Fintype.card_bool] at hc
  omega

theorem shared_degree_bound (a z : ZMod k) (h : a ≠ z) (b l : ℕ) (t : Token k) :
    (∑ p : Shared a z, (inputLength b l t p.val - 1)) ≤ (k - 2) * b := by
  calc
    (∑ p : Shared a z, (inputLength b l t p.val - 1)) ≤ ∑ _p : Shared a z, b := by
      apply Finset.sum_le_sum
      intro p _
      have := inputLength_le b l t p.val
      omega
    _ = (k - 2) * b := by simp [shared_card a z h]

theorem packing_condition (a z : ZMod k) (h : a ≠ z) (b l : ℕ) (t : Token k) :
    (∑ p : Shared a z, (inputLength b l t p.val - 1)) + 2 * b ≤ k * b := by
  have hs := shared_degree_bound a z h b l t
  have hk : 2 ≤ k := by
    have hc := Fintype.card_congr (readerPartiesEquiv a z h)
    simp only [ZMod.card, Fintype.card_sum, Fintype.card_bool] at hc
    omega
  calc
    (∑ p : Shared a z, (inputLength b l t p.val - 1)) + 2 * b ≤ (k - 2) * b + 2 * b :=
      Nat.add_le_add_right hs _
    _ = k * b := by rw [← Nat.add_mul, Nat.sub_add_cancel hk]

/-- Every ordered pair occurs at exactly one reader step. -/
def orderedReadersEquiv : ReaderStep k ≃ OrderedReaders k where
  toFun s := ⟨(s.1, rightReader s.1 s.2.val), readers_distinct s.1 s.2.isLt⟩
  invFun r := (r.val.1, ⟨(r.val.2 - r.val.1).val - 1, by
    have hd : 0 < (r.val.2 - r.val.1).val := by
      by_contra hn
      have hz : (r.val.2 - r.val.1).val = 0 := by omega
      have he : r.val.2 - r.val.1 = 0 := by
        rw [← ZMod.natCast_zmod_val (r.val.2 - r.val.1), hz]
        simp
      exact r.property (sub_eq_zero.mp he).symm
    have := ZMod.val_lt (r.val.2 - r.val.1)
    omega⟩)
  left_inv := by
    rintro ⟨a, l⟩
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change (rightReader a l.val - a).val - 1 = l.val
      have he : rightReader a l.val - a = ((l.val + 1 : ℕ) : ZMod k) := by
        unfold rightReader
        abel
      rw [he, ZMod.val_natCast_of_lt (by have := l.isLt; omega)]
      omega
  right_inv := by
    intro r
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change rightReader r.val.1 ((r.val.2 - r.val.1).val - 1) = r.val.2
      have hd : 0 < (r.val.2 - r.val.1).val := by
        by_contra hn
        have hz : (r.val.2 - r.val.1).val = 0 := by omega
        have he : r.val.2 - r.val.1 = 0 := by
          rw [← ZMod.natCast_zmod_val (r.val.2 - r.val.1), hz]
          simp
        exact r.property (sub_eq_zero.mp he).symm
      unfold rightReader
      rw [Nat.sub_add_cancel hd, ZMod.natCast_zmod_val]
      abel

def edgeSteps (a z : ZMod k) (h : a ≠ z) : Finset (ReaderStep k) :=
  {orderedReadersEquiv.symm ⟨(a, z), h⟩, orderedReadersEquiv.symm ⟨(z, a), h.symm⟩}

theorem mem_edgeSteps (a z : ZMod k) (h : a ≠ z) (s : ReaderStep k) :
    s ∈ edgeSteps a z h ↔
      (orderedReadersEquiv s).val = (a, z) ∨ (orderedReadersEquiv s).val = (z, a) := by
  simp only [edgeSteps, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (hs | hs)
    · left
      rw [hs, Equiv.apply_symm_apply]
    · right
      rw [hs, Equiv.apply_symm_apply]
  · rintro (hs | hs)
    · left
      exact (Equiv.eq_symm_apply _).mpr (Subtype.ext hs)
    · right
      exact (Equiv.eq_symm_apply _).mpr (Subtype.ext hs)

/-- An unordered physical edge appears in precisely two stages and orientations. -/
theorem edgeSteps_card (a z : ZMod k) (h : a ≠ z) : (edgeSteps a z h).card = 2 := by
  have he : orderedReadersEquiv.symm ⟨(a, z), h⟩ ≠
      orderedReadersEquiv.symm ⟨(z, a), h.symm⟩ := by
    intro he
    have hv := congrArg (fun r : OrderedReaders k => r.val.1)
      (orderedReadersEquiv.symm.injective he)
    exact h hv
  simp [edgeSteps, he]

end Lemmata.TensorRank.CyclicSchedule
