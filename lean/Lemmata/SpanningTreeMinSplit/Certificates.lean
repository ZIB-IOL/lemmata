module

public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.SpanningTreeMinSplit

/-- Certificates form a square above each root. Diagonal markers encode a
parent below the root; off-diagonal markers encode the parent itself. -/
abbrev Cert (n : ℕ) : Type := Σ r : Fin n, {x : Fin n // r < x} × {x : Fin n // r < x}

variable {n : ℕ}

/-- The row condition depends only on the set and its minimum. -/
def RowFires (c : Cert n) (S : Finset (Fin n)) (hS : S.Nonempty) : Prop :=
  S.min' hS = c.1 ∧ c.2.1.1 ∈ S ∧ (c.2.2.1 ≠ c.2.1.1 → c.2.2.1 ∉ S)

/-- The column condition is defined for any parent function. -/
def ColFires (c : Cert n) (p : Fin n → Fin n) : Prop :=
  if c.2.2.1 = c.2.1.1 then p c.2.1.1 < c.1 else p c.2.1.1 = c.2.2.1

/-- A certificate fires when both its row and column conditions hold. -/
def Fires (c : Cert n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (p : Fin n → Fin n) : Prop :=
  RowFires c S hS ∧ ColFires c p

instance (c : Cert n) (S : Finset (Fin n)) (hS : S.Nonempty) :
    Decidable (RowFires c S hS) := by unfold RowFires; infer_instance

instance (c : Cert n) (p : Fin n → Fin n) : Decidable (ColFires c p) := by
  unfold ColFires; infer_instance

instance (c : Cert n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (p : Fin n → Fin n) : Decidable (Fires c S hS p) := by
  unfold Fires; infer_instance

/-- The zero-one row factor. -/
def rowFactor (c : Cert n) (S : Finset (Fin n)) (hS : S.Nonempty) : ℝ :=
  if RowFires c S hS then 1 else 0

/-- The zero-one parent-function factor. -/
def parentFactor (c : Cert n) (p : Fin n → Fin n) : ℝ :=
  if ColFires c p then 1 else 0

/-- Every vertex other than the minimum whose parent leaves the set has
exactly one firing certificate. No tree hypotheses are required. -/
theorem splits_eq_fired_card (S : Finset (Fin n)) (hS : S.Nonempty)
    (p : Fin n → Fin n) :
    (S.filter (fun u => u ≠ S.min' hS ∧ p u ∉ S)).card =
      (Finset.univ.filter (fun c : Cert n => Fires c S hS p)).card := by
  classical
  have hvlt : ∀ v, v ∈ S.filter (fun u => u ≠ S.min' hS ∧ p u ∉ S) →
      S.min' hS < v := by
    intro v hv
    obtain ⟨hvS, hne, -⟩ :
        v ∈ S ∧ v ≠ S.min' hS ∧ p v ∉ S := by
      have h := Finset.mem_filter.mp hv; exact ⟨h.1, h.2.1, h.2.2⟩
    exact lt_of_le_of_ne (S.min'_le v hvS) (Ne.symm hne)
  have htlt : ∀ v, v ∈ S.filter (fun u => u ≠ S.min' hS ∧ p u ∉ S) →
      ¬ p v < S.min' hS → S.min' hS < p v := by
    intro v hv h
    obtain ⟨-, -, hpar⟩ :
        v ∈ S ∧ v ≠ S.min' hS ∧ p v ∉ S := by
      have h := Finset.mem_filter.mp hv; exact ⟨h.1, h.2.1, h.2.2⟩
    exact lt_of_le_of_ne (le_of_not_gt h)
      (fun heq => hpar (heq ▸ S.min'_mem hS))
  apply Finset.card_bij
    (i := fun v hv => (⟨S.min' hS,
      (⟨v, hvlt v hv⟩,
       if h : p v < S.min' hS then ⟨v, hvlt v hv⟩
       else ⟨p v, htlt v hv h⟩)⟩ : Cert n))
  · intro v hv
    obtain ⟨hvS, _, hpar⟩ :
        v ∈ S ∧ v ≠ S.min' hS ∧ p v ∉ S := by
      have h := Finset.mem_filter.mp hv; exact ⟨h.1, h.2.1, h.2.2⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_cases h : p v < S.min' hS
    · rw [dite_eq_left h]
      refine ⟨⟨rfl, hvS, fun hne => absurd rfl hne⟩, ?_⟩
      simpa [ColFires] using h
    · rw [dite_eq_right h]
      have htne : p v ≠ v := fun heq => hpar (heq.symm ▸ hvS)
      refine ⟨⟨rfl, hvS, fun _ => hpar⟩, ?_⟩
      simp [ColFires, htne]
  · intro v₁ hv₁ v₂ hv₂ heq
    have := congrArg (fun c : Cert n => c.2.1.1) heq
    simpa using this
  · intro c hc
    have hf : Fires c S hS p := (Finset.mem_filter.mp hc).2
    obtain ⟨r, ⟨v, hrv⟩, ⟨w, hrw⟩⟩ := c
    obtain ⟨⟨hr, hvS, hwS⟩, hcol⟩ := hf
    dsimp only at hr hvS hwS hcol
    subst hr
    have hvne : v ≠ S.min' hS := ne_of_gt hrv
    unfold ColFires at hcol
    dsimp only at hcol
    by_cases hwv : w = v
    · rw [ite_eq_left hwv] at hcol
      have hparS : p v ∉ S := fun hmem =>
        absurd (S.min'_le _ hmem) (not_le.mpr hcol)
      have hsplit : v ∈ S.filter (fun u => u ≠ S.min' hS ∧ p u ∉ S) :=
        Finset.mem_filter.mpr ⟨hvS, hvne, hparS⟩
      refine ⟨v, hsplit, ?_⟩
      simp only [dite_eq_left hcol, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq,
        Subtype.mk.injEq, true_and]
      exact hwv.symm
    · rw [ite_eq_right hwv] at hcol
      have hparS : p v ∉ S := hcol ▸ hwS hwv
      have hsplit : v ∈ S.filter (fun u => u ≠ S.min' hS ∧ p u ∉ S) :=
        Finset.mem_filter.mpr ⟨hvS, hvne, hparS⟩
      refine ⟨v, hsplit, ?_⟩
      have hnlt : ¬ p v < S.min' hS := by
        rw [hcol]
        exact not_lt.mpr (le_of_lt hrw)
      simp only [dite_eq_right hnlt, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq,
        Subtype.mk.injEq, true_and]
      exact hcol

/-- The min-split entry decomposes into row and parent factors, for an
arbitrary family of parent maps indexed by the root. -/
theorem split_sum_eq_factors (S : Finset (Fin n)) (hS : S.Nonempty)
    (p : Fin n → Fin n → Fin n) :
    (∑ v ∈ S.erase (S.min' hS), if p (S.min' hS) v ∉ S then (1 : ℝ) else 0) =
      ∑ c : Cert n, rowFactor c S hS * parentFactor c (p c.1) := by
  classical
  have hpt : ∀ c : Cert n,
      rowFactor c S hS * parentFactor c (p c.1) =
      if Fires c S hS (p (S.min' hS)) then (1 : ℝ) else 0 := by
    intro c
    unfold rowFactor parentFactor
    by_cases hr : RowFires c S hS
    · have hroot : c.1 = S.min' hS := hr.1.symm
      rw [ite_eq_left hr, one_mul, hroot]
      by_cases hc : ColFires c (p (S.min' hS))
      · rw [ite_eq_left hc, ite_eq_left ⟨hr, hc⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun hf => hc hf.2)]
    · rw [ite_eq_right hr, zero_mul, ite_eq_right (fun hf => hr hf.1)]
  have hfilter : (S.erase (S.min' hS)).filter (fun v => p (S.min' hS) v ∉ S) =
      S.filter (fun u => u ≠ S.min' hS ∧ p (S.min' hS) u ∉ S) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  calc
    _ = ((S.filter (fun u => u ≠ S.min' hS ∧ p (S.min' hS) u ∉ S)).card : ℝ) := by
      rw [Finset.sum_boole, hfilter]
    _ = ((Finset.univ.filter (fun c : Cert n => Fires c S hS (p (S.min' hS)))).card : ℝ) := by
      rw [splits_eq_fired_card S hS]
    _ = ∑ c : Cert n, if Fires c S hS (p (S.min' hS)) then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
    _ = _ := (Finset.sum_congr rfl (fun c _ => hpt c)).symm

private lemma six_mul_sum_sq :
    ∀ n : ℕ, 6 * ∑ k ∈ Finset.range n, k ^ 2 = n * (n - 1) * (2 * n - 1)
  | 0 => by simp
  | (m + 1) => by
      rw [Finset.sum_range_succ, Nat.mul_add, six_mul_sum_sq m]
      rcases m with _ | k
      · simp
      · have h1 : (k + 1 + 1) - 1 = k + 1 := rfl
        have h2 : 2 * (k + 1 + 1) - 1 = 2 * k + 3 := by omega
        have h3 : (k + 1) - 1 = k := rfl
        have h4 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [h1, h2, h3, h4]
        ring

/-- Six times the number of certificates is the sum-of-squares numerator. -/
theorem six_mul_card_cert (n : ℕ) :
    6 * Fintype.card (Cert n) = n * (n - 1) * (2 * n - 1) := by
  classical
  have hcard : Fintype.card (Cert n) = ∑ r : Fin n, (n - 1 - r.1) ^ 2 := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro r _
    rw [Fintype.card_prod]
    have hsub : Fintype.card {x : Fin n // r < x} = n - 1 - r.1 := by
      rw [Fintype.card_subtype]
      have : Finset.filter (fun x : Fin n => r < x) Finset.univ
          = Finset.Ioi r := by
        ext x; simp [Finset.mem_Ioi]
      rw [this, Fin.card_Ioi]
    rw [hsub, sq]
  rw [hcard, Fin.sum_univ_eq_sum_range (fun k => (n - 1 - k) ^ 2) n,
    Finset.sum_range_reflect (fun k => k ^ 2) n, six_mul_sum_sq n]

/-- Exact certificate count, including the empty sizes zero and one. -/
theorem card_cert (n : ℕ) :
    Fintype.card (Cert n) = n * (n - 1) * (2 * n - 1) / 6 := by
  rw [← six_mul_card_cert n]
  omega

end Lemmata.SpanningTreeMinSplit
