module

public import Lemmata.CommonInformationHsb.Factorization

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- The entropy contribution of one Boolean rectangle, including an empty rectangle. -/
theorem flat_component_entropy (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, a i = 0 ∨ a i = 1) (hb : ∀ j, b j = 0 ∨ b j = 1)
    {m : ℝ} (hm : 0 < m) :
    let w := (∑ i, a i) * (∑ j, b j) / m
    w * (entropy (normalizeVector a) + entropy (normalizeVector b)) =
      w * Real.log m - Real.negMulLog w := by
  dsimp only
  by_cases hA : ∑ i, a i = 0
  · simp [hA]
  by_cases hB : ∑ j, b j = 0
  · simp [hB]
  have hAp : 0 < ∑ i, a i := lt_of_le_of_ne
    (Finset.sum_nonneg (fun i _ => by rcases ha i with h | h <;> simp [h])) (Ne.symm hA)
  have hBp : 0 < ∑ j, b j := lt_of_le_of_ne
    (Finset.sum_nonneg (fun j _ => by rcases hb j with h | h <;> simp [h])) (Ne.symm hB)
  have ea : normalizeVector a = (fun i => a i / ∑ j, a j) := by
    funext i
    simp [normalizeVector, hA]
  have eb : normalizeVector b = (fun i => b i / ∑ j, b j) := by
    funext i
    simp [normalizeVector, hB]
  rw [ea, eb, entropy_normalize_boolean ha hAp, entropy_normalize_boolean hb hBp]
  rw [Real.negMulLog, Real.log_div (mul_ne_zero hA hB) hm.ne', Real.log_mul hA hB]
  ring

/-- The rectangle witness cost, not a redefinition of the common-information infimum. -/
theorem factorSeed_cost_flat [Nonempty I] [Nonempty J]
    {M : I → J → ℝ} {k : ℕ} (F : NonnegativeFactorization M k)
    (hmass : 0 < matrixMass M)
    (hl : ∀ z i, F.left z i = 0 ∨ F.left z i = 1)
    (hr : ∀ z j, F.right z j = 0 ∨ F.right z j = 1) :
    (factorSeed F hmass).cost = entropy (Function.uncurry (normalize M)) -
      Real.log (matrixMass M) + entropy (factorSeed F hmass).weight := by
  let s := factorSeed F hmass
  have ht (z : Fin k) : s.weight z * (entropy (s.left z) + entropy (s.right z)) =
      s.weight z * Real.log (matrixMass M) - Real.negMulLog (s.weight z) :=
    flat_component_entropy (F.left z) (F.right z) (hl z) (hr z) hmass
  change s.cost = _
  unfold ProductSeed.cost
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, s.weight_prob.2, one_mul]
  change entropy (Function.uncurry (normalize M)) -
      (Real.log (matrixMass M) - entropy s.weight) = _
  ring

/-- Generic flat-factor cap, derived from a witness inside the unrestricted infimum. -/
theorem commonInformationNat_le_flat_factor_cap
    {M : I → J → ℝ} {k : ℕ} (F : NonnegativeFactorization M k)
    (hmass : 0 < matrixMass M)
    (hl : ∀ z i, F.left z i = 0 ∨ F.left z i = 1)
    (hr : ∀ z j, F.right z j = 0 ∨ F.right z j = 1) :
    commonInformationNat M ≤
      Real.log ((k : ℝ) * Fintype.card I * Fintype.card J / matrixMass M) := by
  have hp := isProbability_normalize F.nonneg hmass
  have hne : Nonempty (I × J) := hp.nonempty
  let : Nonempty I := ⟨(Classical.choice hne).1⟩
  let : Nonempty J := ⟨(Classical.choice hne).2⟩
  let s := factorSeed F hmass
  have hseed : Nonempty (Fin k) := s.weight_prob.nonempty
  have hk : (k : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin k) := Fintype.card_pos
    exact_mod_cast (by simpa using this : 0 < k).ne'
  have hI : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJ : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he := entropy_le_log_card hp
  have hw := entropy_le_log_card s.weight_prob
  have hcost := factorSeed_cost_flat F hmass hl hr
  have hlogs : Real.log ((k : ℝ) * Fintype.card I * Fintype.card J / matrixMass M) =
      Real.log (Fintype.card (I × J)) - Real.log (matrixMass M) + Real.log k := by
    rw [Real.log_div (mul_ne_zero (mul_ne_zero hk hI) hJ) hmass.ne',
      Real.log_mul (mul_ne_zero hk hI) hJ, Real.log_mul hk hI]
    simp only [Fintype.card_prod, Nat.cast_mul, Real.log_mul hI hJ]
    ring
  rw [hlogs]
  have hu := commonInformationNat_le_cost s
  simp only [Fintype.card_fin] at hw
  dsimp only [s] at hu hw
  linarith

/-- The same bound for Boolean-valued factors indexed by any finite type. -/
theorem commonInformationNat_le_flat_cap
    {M : I → J → ℝ} (a : K → I → ℝ) (b : K → J → ℝ)
    (ha : ∀ z i, a z i = 0 ∨ a z i = 1)
    (hb : ∀ z j, b z j = 0 ∨ b z j = 1)
    (hM : ∀ i j, M i j = ∑ z, a z i * b z j)
    (hmass : 0 < matrixMass M) :
    commonInformationNat M ≤ Real.log
      ((Fintype.card K : ℝ) * Fintype.card I * Fintype.card J / matrixMass M) := by
  let F : NonnegativeFactorization M (Fintype.card K) := {
    left := fun z => a ((Fintype.equivFin K).symm z)
    right := fun z => b ((Fintype.equivFin K).symm z)
    left_nonneg := fun z i => by rcases ha ((Fintype.equivFin K).symm z) i with h | h <;> simp [h]
    right_nonneg := fun z j => by rcases hb ((Fintype.equivFin K).symm z) j with h | h <;> simp [h]
    reconstruct := fun i j => by
      rw [(Fintype.equivFin K).symm.sum_comp (fun z => a z i * b z j)]
      exact hM i j }
  exact commonInformationNat_le_flat_factor_cap F hmass
    (fun z i => ha _ i) (fun z j => hb _ j)

/-- A Boolean rectangle presentation need not omit its empty rectangles. -/
theorem commonInformationNat_le_boolean_rectangles
    {M : I → J → ℝ} (a : K → I → Bool) (b : K → J → Bool)
    (hM : ∀ i j, M i j = ∑ z, (if a z i then 1 else 0) * (if b z j then 1 else 0))
    (hmass : 0 < matrixMass M) :
    commonInformationNat M ≤ Real.log
      ((Fintype.card K : ℝ) * Fintype.card I * Fintype.card J / matrixMass M) := by
  apply commonInformationNat_le_flat_cap
    (fun z i => if a z i then 1 else 0) (fun z j => if b z j then 1 else 0)
    (fun z i => ?_) (fun z j => ?_) hM hmass
  · cases a z i <;> simp
  · cases b z j <;> simp

end Lemmata.CommonInformationHsb
