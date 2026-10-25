module

public import Lemmata.CommonInformationHsb.CommonInformation
public import Lemmata.SpanningTreeMinSplit.Main
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Normalize a nonnegative vector, with a uniform fallback for a zero vector. -/
noncomputable def normalizeVector (p : I → ℝ) (i : I) : ℝ :=
  if ∑ j, p j = 0 then (Fintype.card I : ℝ)⁻¹ else p i / ∑ j, p j

theorem normalizeVector_probability [Nonempty I] {p : I → ℝ}
    (hp : ∀ i, 0 ≤ p i) : IsProbability (normalizeVector p) := by
  classical
  by_cases hs : ∑ i, p i = 0
  · simp [IsProbability, normalizeVector, hs, Fintype.card_ne_zero]
  · have hpos : 0 < ∑ i, p i := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => hp i)) (Ne.symm hs)
    simpa [IsProbability, normalizeVector, hs] using isProbability_div_sum hp hpos

theorem sum_mul_normalizeVector {p : I → ℝ} (hp : ∀ i, 0 ≤ p i) (i : I) :
    (∑ j, p j) * normalizeVector p i = p i := by
  classical
  by_cases hs : ∑ j, p j = 0
  · have hi : p i = 0 := le_antisymm (by
      simpa [hs] using Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)) (hp i)
    simp [normalizeVector, hs, hi]
  · simpa only [normalizeVector, ite_eq_right hs] using mul_div_cancel₀ (p i) hs

theorem factor_mass {M : I → J → ℝ} {k : ℕ} (F : NonnegativeFactorization M k) :
    ∑ z, (∑ i, F.left z i) * (∑ j, F.right z j) = matrixMass M := by
  calc
    _ = ∑ z, ∑ i, ∑ j, F.left z i * F.right z j := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ z, F.left z i * F.right z j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = matrixMass M := by simp only [matrixMass, F.reconstruct]

/-- The seed induced by an arbitrary nonnegative factorization; zero factors are retained. -/
noncomputable def factorSeed [Nonempty I] [Nonempty J] {M : I → J → ℝ} {k : ℕ}
    (F : NonnegativeFactorization M k) (hmass : 0 < matrixMass M) :
    ProductSeed (normalize M) k where
  weight z := (∑ i, F.left z i) * (∑ j, F.right z j) / matrixMass M
  left z := normalizeVector (F.left z)
  right z := normalizeVector (F.right z)
  weight_prob := ⟨fun z => div_nonneg (mul_nonneg
    (Finset.sum_nonneg (fun i _ => F.left_nonneg z i))
    (Finset.sum_nonneg (fun j _ => F.right_nonneg z j))) hmass.le,
    by rw [← Finset.sum_div, factor_mass F, div_self hmass.ne']⟩
  left_prob z := normalizeVector_probability (F.left_nonneg z)
  right_prob z := normalizeVector_probability (F.right_nonneg z)
  reconstruct i j := by
    simp only [normalize, F.reconstruct, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    have hl := sum_mul_normalizeVector (F.left_nonneg z) i
    have hr := sum_mul_normalizeVector (F.right_nonneg z) j
    rw [← hl, ← hr]
    ring

/-- Every finite nonnegative factorization bounds genuine common information. -/
theorem commonInformationNat_le_log_factor_count {M : I → J → ℝ} {k : ℕ}
    (F : NonnegativeFactorization M k) (hmass : 0 < matrixMass M) :
    commonInformationNat M ≤ Real.log k := by
  have hp := isProbability_normalize F.nonneg hmass
  have hne : Nonempty (I × J) := hp.nonempty
  let : Nonempty I := ⟨(Classical.choice hne).1⟩
  let : Nonempty J := ⟨(Classical.choice hne).2⟩
  let s := factorSeed F hmass
  exact (commonInformationNat_le_cost s).trans
    (s.cost_le_entropy_weight.trans (by simpa using entropy_le_log_card s.weight_prob))

omit [Fintype I] in
/-- Finite nonnegative matrices always have a finite factorization (one per column). -/
theorem finite_nonnegativeFactorization {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    Nonempty (NonnegativeFactorization M (Fintype.card J)) := by
  classical
  refine ⟨{
    left := fun z i => M i ((Fintype.equivFin J).symm z)
    right := fun z j => if j = (Fintype.equivFin J).symm z then 1 else 0
    left_nonneg := fun z i => hM i _
    right_nonneg := fun z j => by split_ifs <;> norm_num
    reconstruct := ?_ }⟩
  intro i j
  rw [(Fintype.equivFin J).symm.sum_comp
    (fun x => M i x * (if j = x then 1 else 0))]
  simp [mul_ite]

omit [Fintype I] in
/-- The published nonnegative rank is attained, rather than merely an infimum. -/
theorem nonnegativeRank_attained {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    ∃ k : ℕ, nonnegativeRank M = k ∧ Nonempty (NonnegativeFactorization M k) := by
  have hne : ({r : ℕ∞ | ∃ k : ℕ, r = k ∧ Nonempty (NonnegativeFactorization M k)}).Nonempty :=
    ⟨Fintype.card J, Fintype.card J, rfl, finite_nonnegativeFactorization hM⟩
  exact csInf_mem hne

/-- In particular, common information is bounded by the logarithm of nonnegative rank. -/
theorem commonInformationNat_le_log_nonnegativeRank {M : I → J → ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hmass : 0 < matrixMass M) {k : ℕ}
    (hk : nonnegativeRank M = k) : commonInformationNat M ≤ Real.log k := by
  obtain ⟨r, hr, ⟨F⟩⟩ := nonnegativeRank_attained hM
  have he : r = k := by exact_mod_cast hr.symm.trans hk
  subst r
  exact commonInformationNat_le_log_factor_count F hmass

end Lemmata.CommonInformationHsb
