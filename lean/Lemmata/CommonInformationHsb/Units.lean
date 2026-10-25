module

public import Lemmata.CommonInformationHsb.Factorization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace Lemmata.CommonInformationHsb

open Lemmata.SpanningTreeMinSplit
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Converting bits back to an exponential recovers the natural-log objective. -/
theorem two_rpow_commonInformation (M : I → J → ℝ) :
    (2 : ℝ) ^ commonInformation M = Real.exp (commonInformationNat M) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  unfold commonInformation
  rw [mul_div_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num)))]

/-- A natural-log bound gives the corresponding numerical rank-bound ceiling. -/
theorem two_rpow_commonInformation_le_of_nat_le_log {M : I → J → ℝ} {b : ℝ}
    (hb : 0 < b) (h : commonInformationNat M ≤ Real.log b) :
    (2 : ℝ) ^ commonInformation M ≤ b := by
  rw [two_rpow_commonInformation]
  exact (Real.exp_le_exp.mpr h).trans_eq (Real.exp_log hb)

/-- A nonzero matrix cannot have an empty factor index. -/
theorem factor_count_pos {M : I → J → ℝ} {k : ℕ}
    (F : NonnegativeFactorization M k) (hmass : 0 < matrixMass M) : 0 < k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst k
  have hzero : matrixMass M = 0 := by
    simp only [matrixMass, F.reconstruct, Finset.univ_eq_empty, Finset.sum_empty,
      Finset.sum_const_zero]
  linarith

/-- Every finite nonnegative factorization bounds common information in bits. -/
theorem commonInformation_le_log_factor_count {M : I → J → ℝ} {k : ℕ}
    (F : NonnegativeFactorization M k) (hmass : 0 < matrixMass M) :
    commonInformation M ≤ Real.log k / Real.log 2 :=
  div_le_div_of_nonneg_right (commonInformationNat_le_log_factor_count F hmass)
    (Real.log_nonneg (by norm_num))

/-- The exponentiated common-information quantity is a lower bound on each
actual nonnegative factorization's size. -/
theorem two_rpow_commonInformation_le_factor_count {M : I → J → ℝ} {k : ℕ}
    (F : NonnegativeFactorization M k) (hmass : 0 < matrixMass M) :
    (2 : ℝ) ^ commonInformation M ≤ (k : ℝ) :=
  two_rpow_commonInformation_le_of_nat_le_log
    (by exact_mod_cast factor_count_pos F hmass)
    (commonInformationNat_le_log_factor_count F hmass)

/-- The published extended-natural nonnegative rank is finite and attained;
its finite value bounds the common-information lower-bound quantity. -/
theorem commonInformation_rank_bound {M : I → J → ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hmass : 0 < matrixMass M) :
    ∃ k : ℕ, 0 < k ∧ nonnegativeRank M = (k : ℕ∞) ∧
      (2 : ℝ) ^ commonInformation M ≤ (k : ℝ) := by
  obtain ⟨k, hk, ⟨F⟩⟩ := nonnegativeRank_attained hM
  exact ⟨k, factor_count_pos F hmass, hk, two_rpow_commonInformation_le_factor_count F hmass⟩

end Lemmata.CommonInformationHsb
