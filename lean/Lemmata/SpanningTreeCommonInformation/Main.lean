module

public import Lemmata.SpanningTreeCommonInformation.Ceiling

@[expose] public section

namespace Lemmata.SpanningTreeCommonInformation

open Lemmata.SpanningTreeMinSplit Lemmata.CommonInformationHsb
open scoped BigOperators

/-- A reusable bit-valued cap for a sum of unit Boolean rectangles. -/
theorem flat_factor_bound {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {M : I → J → ℝ} (a : K → I → Bool) (b : K → J → Bool)
    (hM : ∀ i j, M i j = ∑ z, (if a z i then 1 else 0) * (if b z j then 1 else 0))
    (hmass : 0 < matrixMass M) :
    commonInformation M ≤ Real.log
      ((Fintype.card K : ℝ) * Fintype.card I * Fintype.card J / matrixMass M) / Real.log 2 :=
  div_le_div_of_nonneg_right (commonInformationNat_le_boolean_rectangles a b hM hmass)
    (Real.log_nonneg (by norm_num))

/-- The published full matrix is exactly a sum of unit Boolean rectangles on
its unchanged certificate index, including the reused edge slots. -/
theorem full_flat_factorization (n : ℕ) (hn : 3 ≤ n) :
    ∃ a : Cert n → Row n → Bool, ∃ b : Cert n → Tree n → Bool,
      (∀ R T, fullSlack n R T = ∑ c : Cert n,
        (if a c R then (1 : ℝ) else 0) * (if b c T then (1 : ℝ) else 0)) ∧
      Fintype.card (Cert n) = n * (n - 1) * (2 * n - 1) / 6 := by
  let : NeZero n := ⟨by omega⟩
  exact ⟨rowWitness, columnWitness, fullSlack_boolean_rectangles, card_cert n⟩

/-- Per-column masses for the two canonical row families, without enumerating trees. -/
theorem column_masses (n : ℕ) (hn : 3 ≤ n) (T : Tree n) :
    (∑ S : Subtour n, subtourMatrix n S T) =
        ((n : ℝ) - 3) * 2 ^ (n - 2) + 1 ∧
      (∑ R : Row n, fullSlack n R T) =
        ((n : ℝ) - 3) * 2 ^ (n - 2) + n :=
  ⟨sum_subtourSlack T hn, sum_fullSlack T hn⟩

-- DOCS_BEGIN_MAIN
/-- A quadratic ceiling on the CI lower-bound quantity for the full canonical slack. -/
theorem full_ci_ceiling (n : ℕ) (hn : 3 ≤ n) :
    commonInformation (fullSlack n) ≤ 2 * Real.log (n : ℝ) / Real.log 2 + 2 ∧
      (2 : ℝ) ^ commonInformation (fullSlack n) ≤ 4 * (n : ℝ) ^ 2 :=
  ⟨commonInformation_full_bound n hn, two_rpow_commonInformation_full_bound n hn⟩

/-- The same ceiling for the proper subtour rows alone. -/
theorem subtour_ci_ceiling (n : ℕ) (hn : 3 ≤ n) :
    commonInformation (subtourMatrix n) ≤ 2 * Real.log (n : ℝ) / Real.log 2 + 2 ∧
      (2 : ℝ) ^ commonInformation (subtourMatrix n) ≤ 4 * (n : ℝ) ^ 2 :=
  ⟨commonInformation_subtour_bound n hn, two_rpow_commonInformation_subtour_bound n hn⟩
-- DOCS_END_MAIN

end Lemmata.SpanningTreeCommonInformation
