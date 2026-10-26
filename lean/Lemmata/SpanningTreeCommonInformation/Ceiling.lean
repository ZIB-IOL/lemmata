module

public import Lemmata.CommonInformationHsb.Main
public import Lemmata.SpanningTreeCommonInformation.ColumnMass
public import Lemmata.SpanningTreeCommonInformation.Flatness
public import Lemmata.SpanningTreeCommonInformation.Arithmetic

@[expose] public section

namespace Lemmata.SpanningTreeCommonInformation

open Lemmata.SpanningTreeMinSplit Lemmata.CommonInformationHsb
open scoped BigOperators Classical
noncomputable section

/-- Restriction of the actual graph slack to the proper subtour rows. -/
def subtourMatrix (n : ℕ) (S : Subtour n) (T : Tree n) : ℝ := subtourSlack T S.val

/-- Nonnegativity of the actual full matrix is inherited from the published proof. -/
theorem fullSlack_nonneg (n : ℕ) (hn : 3 ≤ n) (R : Row n) (T : Tree n) :
    0 ≤ fullSlack n R T := fullSlack_nonnegative n hn R T

/-- Nonnegativity also holds after restricting to the subtour rows. -/
theorem subtourMatrix_nonneg (n : ℕ) (hn : 3 ≤ n) (S : Subtour n) (T : Tree n) :
    0 ≤ subtourMatrix n S T := fullSlack_nonnegative n hn (.inl S) T

/-- Total full slack mass, retaining the actual finite number of tree columns. -/
theorem fullSlack_mass (n : ℕ) (hn : 3 ≤ n) :
    matrixMass (fullSlack n) = (Fintype.card (Tree n) : ℝ) *
      (((n : ℝ) - 3) * 2 ^ (n - 2) + n) := by
  unfold matrixMass
  rw [Finset.sum_comm]
  simp_rw [sum_fullSlack _ hn]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Total subtour slack mass, without a formula for the number of trees. -/
theorem subtourMatrix_mass (n : ℕ) (hn : 3 ≤ n) :
    matrixMass (subtourMatrix n) = (Fintype.card (Tree n) : ℝ) *
      (((n : ℝ) - 3) * 2 ^ (n - 2) + 1) := by
  unfold matrixMass
  rw [Finset.sum_comm]
  simp_rw [subtourMatrix, sum_subtourSlack _ hn]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Every full column has strictly positive mass in the stated range. -/
theorem fullColumnMass_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < ((n : ℝ) - 3) * 2 ^ (n - 2) + n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : 0 ≤ ((n : ℝ) - 3) * 2 ^ (n - 2) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

/-- Every subtour column also has strictly positive mass, including n=3. -/
theorem subtourColumnMass_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < ((n : ℝ) - 3) * 2 ^ (n - 2) + 1 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : 0 ≤ ((n : ℝ) - 3) * 2 ^ (n - 2) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

/-- Actual tree columns exist (for example the labelled path), so their count is positive. -/
theorem card_tree_pos (n : ℕ) (hn : 3 ≤ n) : 0 < (Fintype.card (Tree n) : ℝ) := by
  let : NeZero n := ⟨by omega⟩
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Tree n))

/-- The full matrix has positive total mass, without assuming a tree count. -/
theorem fullSlack_mass_pos (n : ℕ) (hn : 3 ≤ n) : 0 < matrixMass (fullSlack n) := by
  rw [fullSlack_mass n hn]
  exact mul_pos (card_tree_pos n hn) (fullColumnMass_pos n hn)

/-- The subtour matrix has positive total mass. -/
theorem subtourMatrix_mass_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < matrixMass (subtourMatrix n) := by
  rw [subtourMatrix_mass n hn]
  exact mul_pos (card_tree_pos n hn) (subtourColumnMass_pos n hn)

/-- Cancel the actual number of full-matrix columns; no Cayley formula is needed. -/
theorem fullSlack_flat_ratio (n : ℕ) (hn : 3 ≤ n) :
    (Fintype.card (Cert n) : ℝ) * Fintype.card (Row n) * Fintype.card (Tree n) /
        matrixMass (fullSlack n) =
      (Fintype.card (Cert n) : ℝ) * Fintype.card (Row n) /
        (((n : ℝ) - 3) * 2 ^ (n - 2) + n) := by
  rw [fullSlack_mass n hn, mul_comm (Fintype.card (Tree n) : ℝ)]
  exact mul_div_mul_right _ _ (card_tree_pos n hn).ne'

/-- The same exact tree-count cancellation for the subtour matrix. -/
theorem subtourMatrix_flat_ratio (n : ℕ) (hn : 3 ≤ n) :
    (Fintype.card (Cert n) : ℝ) * Fintype.card (Subtour n) * Fintype.card (Tree n) /
        matrixMass (subtourMatrix n) =
      (Fintype.card (Cert n) : ℝ) * Fintype.card (Subtour n) /
        (((n : ℝ) - 3) * 2 ^ (n - 2) + 1) := by
  rw [subtourMatrix_mass n hn, mul_comm (Fintype.card (Tree n) : ℝ)]
  exact mul_div_mul_right _ _ (card_tree_pos n hn).ne'

/-- The unchanged certificate type has positive size in the nontrivial range. -/
theorem card_cert_pos (n : ℕ) (hn : 3 ≤ n) : 0 < (Fintype.card (Cert n) : ℝ) := by
  rw [card_cert_real n (by omega)]
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by norm_num)

/-- Natural-log common-information ceiling for the actual full spanning-tree slack. -/
theorem commonInformationNat_full_bound (n : ℕ) (hn : 3 ≤ n) :
    commonInformationNat (fullSlack n) ≤ Real.log (4 * (n : ℝ) ^ 2) := by
  let : NeZero n := ⟨by omega⟩
  have hm := fullSlack_mass_pos n hn
  have hcap := commonInformationNat_le_boolean_rectangles
    (rowWitness (n := n)) (columnWitness (n := n))
    (fun R T => fullSlack_boolean_rectangles R T) hm
  rw [fullSlack_flat_ratio n hn] at hcap
  apply hcap.trans
  have hne := (isProbability_normalize (fullSlack_nonneg n hn) hm).nonempty
  let : Nonempty (Row n) := ⟨(Classical.choice hne).1⟩
  have hr : 0 < (Fintype.card (Row n) : ℝ) := by exact_mod_cast Fintype.card_pos
  apply Real.log_le_log (div_pos (mul_pos (card_cert_pos n hn) hr) (fullColumnMass_pos n hn))
  apply (div_le_iff₀ (fullColumnMass_pos n hn)).mpr
  rw [card_cert_real n (by omega), card_row_real n (by omega)]
  exact full_count_ceiling n hn

/-- The same natural-log ceiling for the actual subtour-only matrix. -/
theorem commonInformationNat_subtour_bound (n : ℕ) (hn : 3 ≤ n) :
    commonInformationNat (subtourMatrix n) ≤ Real.log (4 * (n : ℝ) ^ 2) := by
  let : NeZero n := ⟨by omega⟩
  have hm := subtourMatrix_mass_pos n hn
  have hcap := commonInformationNat_le_boolean_rectangles (M := subtourMatrix n)
    (fun c S => rowWitness (n := n) c (.inl S)) (columnWitness (n := n))
    (fun S T => subtourSlack_boolean_rectangles S T) hm
  rw [subtourMatrix_flat_ratio n hn] at hcap
  apply hcap.trans
  have hne := (isProbability_normalize (subtourMatrix_nonneg n hn) hm).nonempty
  let : Nonempty (Subtour n) := ⟨(Classical.choice hne).1⟩
  have hr : 0 < (Fintype.card (Subtour n) : ℝ) := by exact_mod_cast Fintype.card_pos
  apply Real.log_le_log (div_pos (mul_pos (card_cert_pos n hn) hr) (subtourColumnMass_pos n hn))
  apply (div_le_iff₀ (subtourColumnMass_pos n hn)).mpr
  rw [card_cert_real n (by omega), card_subtour_real n (by omega)]
  exact subtour_count_ceiling n hn

/-- Convert the natural-log ceiling to the explicitly stated bound in bits. -/
theorem log_four_square_div_log_two (n : ℕ) (hn : 3 ≤ n) :
    Real.log (4 * (n : ℝ) ^ 2) / Real.log 2 =
      2 * Real.log (n : ℝ) / Real.log 2 + 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0), hlog, Real.log_pow]
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  push_cast
  field_simp
  ring

/-- Common information of the actual full slack matrix is at most 2 log₂ n + 2 bits. -/
theorem commonInformation_full_bound (n : ℕ) (hn : 3 ≤ n) :
    commonInformation (fullSlack n) ≤ 2 * Real.log (n : ℝ) / Real.log 2 + 2 := by
  rw [commonInformation, ← log_four_square_div_log_two n hn]
  exact div_le_div_of_nonneg_right (commonInformationNat_full_bound n hn)
    (Real.log_nonneg (by norm_num))

/-- The subtour-only matrix obeys the same bit ceiling. -/
theorem commonInformation_subtour_bound (n : ℕ) (hn : 3 ≤ n) :
    commonInformation (subtourMatrix n) ≤ 2 * Real.log (n : ℝ) / Real.log 2 + 2 := by
  rw [commonInformation, ← log_four_square_div_log_two n hn]
  exact div_le_div_of_nonneg_right (commonInformationNat_subtour_bound n hn)
    (Real.log_nonneg (by norm_num))

/-- The exponentiated common-information lower-bound quantity is at most 4n². -/
theorem two_rpow_commonInformation_full_bound (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ commonInformation (fullSlack n) ≤ 4 * (n : ℝ) ^ 2 := by
  apply two_rpow_commonInformation_le_of_nat_le_log
    (mul_pos (by norm_num) (sq_pos_of_pos (by exact_mod_cast (show 0 < n by omega))))
  exact commonInformationNat_full_bound n hn

/-- The same numerical ceiling holds for the subtour-only lower-bound quantity. -/
theorem two_rpow_commonInformation_subtour_bound (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ commonInformation (subtourMatrix n) ≤ 4 * (n : ℝ) ^ 2 := by
  apply two_rpow_commonInformation_le_of_nat_le_log
    (mul_pos (by norm_num) (sq_pos_of_pos (by exact_mod_cast (show 0 < n by omega))))
  exact commonInformationNat_subtour_bound n hn

end
end Lemmata.SpanningTreeCommonInformation
