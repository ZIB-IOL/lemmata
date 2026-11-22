module

public import Lemmata.SymmetricBellFacetLifting.Recovery.Recovery
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

/-! The analytic reduction from a one-party normalized energy bound to
exponential two-coordinate decay for any number of parties. -/

namespace Lemmata.SymmetricBellFacetLifting.Recovery

open scoped BigOperators

/-- A weighted Parseval upper bound implies the unweighted energy bound when
all normalization weights are at least four fifths. -/
theorem energy_of_weighted_parseval [Fintype ι] (a w : ι → ℝ)
    (hw : ∀ i, (4 : ℝ)/5 ≤ w i) (h : ∑ i, w i * a i ^ 2 ≤ 1) :
    ∑ i, a i ^ 2 ≤ (5 : ℝ)/4 := by
  have h' : (4/5 : ℝ) * (∑ i, a i ^ 2) ≤ ∑ i, w i * a i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
  linarith

/-- Two different entries of a vector of squared mass at most 5/4 have
product at most 5/8. -/
theorem pair_le_of_energy [Fintype ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 ≤ (5 : ℝ)/4) {i j : ι} (hij : i ≠ j) :
    a i * a j ≤ (5 : ℝ)/8 := by
  classical
  have hsum : a i ^ 2 + a j ^ 2 ≤ ∑ k, a k ^ 2 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, j} : Finset ι))
      (f := fun k => a k ^ 2) (fun k _ _ => sq_nonneg (a k))
    simpa [hij] using h
  nlinarith [sq_nonneg (a i - a j)]

/-- A real projection dominated in each mode by a product of one-party
amplitudes inherits the N-th power of the two-mode bound. -/
theorem pair_decay_of_energy [Fintype ι] [Fintype P] (a : P → ι → ℝ)
    (ha : ∀ p i, 0 ≤ a p i) (he : ∀ p, ∑ i, a p i ^ 2 ≤ (5 : ℝ)/4)
    (x : ι → ℝ) {C : ℝ} (hc : 0 ≤ C)
    (hx : ∀ i, |x i| ≤ C * ∏ p, a p i) {i j : ι} (hij : i ≠ j) :
    |x i| * |x j| ≤ C ^ 2 * ((5 : ℝ)/8) ^ Fintype.card P := by
  calc
    |x i| * |x j| ≤ (C * ∏ p, a p i) * (C * ∏ p, a p j) :=
      mul_le_mul (hx i) (hx j) (abs_nonneg _) (mul_nonneg hc (Finset.prod_nonneg fun p _ => ha p i))
    _ = C ^ 2 * ∏ p, (a p i * a p j) := by rw [Finset.prod_mul_distrib]; ring
    _ ≤ C ^ 2 * ∏ _p : P, ((5 : ℝ)/8) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      apply Finset.prod_le_prod₀
      · intro p _
        exact mul_nonneg (ha p i) (ha p j)
      · intro p _
        exact pair_le_of_energy (a p) (he p) hij
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Lemmata.SymmetricBellFacetLifting.Recovery
