module

public import Lemmata.CommonInformationHsb.Entropy
public import Lemmata.CommonInformationHsb.Families
public import Lemmata.CommonInformationHsb.CommonInformation

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- A probability vector has a positive coordinate, even when zero entries are allowed. -/
theorem probability_exists_pos {p : I → ℝ} (hp : IsProbability p) :
    ∃ i, 0 < p i := by
  by_contra h
  push Not at h
  have hsum := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
  rw [hp.2] at hsum
  norm_num at hsum

/-- A probability vector concentrated at one coordinate has zero entropy. -/
theorem entropy_eq_zero_of_single_support {p : I → ℝ} (hp : IsProbability p)
    (a : I) (ha : ∀ i, i ≠ a → p i = 0) : entropy p = 0 := by
  classical
  have hpa : p a = 1 := by
    rw [← hp.2, Finset.sum_eq_single a]
    · intro b _ hba
      exact ha b hba
    · simp
  unfold entropy
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = a
  · simp [hi, hpa]
  · simp [ha i hi]

/-- A product probability distribution supported on a diagonal is a point mass.
In particular, both marginal entropies vanish. -/
theorem entropy_eq_zero_of_product_diagonal {p q : I → ℝ}
    (hp : IsProbability p) (hq : IsProbability q)
    (hsupport : ∀ i j, i ≠ j → p i * q j = 0) :
    entropy p = 0 ∧ entropy q = 0 := by
  obtain ⟨a, ha⟩ := probability_exists_pos hp
  obtain ⟨b, hb⟩ := probability_exists_pos hq
  have hab : a = b := by
    by_contra h
    have := hsupport a b h
    exact (mul_pos ha hb).ne' this
  subst b
  constructor
  · apply entropy_eq_zero_of_single_support hp a
    intro i hi
    exact (mul_eq_zero.mp (hsupport i a hi)).resolve_right (ne_of_gt hb)
  · apply entropy_eq_zero_of_single_support hq a
    intro j hj
    exact (mul_eq_zero.mp (hsupport a j (Ne.symm hj))).resolve_left (ne_of_gt ha)

/-- A diagonal matrix has the mass of its diagonal vector. -/
theorem matrixMass_diagonalMatrix [DecidableEq I] (p : I → ℝ) :
    matrixMass (diagonalMatrix p) = ∑ i, p i := by
  simp [matrixMass, diagonalMatrix]

/-- A probability diagonal is already normalized. -/
theorem normalize_diagonalMatrix [DecidableEq I] {p : I → ℝ}
    (hp : IsProbability p) : normalize (diagonalMatrix p) = diagonalMatrix p := by
  apply normalize_eq_self
  rw [matrixMass_diagonalMatrix, hp.2]

/-- Recording a coordinate twice on a diagonal does not change entropy. -/
theorem entropy_diagonalMatrix [DecidableEq I] (p : I → ℝ) :
    entropy (Function.uncurry (diagonalMatrix p)) = entropy p := by
  simp [entropy, Fintype.sum_prod_type, Function.uncurry, diagonalMatrix,
    apply_ite Real.negMulLog]

/-- Every seed for a probability diagonal has the same mutual-information cost. -/
theorem ProductSeed.cost_diagonal [DecidableEq I] {p : I → ℝ}
    (hp : IsProbability p) {k : ℕ} (s : ProductSeed (normalize (diagonalMatrix p)) k) :
    s.cost = entropy p := by
  have hs : ∀ z, s.weight z * (entropy (s.left z) + entropy (s.right z)) = 0 := by
    intro z
    rcases (s.weight_prob.1 z).eq_or_lt with hz | hz
    · simp [← hz]
    · have hzero : ∀ i j, i ≠ j → s.left z i * s.right z j = 0 := by
        intro i j hij
        apply s.zero_of_zero hz
        rw [normalize_diagonalMatrix hp]
        exact diagonalMatrix_ne p hij
      obtain ⟨hl, hr⟩ := entropy_eq_zero_of_product_diagonal
        (s.left_prob z) (s.right_prob z) hzero
      simp [hl, hr]
  simp only [ProductSeed.cost, hs, Finset.sum_const_zero, sub_zero,
    normalize_diagonalMatrix hp, entropy_diagonalMatrix]

/-- The half-heavy vector is a probability vector for every positive size. -/
theorem isProbability_heavyProbability (N : ℕ) (hN : 1 ≤ N) :
    IsProbability (heavyProbability N) := by
  refine ⟨heavyProbability_nonneg N, ?_⟩
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [Fintype.sum_option, heavyProbability, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- Natural-log entropy of the half-heavy diagonal family. -/
theorem entropy_heavyProbability (N : ℕ) (hN : 1 ≤ N) :
    entropy (heavyProbability N) = Real.log 2 + Real.log N / 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [entropy, Fintype.sum_option, heavyProbability, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.negMulLog]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (mul_ne_zero (by norm_num) hn),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn]
  simp only [Real.log_one]
  field_simp
  ring

/-- Exact common information of any probability diagonal, with arbitrary zero entries. -/
theorem commonInformationNat_diagonalMatrix [DecidableEq I] {p : I → ℝ}
    (hp : IsProbability p) : commonInformationNat (diagonalMatrix p) = entropy p := by
  have hM := diagonalMatrix_nonneg hp.1
  have hm : 0 < matrixMass (diagonalMatrix p) := by
    rw [matrixMass_diagonalMatrix, hp.2]
    norm_num
  apply le_antisymm
  · simpa [normalize_diagonalMatrix hp, entropy_diagonalMatrix] using
      commonInformationNat_le_entropy hM hm
  · apply le_commonInformationNat hM hm
    intro k s
    exact le_of_eq (s.cost_diagonal hp).symm

/-- Exact natural-log common information of the half-heavy diagonal family. -/
theorem commonInformationNat_heavyDiagonal (N : ℕ) (hN : 1 ≤ N) :
    commonInformationNat (heavyDiagonal N) = Real.log 2 + Real.log N / 2 := by
  rw [heavyDiagonal, commonInformationNat_diagonalMatrix (isProbability_heavyProbability N hN),
    entropy_heavyProbability N hN]

/-- Exact bit-valued common information of the half-heavy diagonal family. -/
theorem commonInformation_heavyDiagonal (N : ℕ) (hN : 1 ≤ N) :
    commonInformation (heavyDiagonal N) = 1 + Real.log N / (2 * Real.log 2) := by
  rw [commonInformation, commonInformationNat_heavyDiagonal N hN]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

end Lemmata.CommonInformationHsb
