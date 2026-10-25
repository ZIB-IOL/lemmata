module

public import Lemmata.CommonInformationHsb.Separation
public import Lemmata.CommonInformationHsb.JointSeeds
public import Lemmata.CommonInformationHsb.CIProperties
public import Lemmata.CommonInformationHsb.FlatCap
public import Lemmata.CommonInformationHsb.Units

@[expose] public section

namespace Lemmata.CommonInformationHsb

-- DOCS_BEGIN_MAIN
/-- A fixed HSB value coexists with unbounded common information in bits. -/
theorem heavy_diagonal_values (N : ℕ) (hN : 1 ≤ N) :
    commonInformation (heavyDiagonal N) = 1 + Real.log N / (2 * Real.log 2) ∧
      hsb (heavyDiagonal N) = 2 :=
  ⟨commonInformation_heavyDiagonal N hN, hsb_heavyDiagonal N hN⟩

/-- One large product block plus r singleton blocks has r+1 as its HSB value. -/
theorem block_matrix_values (S r : ℕ) (hS : 1 ≤ S) :
    commonInformation (blockMatrix S r) = entropy (blockWeights S r) / Real.log 2 ∧
      hsb (blockMatrix S r) = (r : ℝ) + 1 :=
  ⟨by rw [commonInformation, commonInformationNat_blockMatrix S r hS],
    hsb_blockMatrix S r hS⟩

/-- Neither functional has a dimension-independent polynomial-growth bound
in terms of the other. Common information and logarithmic HSB are both in bits. -/
theorem no_polynomial_comparison (a : ℝ) (ha : 0 ≤ a) (d : ℕ) :
    (∃ N : ℕ, 1 ≤ N ∧
      a * (1 + Real.log (hsb (heavyDiagonal N)) / Real.log 2)^d <
        commonInformation (heavyDiagonal N)) ∧
    (∃ r S : ℕ, 1 ≤ S ∧
      a * (1 + commonInformation (blockMatrix S r))^d <
        Real.log (hsb (blockMatrix S r)) / Real.log 2) :=
  ⟨commonInformation_exceeds_polynomial_log_hsb a d,
    log_hsb_exceeds_polynomial_commonInformation a ha d⟩
-- DOCS_END_MAIN

end Lemmata.CommonInformationHsb
