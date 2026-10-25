module

public import Lemmata.CommonInformationHsb.Seeds

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Costs of all finite conditional-independent extensions of the normalized matrix.
There is no bound on seed cardinality and no uniformity condition on the factors. -/
def admissibleCosts (M : I → J → ℝ) : Set ℝ :=
  {c | ∃ k, ∃ s : ProductSeed (normalize M) k, s.cost = c}

/-- Wyner common information of the normalized finite matrix, in nats. -/
noncomputable def commonInformationNat (M : I → J → ℝ) : ℝ := sInf (admissibleCosts M)

/-- Wyner common information, in bits. -/
noncomputable def commonInformation (M : I → J → ℝ) : ℝ :=
  commonInformationNat M / Real.log 2

theorem admissibleCosts_nonempty {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hmass : 0 < matrixMass M) : (admissibleCosts M).Nonempty := by
  let s := ProductSeed.points (isProbability_normalize hM hmass)
  exact ⟨s.cost, _, s, rfl⟩

theorem admissibleCosts_bddBelow (M : I → J → ℝ) : BddBelow (admissibleCosts M) := by
  refine ⟨0, ?_⟩
  rintro c ⟨k, s, rfl⟩
  exact s.cost_nonneg

/-- Every actual finite seed is an upper bound on the infimum. -/
theorem commonInformationNat_le_cost {M : I → J → ℝ} {k : ℕ}
    (s : ProductSeed (normalize M) k) : commonInformationNat M ≤ s.cost :=
  csInf_le (admissibleCosts_bddBelow M) ⟨k, s, rfl⟩

/-- A bound valid for every finite seed is a bound on genuine common information. -/
theorem le_commonInformationNat {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hmass : 0 < matrixMass M) {a : ℝ}
    (h : ∀ k (s : ProductSeed (normalize M) k), a ≤ s.cost) :
    a ≤ commonInformationNat M := by
  apply le_csInf (admissibleCosts_nonempty hM hmass)
  rintro c ⟨k, s, rfl⟩
  exact h k s

theorem commonInformationNat_nonneg {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hmass : 0 < matrixMass M) : 0 ≤ commonInformationNat M :=
  le_commonInformationNat hM hmass (fun _ s => s.cost_nonneg)

theorem commonInformation_nonneg {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hmass : 0 < matrixMass M) : 0 ≤ commonInformation M :=
  div_nonneg (commonInformationNat_nonneg hM hmass) (Real.log_nonneg (by norm_num))

theorem commonInformationNat_le_entropy {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hmass : 0 < matrixMass M) :
    commonInformationNat M ≤ entropy (Function.uncurry (normalize M)) := by
  simpa only [ProductSeed.cost_points] using
    commonInformationNat_le_cost (ProductSeed.points (isProbability_normalize hM hmass))

end Lemmata.CommonInformationHsb
