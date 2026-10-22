module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.ActualCertificate

@[expose] public section

/-!
# Certificate-free sharp lower bounds for the concrete fixed-horizon controller

The optimizer parameter, numerical posterior, deficit and per-history
certificates are CONSTRUCTED here. Only the original measurable-controller and
every-instance/every-seed final-feasibility hypotheses remain. This endpoint is
for the base family and exactly T paired calls. Positive-rescaling simulation
and actual stopping/truncation adapters are separate constructions.
-/
open MeasureTheory
namespace Lemmata.DistributionalLowerBounds.Core.Distributional

noncomputable def hardRho (T : ℕ) : ℝ :=
  (concrete_existsUnique_rho (linearProofDimension_ge_three T)).exists.choose

lemma hardRho_spec (T : ℕ) : hardRho T ∈ Set.Ioo (0 : ℝ) 1 ∧
    rhoLHS (hardWeight (linearProofDimension T)) (hardTopWeight (linearProofDimension T))
      (hardRho T) = hardC (linearProofDimension T)^2 :=
  (concrete_existsUnique_rho (linearProofDimension_ge_three T)).exists.choose_spec

/-- Fixed-prior, arbitrary measurable independent seeds, arbitrary measurable
adaptive queries/outputs, and pointwise final feasibility. No posterior, drift,
loss, regularity or optimizer-parameter proof input is supplied. -/
theorem baseFamily_sharp_lower_bounds
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ)
    (strategy : Seed → DeterministicAdaptiveStrategy (PairedQuery (linearProofDimension T))
      (PairedAnswer (linearProofDimension T)) (Fin (linearProofDimension T) → ℝ))
    (hStrategy : MeasurableStrategy strategy T)
    (hFeas : ∀ seed π, coordinateEnergy (permutedHardWeight (linearProofDimension T) π)
      ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T) ≤
        hardC (linearProofDimension T)^2) :
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    let b := hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2)
    b ≤ P.expect (fun π => ∫ seed, hardFamilyLoss (linearProofDimension T) (hardRho T) π
      ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T) ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | b ≤
      hardFamilyLoss (linearProofDimension T) (hardRho T) π
        ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T)}) := by
  apply measurableSeed_concrete_controller_sharp_lower_bounds μ T (hardRho T)
    strategy hStrategy (fun seed => numericalDeficit (strategy seed) (hardRho T))
    (fun seed => actualCertifiedStrategy (strategy seed) (hardRho T) T)
    (hardRho_spec T).1 (hardRho_spec T).2
  · intro seed
    change (FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))).expect
      (fun π => numericalDeficit (strategy seed) (hardRho T) 0 π) = _
    simp_rw [numericalDeficit_initial]
    exact FinitePMF.expect_const _ _
  · intro seed π
    exact numericalDeficit_cap _ _ _ _
  · intro seed π
    exact numerical_terminal_loss (strategy seed) (hardRho_spec T).1 (hardRho_spec T).2
      (by have := linearProofDimension_ge_three T; omega) T (hFeas seed) π
  · exact hFeas

/-- The same base-family result with the manuscript's exact diameter normalization.
The representative permutation affects neither the diameter nor prior. -/
theorem baseFamily_diameter_lower_bounds
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ)
    (strategy : Seed → DeterministicAdaptiveStrategy (PairedQuery (linearProofDimension T))
      (PairedAnswer (linearProofDimension T)) (Fin (linearProofDimension T) → ℝ))
    (hStrategy : MeasurableStrategy strategy T)
    (hFeas : ∀ seed π, coordinateEnergy (permutedHardWeight (linearProofDimension T) π)
      ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T) ≤
        hardC (linearProofDimension T)^2)
    (π₀ : Equiv.Perm (Fin (linearProofDimension T))) :
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    let b := sharpConstant * (Metric.diam (weightedHardSet (hardC (linearProofDimension T))
      (permutedHardWeight (linearProofDimension T) π₀)))^2/(T+1 : ℝ)^2
    b ≤ P.expect (fun π => ∫ seed, hardFamilyLoss (linearProofDimension T) (hardRho T) π
      ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T) ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | b ≤
      hardFamilyLoss (linearProofDimension T) (hardRho T) π
        ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T)}) := by
  dsimp only
  rw [← sharp_threshold_eq_diameter T π₀]
  exact baseFamily_sharp_lower_bounds μ T strategy hStrategy hFeas

/-- Separate fixed-instance witnesses, selected before the independent seed.
The expectation and probability witnesses are not asserted to coincide. -/
theorem baseFamily_fixed_instances
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ)
    (strategy : Seed → DeterministicAdaptiveStrategy (PairedQuery (linearProofDimension T))
      (PairedAnswer (linearProofDimension T)) (Fin (linearProofDimension T) → ℝ))
    (hStrategy : MeasurableStrategy strategy T)
    (hFeas : ∀ seed π, coordinateEnergy (permutedHardWeight (linearProofDimension T) π)
      ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T) ≤
        hardC (linearProofDimension T)^2) :
    let b := hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2)
    (∃ π, b ≤ ∫ seed, hardFamilyLoss (linearProofDimension T) (hardRho T) π
      ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T) ∂μ) ∧
    (∃ π, (3 : ℝ)/4 ≤ μ.real {seed | b ≤ hardFamilyLoss (linearProofDimension T) (hardRho T) π
      ((strategy seed).run (concreteOracle (linearProofDimension T) (hardRho T)) π T)}) := by
  have hb := baseFamily_sharp_lower_bounds μ T strategy hStrategy hFeas
  exact ⟨FinitePMF.exists_ge_of_le_expect _ _ hb.1, FinitePMF.exists_ge_of_le_expect _ _ hb.2⟩

end Lemmata.DistributionalLowerBounds.Core.Distributional
