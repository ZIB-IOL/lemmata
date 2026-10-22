module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.MeasurableStrategy
public import Lemmata.DistributionalLowerBounds.Core.Distributional.MeasurableLMO
public import Lemmata.DistributionalLowerBounds.Core.Distributional.FiniteUniformFibers
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

/-!
# Concrete measurable fixed-horizon paired-oracle execution

A query is an arbitrary objective point and an arbitrary LMO direction. The
answer contains the common quadratic's value, its gradient coordinates, and
the exact total LMO. No query feasibility, span or atom-hull constraint occurs.
The final averaging theorem fixes the uniform permutation prior and derives
execution/loss regularity from the controller's measurable maps. The actual
posterior, drift certificate and terminal variance/loss bound remain inputs.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory

noncomputable def coordinateObjectiveDifferential {d : ℕ} (M : ℝ) (x : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, (x i-M) • ContinuousLinearMap.proj i

theorem coordinateObjective_hasFDerivAt {d : ℕ} (M : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (coordinateObjective M) (coordinateObjectiveDifferential M x) x := by
  unfold coordinateObjective coordinateObjectiveDifferential
  apply HasFDerivAt.fun_sum
  intro i _
  have h := (hasFDerivAt_apply (𝕜 := ℝ) i x).sub_const M
  have hh := (h.mul h).const_mul (1/2 : ℝ)
  convert hh using 1
  · funext y
    simp [pow_two]
  · ext v
    simp
    ring

lemma coordinateObjectiveDifferential_apply {d : ℕ} (M : ℝ) (x v : Fin d → ℝ) :
    coordinateObjectiveDifferential M x v = ∑ i, (x i-M)*v i := by
  simp [coordinateObjectiveDifferential]

abbrev PairedQuery (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ)
abbrev PairedAnswer (d : ℕ) := ℝ × (Fin d → ℝ) × (Fin d → ℝ)

noncomputable def concreteOracle (d : ℕ) (rho : ℝ) (π : Equiv.Perm (Fin d))
    (q : PairedQuery d) : PairedAnswer d :=
  let M := objectiveCenter rho (hardTopWeight d)
  (coordinateObjective M q.1, (fun i => q.1 i-M), concreteLMO d π q.2)

theorem concreteOracle_measurable (d : ℕ) (rho : ℝ) (π : Equiv.Perm (Fin d)) :
    Measurable (concreteOracle d rho π) := by
  have hl : Measurable (fun q : PairedQuery d => concreteLMO d π q.2) :=
    (concreteLMO_measurable d π).comp measurable_snd
  have hf : Measurable (fun q : PairedQuery d =>
      coordinateObjective (objectiveCenter rho (hardTopWeight d)) q.1) :=
    (continuous_coordinateObjective d (objectiveCenter rho (hardTopWeight d))).measurable.comp
      measurable_fst
  have hg : Measurable (fun q : PairedQuery d =>
      fun i => q.1 i-objectiveCenter rho (hardTopWeight d)) := by fun_prop
  exact hf.prodMk (hg.prodMk hl)

/-- A paired call contains no extra unknown-objective line-search oracle. -/
lemma concreteOracle_first_order (d : ℕ) (rho : ℝ) (π : Equiv.Perm (Fin d))
    (q : PairedQuery d) (v : Fin d → ℝ) :
    (concreteOracle d rho π q).1 = coordinateObjective (objectiveCenter rho (hardTopWeight d)) q.1 ∧
    coordinateObjectiveDifferential (objectiveCenter rho (hardTopWeight d)) q.1 v =
      ∑ i, (concreteOracle d rho π q).2.1 i*v i := by
  exact ⟨rfl, coordinateObjectiveDifferential_apply _ _ _⟩

/-- Zero-direction padding reveals no hidden permutation; the first-order
answer is from the same public objective on every instance. -/
lemma concreteOracle_zero_direction (d : ℕ) (rho : ℝ)
    (π₁ π₂ : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    concreteOracle d rho π₁ (x, 0) = concreteOracle d rho π₂ (x, 0) := by
  simp [concreteOracle, concreteLMO_zero]

/-- Fixed-horizon application with the actual oracle and a constructed uniform
prior. `CertifiedStrategy`, initial/cap identities and `hloss` are STILL
unproved raw-transcript bridges; this endpoint is deliberately conditional. -/
theorem measurableSeed_concrete_controller_sharp_lower_bounds
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (rho : ℝ)
    (strategy : Seed → DeterministicAdaptiveStrategy (PairedQuery (linearProofDimension T))
      (PairedAnswer (linearProofDimension T)) (Fin (linearProofDimension T) → ℝ))
    (hStrategy : MeasurableStrategy strategy T)
    (deficit : Seed → ℕ → Equiv.Perm (Fin (linearProofDimension T)) → ℝ)
    (certificate : ∀ seed, CertifiedStrategy (linearProofDimension T) T
      (FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T))))
      (strategy seed) (concreteOracle (linearProofDimension T) rho) (deficit seed))
    (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq : rhoLHS (hardWeight (linearProofDimension T))
      (hardTopWeight (linearProofDimension T)) rho = hardC (linearProofDimension T)^2)
    (hzero : ∀ seed, (FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))).expect
      (deficit seed 0) = initialDeficit (linearProofDimension T))
    (hcap : ∀ seed π, deficit seed T π ≤ initialDeficit (linearProofDimension T))
    (hloss : ∀ seed π, rho^2*hardC (linearProofDimension T)^2*deficit seed T π^2 /
      (48*(linearProofDimension T : ℝ)^2) ≤ hardFamilyLoss (linearProofDimension T) rho π
        ((strategy seed).run (concreteOracle (linearProofDimension T) rho) π T))
    (hFeas : ∀ seed π, coordinateEnergy (permutedHardWeight (linearProofDimension T) π)
      ((strategy seed).run (concreteOracle (linearProofDimension T) rho) π T) ≤
        hardC (linearProofDimension T)^2) :
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    let threshold := hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2)
    threshold ≤ P.expect (fun π => ∫ seed, hardFamilyLoss (linearProofDimension T) rho π
      ((strategy seed).run (concreteOracle (linearProofDimension T) rho) π T) ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | threshold ≤
      hardFamilyLoss (linearProofDimension T) rho π
        ((strategy seed).run (concreteOracle (linearProofDimension T) rho) π T)}) := by
  apply measurableSeed_feasible_strategy_sharp_lower_bounds μ T _ strategy _ deficit certificate
    hrho hrhoEq hzero hcap hloss
  · intro π
    exact hStrategy.run_measurable _ (concreteOracle_measurable _ _) π
  · exact hFeas

end Lemmata.DistributionalLowerBounds.Core.Distributional
