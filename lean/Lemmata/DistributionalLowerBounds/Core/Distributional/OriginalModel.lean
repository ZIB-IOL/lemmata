module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.OriginalModelDefinitions

@[expose] public section

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory DeterministicAdaptiveStrategy

/-- Original-model main theorem: arbitrary measurable maps of full histories,
every-seed/every-instance final feasibility, and at most T actual paired calls. -/
theorem original_model_lower_bounds
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FullFamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedQuery (linearProofDimension T) × PairedAnswer (linearProofDimension T)))
    (hs : MeasurableStoppingStrategy s r T)
    (hBudget : ∀ seed π, (s seed).callCount (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π ≤ (T : WithTop ℕ))
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π))
    (π₀ : Equiv.Perm (Fin (linearProofDimension T))) :
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    let b := sharpConstant * L * (Metric.diam (scaledSet
      (weightedHardSet (hardC (linearProofDimension T))
        (permutedHardWeight (linearProofDimension T) π₀)) alpha))^2/(T+1 : ℝ)^2
    b ≤ P.expect (fun π => ∫ seed, fullFinalGap (s seed) (r seed) (hardRho T) L alpha π ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | b ≤
      fullFinalGap (s seed) (r seed) (hardRho T) L alpha π}) := by
  have h := distributional_diameter_lower_bounds μ T L alpha hL ha
    (fun seed => (s seed).feedback) (fun seed => (s seed).feedbackRule (r seed)) hs.feedback
    (by simpa only [feedback_callCount] using hBudget)
    (by simpa only [feedback_stoppedRun] using hFeas) π₀
  simpa only [finalGap, feedback_stoppedRun, fullFinalGap] using h

theorem original_model_fixed_instances
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FullFamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedQuery (linearProofDimension T) × PairedAnswer (linearProofDimension T)))
    (hs : MeasurableStoppingStrategy s r T)
    (hBudget : ∀ seed π, (s seed).callCount (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π ≤ (T : WithTop ℕ))
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π)) :
    (∃ π, scaledThreshold T L alpha ≤
      ∫ seed, fullFinalGap (s seed) (r seed) (hardRho T) L alpha π ∂μ) ∧
    (∃ π, (3 : ℝ)/4 ≤ μ.real {seed | scaledThreshold T L alpha ≤
      fullFinalGap (s seed) (r seed) (hardRho T) L alpha π}) := by
  have h := distributional_fixed_instances μ T L alpha hL ha
    (fun seed => (s seed).feedback) (fun seed => (s seed).feedbackRule (r seed)) hs.feedback
    (by simpa only [feedback_callCount] using hBudget)
    (by simpa only [feedback_stoppedRun] using hFeas)
  simpa only [finalGap, feedback_stoppedRun, fullFinalGap] using h

/-- Only failures on returned outputs matter: nontermination already belongs to
the call tail. Thus no arbitrary convention for a nonreturned output is needed. -/
theorem original_model_stopping_tail
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FullFamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedQuery (linearProofDimension T) × PairedAnswer (linearProofDimension T)))
    (hs : ∀ n, MeasurableStoppingStrategy s r n)
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π))
    (eta : ℝ)
    (hFailure : ∀ π, μ.real {seed | (s seed).callCount (r seed) (recordedOracle
        (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π < ⊤ ∧
      scaledThreshold T L alpha ≤ fullFinalGap (s seed) (r seed) (hardRho T) L alpha π} ≤ eta) :
    ∃ π, (3 : ℝ)/4-eta ≤ μ.real {seed | (T : WithTop ℕ) < (s seed).callCount (r seed)
      (recordedOracle (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π} := by
  have h := distributional_stopping_tail_returned μ T L alpha hL ha
    (fun seed => (s seed).feedback) (fun seed => (s seed).feedbackRule (r seed)) (fun n => (hs n).feedback)
    (by simpa only [feedback_stoppedRun] using hFeas) eta
    (by simpa only [finalGap, feedback_stoppedRun, feedback_callCount, fullFinalGap] using hFailure)
  simpa only [feedback_callCount] using h

/-- Pointwise feasibility on defined outputs suffices for the auxiliary total
output used in the stopping theorem, also for full query/answer histories. -/
lemma full_stoppedRun_feasible_of_returned {d : ℕ} (s : FullFamilyStrategy d)
    (r : StopRule (PairedQuery d × PairedAnswer d)) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d))
    (hf : ∀ n, FirstStop r n (s.transcript (recordedOracle (scaledConcreteOracle d rho L alpha)) π n) →
      ScaledFeasible alpha π (s.run (recordedOracle (scaledConcreteOracle d rho L alpha)) π n)) :
    ScaledFeasible alpha π (s.stoppedRun r (recordedOracle (scaledConcreteOracle d rho L alpha)) π) := by
  have h := stoppedRun_feasible_of_returned s.feedback (s.feedbackRule r) rho L alpha π
    (fun n hn => by
      rw [feedback_run]
      exact hf n ((s.feedback_firstStop r _ π n).mp hn))
  simpa only [feedback_stoppedRun] using h

end Lemmata.DistributionalLowerBounds.Core.Distributional
