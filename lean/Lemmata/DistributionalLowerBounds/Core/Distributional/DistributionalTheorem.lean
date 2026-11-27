module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.StoppedRun

@[expose] public section

/-!
# Distributional lower bounds for the original at-most-call model

The prior, optimizer, exact scaled oracle, posterior and all drift/loss data
are constructed. The final assumptions are positive scales, measurable
query/stopping/output maps, the actual call budget, and final feasibility on
EVERY instance and seed. The stopping-tail endpoint removes the fixed budget.
-/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory

abbrev FamilyStrategy (d : ℕ) :=
  DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) (Fin d → ℝ)

noncomputable def finalGap {d : ℕ} (s : FamilyStrategy d) (r : StopRule (PairedAnswer d))
    (rho L alpha : ℝ) (π : Equiv.Perm (Fin d)) : ℝ :=
  scaledFamilyLoss d rho L alpha π (s.stoppedRun r (scaledConcreteOracle d rho L alpha) π)

lemma padded_feasible {d : ℕ} (s : FamilyStrategy d) (r : StopRule (PairedAnswer d))
    (rho L alpha : ℝ) (π : Equiv.Perm (Fin d)) (T : ℕ)
    (hf : ScaledFeasible alpha π (s.stoppedRun r (scaledConcreteOracle d rho L alpha) π)) :
    ScaledFeasible alpha π ((s.padded r 0).run (scaledConcreteOracle d rho L alpha) π T) := by
  by_cases ht : StoppedBy r T (s.transcript (scaledConcreteOracle d rho L alpha) π T)
  · rwa [s.padded_run_eq_stoppedRun r 0 _ π T ht]
  · rw [s.padded_run_of_not_stopped r 0 _ π T ht]
    exact scaledFeasible_zero _ _

/-- Main fixed-prior theorem, including arbitrary measurable independent seeds
and the same non-strict threshold in expectation and probability. -/
theorem distributional_lower_bounds
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedAnswer (linearProofDimension T)))
    (hs : MeasurableStoppingStrategy s r T)
    (hBudget : ∀ seed π, (s seed).callCount (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π ≤ (T : WithTop ℕ))
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π)) :
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    scaledThreshold T L alpha ≤ P.expect (fun π =>
      ∫ seed, finalGap (s seed) (r seed) (hardRho T) L alpha π ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | scaledThreshold T L alpha ≤
      finalGap (s seed) (r seed) (hardRho T) L alpha π}) := by
  have h := scaled_controller_sharp_lower_bounds μ T L alpha hL ha
    (fun seed => (s seed).padded (r seed) 0) (hs.padded 0)
    (fun seed π => padded_feasible _ _ _ _ _ _ T (hFeas seed π))
  have he seed π := (s seed).padded_run_eq_stoppedRun (r seed) 0
    (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π T
    (((s seed).callCount_le_iff (r seed) _ π T).mp (hBudget seed π))
  simpa only [he, finalGap] using h

/-- Exact manuscript normalization; the representative permutation only names
its common diameter, and is not a hard-instance witness. -/
theorem distributional_diameter_lower_bounds
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedAnswer (linearProofDimension T)))
    (hs : MeasurableStoppingStrategy s r T)
    (hBudget : ∀ seed π, (s seed).callCount (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π ≤ (T : WithTop ℕ))
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π))
    (π₀ : Equiv.Perm (Fin (linearProofDimension T))) :
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    let b := sharpConstant * L * (Metric.diam (scaledSet
      (weightedHardSet (hardC (linearProofDimension T))
        (permutedHardWeight (linearProofDimension T) π₀)) alpha))^2/(T+1 : ℝ)^2
    b ≤ P.expect (fun π => ∫ seed, finalGap (s seed) (r seed) (hardRho T) L alpha π ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | b ≤
      finalGap (s seed) (r seed) (hardRho T) L alpha π}) := by
  dsimp only
  rw [← scaledThreshold_eq_diameter T L alpha ha π₀]
  exact distributional_lower_bounds μ T L alpha hL ha s r hs hBudget hFeas

theorem distributional_fixed_instances
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedAnswer (linearProofDimension T)))
    (hs : MeasurableStoppingStrategy s r T)
    (hBudget : ∀ seed π, (s seed).callCount (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π ≤ (T : WithTop ℕ))
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π)) :
    (∃ π, scaledThreshold T L alpha ≤
      ∫ seed, finalGap (s seed) (r seed) (hardRho T) L alpha π ∂μ) ∧
    (∃ π, (3 : ℝ)/4 ≤ μ.real {seed | scaledThreshold T L alpha ≤
      finalGap (s seed) (r seed) (hardRho T) L alpha π}) := by
  have h := distributional_lower_bounds μ T L alpha hL ha s r hs hBudget hFeas
  exact ⟨FinitePMF.exists_ge_of_le_expect _ _ h.1, FinitePMF.exists_ge_of_le_expect _ _ h.2⟩

/-- The event cover is derived from actual truncation, not supplied by a caller.
The budget may be unbounded and infinity is included in the tail event. -/
theorem distributional_stopping_tail_returned
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedAnswer (linearProofDimension T)))
    (hs : ∀ n, MeasurableStoppingStrategy s r n)
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π))
    (eta : ℝ)
    (hFailure : ∀ π, μ.real {seed | (s seed).callCount (r seed)
        (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π < ⊤ ∧
      scaledThreshold T L alpha ≤ finalGap (s seed) (r seed) (hardRho T) L alpha π} ≤ eta) :
    ∃ π, (3 : ℝ)/4-eta ≤ μ.real {seed | (T : WithTop ℕ) < (s seed).callCount (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π} := by
  let oracle := scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha
  have h := scaled_controller_sharp_lower_bounds μ T L alpha hL ha
    (fun seed => (s seed).padded (r seed) 0) ((hs T).padded 0)
    (fun seed π => padded_feasible _ _ _ _ _ _ T (hFeas seed π))
  obtain ⟨π, hp⟩ := FinitePMF.exists_ge_of_le_expect _ _ h.2
  let A : Set Seed := {seed | scaledThreshold T L alpha ≤
    scaledFamilyLoss _ (hardRho T) L alpha π ((s seed).padded (r seed) 0 |>.run oracle π T)}
  let B : Set Seed := {seed | (s seed).callCount (r seed) oracle π < ⊤ ∧
    scaledThreshold T L alpha ≤ finalGap (s seed) (r seed) (hardRho T) L alpha π}
  let C : Set Seed := {seed | (T : WithTop ℕ) < (s seed).callCount (r seed) oracle π}
  have hc : A ⊆ B ∪ C := by
    intro seed hseed
    by_cases ht : (s seed).callCount (r seed) oracle π ≤ (T : WithTop ℕ)
    · left
      refine ⟨lt_of_le_of_lt ht (WithTop.natCast_lt_top T), ?_⟩
      have he := (s seed).padded_run_eq_stoppedRun (r seed) 0 oracle π T
        (((s seed).callCount_le_iff (r seed) oracle π T).mp ht)
      change scaledThreshold T L alpha ≤ scaledFamilyLoss _ _ _ _ _ _ at hseed
      rw [he] at hseed
      exact hseed
    · exact Or.inr (lt_of_not_ge ht)
  have hm : μ.real A ≤ μ.real B + μ.real C :=
    (measureReal_mono hc).trans (measureReal_union_le B C)
  have hp' : (3 : ℝ)/4 ≤ μ.real A := hp
  have hf : μ.real B ≤ eta := hFailure π
  exact ⟨π, by change (3 : ℝ)/4-eta ≤ μ.real C; linarith⟩

/-- The manuscript's all-instance final-failure premise implies the weaker
returned-failure premise. No finite-termination assumption is needed. -/
theorem distributional_stopping_tail
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedAnswer (linearProofDimension T)))
    (hs : ∀ n, MeasurableStoppingStrategy s r n)
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π))
    (eta : ℝ)
    (hFailure : ∀ π, μ.real {seed | scaledThreshold T L alpha ≤
      finalGap (s seed) (r seed) (hardRho T) L alpha π} ≤ eta) :
    ∃ π, (3 : ℝ)/4-eta ≤ μ.real {seed | (T : WithTop ℕ) < (s seed).callCount (r seed)
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π} := by
  apply distributional_stopping_tail_returned μ T L alpha hL ha s r hs hFeas eta
  intro π
  exact (measureReal_mono (fun _ h => h.2)).trans (hFailure π)

lemma finalGap_measurable {Seed : Type} [MeasurableSpace Seed] {d : ℕ}
    (s : Seed → FamilyStrategy d) (r : Seed → StopRule (PairedAnswer d))
    (hs : ∀ n, MeasurableStoppingStrategy s r n) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) :
    Measurable (fun seed => finalGap (s seed) (r seed) rho L alpha π) :=
  (scaledFamilyLoss_measurable d rho L alpha π).comp
    (stoppedRun_measurable (scaledConcreteOracle d rho L alpha)
      (scaledConcreteOracle_measurable d rho L alpha) hs 0 π)

lemma callCount_tail_measurable {Seed : Type} [MeasurableSpace Seed] {d T : ℕ}
    (s : Seed → FamilyStrategy d) (r : Seed → StopRule (PairedAnswer d))
    (hs : MeasurableStoppingStrategy s r T) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) :
    MeasurableSet {seed | (T : WithTop ℕ) < (s seed).callCount (r seed)
      (scaledConcreteOracle d rho L alpha) π} := by
  convert (hs.stoppedBy_run_set (scaledConcreteOracle d rho L alpha)
    (scaledConcreteOracle_measurable d rho L alpha) π).compl using 1
  ext seed
  simp [← not_le, DeterministicAdaptiveStrategy.callCount_le_iff]

/-- The zero value on nontermination is only a totalization convention. A
pointwise guarantee on every defined output supplies feasibility of this total map. -/
lemma stoppedRun_feasible_of_returned {d : ℕ} (s : FamilyStrategy d) (r : StopRule (PairedAnswer d))
    (rho L alpha : ℝ) (π : Equiv.Perm (Fin d))
    (hf : ∀ n, FirstStop r n (s.transcript (scaledConcreteOracle d rho L alpha) π n) →
      ScaledFeasible alpha π (s.run (scaledConcreteOracle d rho L alpha) π n)) :
    ScaledFeasible alpha π (s.stoppedRun r (scaledConcreteOracle d rho L alpha) π) := by
  by_cases h : ∃ n, FirstStop r n (s.transcript (scaledConcreteOracle d rho L alpha) π n)
  · obtain ⟨n, hn⟩ := h
    rw [s.stoppedRun_of_firstStop r _ π n hn]
    exact hf n hn
  · rw [s.stoppedRun_of_no_stop r _ π h]
    exact scaledFeasible_zero _ _

end Lemmata.DistributionalLowerBounds.Core.Distributional
