module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.SharpNormalized
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Arbitrary measurable seed laws

Independence is represented by using the same finite instance prior for every
seed and then integrating over a probability measure. No seed atoms, finite
seed support, or conditioning on positive-probability seed singletons occurs.
Measurability and integrability are explicit; deriving them and the numerical
transcript certificate from the oracle-model algorithm remains out of scope.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory

namespace FinitePMF

variable {S Ω : Type*} [MeasurableSpace S] [Fintype Ω]

lemma integral_expect (P : FinitePMF Ω) (μ : Measure S) (X : S → Ω → ℝ)
    (hX : ∀ ω, Integrable (fun s => X s ω) μ) :
    (∫ s, P.expect (X s) ∂μ) = P.expect (fun ω => ∫ s, X s ω ∂μ) := by
  unfold expect
  rw [integral_finset_sum _ (fun ω _ => (hX ω).const_mul (P.weight ω))]
  apply Finset.sum_congr rfl
  intro ω _
  exact integral_const_mul _ _

/-- Integrate the deterministic lower bound over any independent seed law. -/
theorem integrate_seedwise_lower_bound (P : FinitePMF Ω)
    (μ : Measure S) [IsProbabilityMeasure μ] (X : S → Ω → ℝ)
    (hX : ∀ ω, Integrable (fun s => X s ω) μ) {c : ℝ}
    (hbound : ∀ s, c ≤ P.expect (X s)) :
    c ≤ P.expect (fun ω => ∫ s, X s ω ∂μ) := by
  have hi : Integrable (fun s => P.expect (X s)) μ := by
    exact integrable_finset_sum _ (fun ω _ => (hX ω).const_mul (P.weight ω))
  calc
    c = ∫ _ : S, c ∂μ := by simp
    _ ≤ ∫ s, P.expect (X s) ∂μ := integral_mono (integrable_const _) hi hbound
    _ = _ := P.integral_expect μ X hX

/-- The conclusion uses actual real-valued event measures, not just an
uninterpreted 'probability' function. Indicators are automatically integrable. -/
theorem integrate_seedwise_probability_lower_bound (P : FinitePMF Ω)
    (μ : Measure S) [IsProbabilityMeasure μ] (A : S → Ω → Prop)
    (hA : ∀ ω, MeasurableSet {s | A s ω}) {p : ℝ}
    (hbound : ∀ s, p ≤ P.prob (A s)) :
    p ≤ P.expect (fun ω => μ.real {s | A s ω}) := by
  classical
  have hi : ∀ ω, Integrable (fun s => if A s ω then (1 : ℝ) else 0) μ := by
    intro ω
    convert (integrable_const (μ := μ) (1 : ℝ)).indicator (hA ω) using 1
    funext s
    simp [Set.indicator]
  have he : ∀ ω, (∫ s, if A s ω then (1 : ℝ) else 0 ∂μ) = μ.real {s | A s ω} := by
    intro ω
    simpa [Set.indicator] using (integral_indicator_const (μ := μ) (1 : ℝ) (hA ω))
  have h := P.integrate_seedwise_lower_bound μ
    (fun s ω => if A s ω then (1 : ℝ) else 0) hi hbound
  simpa only [he] using h

/-- The hard instance is selected before the seed is sampled. -/
theorem exists_instance_measurable_probability_ge (P : FinitePMF Ω)
    (μ : Measure S) [IsProbabilityMeasure μ] (A : S → Ω → Prop)
    (hA : ∀ ω, MeasurableSet {s | A s ω}) {p : ℝ}
    (hbound : ∀ s, p ≤ P.prob (A s)) :
    ∃ ω, p ≤ μ.real {s | A s ω} :=
  P.exists_ge_of_le_expect _ (P.integrate_seedwise_probability_lower_bound μ A hA hbound)

end FinitePMF

/-- Sharp expectation and same-threshold 3/4 probability for arbitrary
measurable seed laws, at the explicit strategy-certificate interface. The
instance law is independent of the seed. The two fixed-instance witnesses can
subsequently be selected separately using `exists_ge_of_le_expect`. -/
theorem measurableSeed_strategy_sharp_lower_bounds
    {Seed Ω Query Answer Output : Type} [MeasurableSpace Seed] [Fintype Ω]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (instanceLaw : FinitePMF Ω)
    (strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Ω → Query → Answer) (loss : Ω → Output → ℝ)
    (deficit : Seed → ℕ → Ω → ℝ) (T : ℕ)
    (certificate : ∀ seed, CertifiedStrategy (linearProofDimension T) T instanceLaw
      (strategy seed) oracle (deficit seed))
    {rho : ℝ} (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq : rhoLHS (hardWeight (linearProofDimension T))
      (hardTopWeight (linearProofDimension T)) rho = hardC (linearProofDimension T)^2)
    (hzero : ∀ seed, instanceLaw.expect (deficit seed 0) = initialDeficit (linearProofDimension T))
    (hcap : ∀ seed ω, deficit seed T ω ≤ initialDeficit (linearProofDimension T))
    (hloss : ∀ seed ω, rho^2*hardC (linearProofDimension T)^2*deficit seed T ω^2 /
      (48*(linearProofDimension T : ℝ)^2) ≤ loss ω ((strategy seed).run oracle ω T))
    (hInt : ∀ ω, Integrable (fun seed => loss ω ((strategy seed).run oracle ω T)) μ)
    (hMeas : ∀ ω, MeasurableSet {seed |
      hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2) ≤
        loss ω ((strategy seed).run oracle ω T)}) :
    let threshold := hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2)
    threshold ≤ instanceLaw.expect (fun ω => ∫ seed, loss ω ((strategy seed).run oracle ω T) ∂μ) ∧
    (3 : ℝ)/4 ≤ instanceLaw.expect (fun ω => μ.real {seed |
      threshold ≤ loss ω ((strategy seed).run oracle ω T)}) := by
  dsimp only
  constructor
  · apply instanceLaw.integrate_seedwise_lower_bound μ _ hInt
    intro seed
    exact adaptive_distributional_lower_bound_linear instanceLaw (deficit seed T)
      (fun ω => loss ω ((strategy seed).run oracle ω T)) T
      (certificate seed).toAdaptiveProcess hrhoIoo hrhoEq (hzero seed) rfl (hloss seed)
  · apply instanceLaw.integrate_seedwise_probability_lower_bound μ _ hMeas
    intro seed
    exact adaptive_probability_lower_bound_linear instanceLaw (deficit seed T)
      (fun ω => loss ω ((strategy seed).run oracle ω T)) T
      (certificate seed).toAdaptiveProcess hrhoIoo hrhoEq (hzero seed) rfl (hcap seed) (hloss seed)

end Lemmata.DistributionalLowerBounds.Core.Distributional
