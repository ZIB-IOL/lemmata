module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.OriginalModelDefinitions

@[expose] public section

/-!
# Paper-facing statements, without their proofs

The model definitions are separated from `Core.Distributional.OriginalModel`,
which proves the three endpoints. The shared core retains its original internal
organization: it contains both model definitions and supporting lemmas.

The seed law is independent of the uniform permutation prior (the expectations
below are iterated product expectations). Final feasibility is pointwise on every
instance and seed, not merely almost sure. The fixed-instance witnesses in the
two conclusions need not coincide. In the stopping statement, infinite call count
is included in the tail and failures concern returned outputs only.
-/
namespace Lemmata.DistributionalLowerBounds

open MeasureTheory Core.Distributional Core.Distributional.DeterministicAdaptiveStrategy

/-- Expected loss and a same-threshold probability lower bound for at most `T`
actual paired calls. This is the original full-history oracle model. -/
def MainBounds : Prop :=
  ∀ {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FullFamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedQuery (linearProofDimension T) × PairedAnswer (linearProofDimension T)))
    (hs : MeasurableStoppingStrategy s r T)
    (hBudget : ∀ seed π, (s seed).callCount (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π ≤ (T : WithTop ℕ))
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π))
    (π₀ : Equiv.Perm (Fin (linearProofDimension T))),
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    let b := sharpConstant * L * (Metric.diam (scaledSet
      (weightedHardSet (hardC (linearProofDimension T))
        (permutedHardWeight (linearProofDimension T) π₀)) alpha))^2/(T+1 : ℝ)^2
    b ≤ P.expect (fun π => ∫ seed, fullFinalGap (s seed) (r seed) (hardRho T) L alpha π ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | b ≤
      fullFinalGap (s seed) (r seed) (hardRho T) L alpha π})

/-- A fixed instance for expected error and a (possibly different) fixed
instance for the same-threshold probability bound. Neither depends on the
realized independent seed. -/
def FixedInstanceBounds : Prop :=
  ∀ {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FullFamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedQuery (linearProofDimension T) × PairedAnswer (linearProofDimension T)))
    (hs : MeasurableStoppingStrategy s r T)
    (hBudget : ∀ seed π, (s seed).callCount (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π ≤ (T : WithTop ℕ))
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π)),
    (∃ π, scaledThreshold T L alpha ≤
      ∫ seed, fullFinalGap (s seed) (r seed) (hardRho T) L alpha π ∂μ) ∧
    (∃ π, (3 : ℝ)/4 ≤ μ.real {seed | scaledThreshold T L alpha ≤
      fullFinalGap (s seed) (r seed) (hardRho T) L alpha π})

/-- First-return call tail, permitting nontermination. The hypothesis bounds
failures on returned outputs; nontermination already lies in the call tail. -/
def StoppingTailBound : Prop :=
  ∀ {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → FullFamilyStrategy (linearProofDimension T))
    (r : Seed → StopRule (PairedQuery (linearProofDimension T) × PairedAnswer (linearProofDimension T)))
    (hs : ∀ n, MeasurableStoppingStrategy s r n)
    (hFeas : ∀ seed π, ScaledFeasible alpha π ((s seed).stoppedRun (r seed) (recordedOracle
      (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π))
    (eta : ℝ)
    (hFailure : ∀ π, μ.real {seed | (s seed).callCount (r seed) (recordedOracle
        (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π < ⊤ ∧
      scaledThreshold T L alpha ≤ fullFinalGap (s seed) (r seed) (hardRho T) L alpha π} ≤ eta),
    ∃ π, (3 : ℝ)/4-eta ≤ μ.real {seed | (T : WithTop ℕ) < (s seed).callCount (r seed)
      (recordedOracle (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha)) π}

end Lemmata.DistributionalLowerBounds
