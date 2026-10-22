module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FullHistory
public import Lemmata.DistributionalLowerBounds.Core.Distributional.CoordinateSymmetry

@[expose] public section

/-! Paper-facing endpoints with the full query/answer history and actual
stopping count. The finite prior and independent seed law are unchanged. -/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory DeterministicAdaptiveStrategy

abbrev FullFamilyStrategy (d : ℕ) :=
  DeterministicAdaptiveStrategy (PairedQuery d) (PairedQuery d × PairedAnswer d) (Fin d → ℝ)

noncomputable def fullFinalGap {d : ℕ} (s : FullFamilyStrategy d)
    (r : StopRule (PairedQuery d × PairedAnswer d)) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) : ℝ :=
  scaledFamilyLoss d rho L alpha π
    (s.stoppedRun r (recordedOracle (scaledConcreteOracle d rho L alpha)) π)

end Lemmata.DistributionalLowerBounds.Core.Distributional
