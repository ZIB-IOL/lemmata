module

public import Lemmata.CocubicCovering.Compute.CommonProofs
public meta import Lemmata.CocubicCovering.Compute.CommonProofs

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringZeroKernel

open Module CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness
open CoveringCovarianceData CoveringLocal CoveringSymmetry

theorem finrank_fullKernel_le_seven (v : Vector 127)
    (hpoint : v (Fin.last 126) = 1) (hprojection : localParameterProjection v = 0) :
    finrank Field (fullKernel (fullForm v)) ≤ 7 := by
  by_contra hbad
  have hdimension : 8 ≤ finrank Field (fullKernel (fullForm v)) := by omega
  apply Lemmata.CocubicCovering.Compute.CommonModel.no_allowed 0 v
  refine ⟨hpoint, ?_, hdimension⟩
  exact hprojection.trans (decodeMask_zero 15).symm

end Lemmata.CocubicCovering.CoveringZeroKernel
