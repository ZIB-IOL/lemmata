module

public import Lemmata.CocubicCovering.Proof.RankTwelve
public meta import Lemmata.CocubicCovering.Proof.RankTwelve
public import Lemmata.CocubicCovering.Proof.LevelSix
public meta import Lemmata.CocubicCovering.Proof.LevelSix

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

theorem form9_weight_ge_thirty_two (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    32 ≤ weight (eval form9 + h) := by
  obtain ⟨v, hv, hw⟩ := CoveringLevelSix.form9_packed_weight_reduction h hh
  have hr := CoveringRankTwelve.rank_at_least_twelve v hv
  change 12 ≤ Module.finrank Field
    (LinearMap.range (Matrix.toBilin'
      (CoveringCongruence.coefficientMatrix CoveringLevelSix.matrixRows v))) at hr
  omega

theorem coveringRadius9_ge_thirty_two : 32 ≤ coveringRadius 9 5 6 :=
  coveringRadius_lower_bound form9_mem form9_weight_ge_thirty_two

end Lemmata.CocubicCovering.Covering
