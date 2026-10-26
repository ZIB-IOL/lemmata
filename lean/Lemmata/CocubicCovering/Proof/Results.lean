module

public import Lemmata.CocubicCovering.Proof.RankTen
public meta import Lemmata.CocubicCovering.Proof.RankTen
public import Lemmata.CocubicCovering.Proof.Realization
public meta import Lemmata.CocubicCovering.Proof.Realization
public import Lemmata.CocubicCovering.Proof.Ambient
public meta import Lemmata.CocubicCovering.Proof.Ambient

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open CoveringCongruence CoveringCovarianceData

theorem form9_weight_ge_thirty (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    30 ≤ weight (eval form9 + h) := by
  obtain ⟨v, hv, hw⟩ := CoveringRealization.form9_packed_weight_reduction h hh
  have hr : 10 ≤ Module.finrank Field
      (LinearMap.range (Matrix.toBilin' (coefficientMatrix matrixRows v))) :=
    CoveringRankTen.rank_at_least_ten v hv
  omega

theorem form10_weight_ge_thirty_two (h : BooleanFunction 10)
    (hh : h ∈ reedMuller 10 6) : 32 ≤ weight (eval form10 + h) := by
  obtain ⟨v, hv, hw⟩ := CoveringAmbient.form10_packed_weight_reduction h hh
  have hr : 10 ≤ Module.finrank Field
      (LinearMap.range (Matrix.toBilin' (coefficientMatrix matrixRows v))) :=
    CoveringRankTen.rank_at_least_ten v hv
  omega

theorem form11_weight_ge_thirty_four (h : BooleanFunction 11)
    (hh : h ∈ reedMuller 11 7) : 34 ≤ weight (eval form11 + h) := by
  obtain ⟨v, hv, hw⟩ := CoveringAmbient.form11_packed_weight_reduction h hh
  have hr : 10 ≤ Module.finrank Field
      (LinearMap.range (Matrix.toBilin' (coefficientMatrix matrixRows v))) :=
    CoveringRankTen.rank_at_least_ten v hv
  omega

theorem coveringRadius9_ge_thirty : 30 ≤ coveringRadius 9 5 6 :=
  coveringRadius_lower_bound form9_mem form9_weight_ge_thirty

theorem coveringRadius10_ge_thirty_two : 32 ≤ coveringRadius 10 6 7 :=
  coveringRadius_lower_bound form10_mem form10_weight_ge_thirty_two

theorem coveringRadius11_ge_thirty_four : 34 ≤ coveringRadius 11 7 8 :=
  coveringRadius_lower_bound form11_mem form11_weight_ge_thirty_four

end Lemmata.CocubicCovering.Covering
