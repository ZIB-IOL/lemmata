module

public import Lemmata.CocubicCovering.Compute.LevelSixProofs
public meta import Lemmata.CocubicCovering.Compute.LevelSixProofs
public import Lemmata.CocubicCovering.Proof.LevelSixCases
public meta import Lemmata.CocubicCovering.Proof.LevelSixCases

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringRankTwelve

open Module CoveringBits CoveringWitness CoveringPackedWitness

theorem rank_at_least_twelve (v : Vector 127) (hpoint : v (Fin.last 126) = 1) :
    12 ≤ finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) := by
  by_contra hbad
  have hsmall := CoveringLevelSixReduction.rank_le_ten_of_lt_twelve v (by omega)
  obtain ⟨i, hq⟩ := CoveringLevelSixCases.some_entry_feasible v hpoint hsmall
  obtain ⟨q, hallowed, _⟩ := hq
  apply Lemmata.CocubicCovering.Compute.LevelSixModel.no_state i
  change ∃ q, Lemmata.CocubicCovering.Compute.LevelSixModel.allowed i.val q ∧
    familySpan (decoded (n := 12) ([] : List Nat).get) ≤ Lemmata.CocubicCovering.Compute.LevelSixModel.kernel q
  refine ⟨q, ?_, Submodule.span_le.mpr ?_⟩
  · change CoveringLevelSixProblem.allowed (Fin.ofNat 30 i.val) q
    change CoveringLevelSixProblem.allowed (Fin.ofNat 30 i.val) q at hallowed
    exact hallowed
  · rintro _ ⟨j, _⟩
    exact Fin.elim0 j

end Lemmata.CocubicCovering.CoveringRankTwelve
