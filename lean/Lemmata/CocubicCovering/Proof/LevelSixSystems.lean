module

public import Lemmata.CocubicCovering.Proof.LevelSixSystemData
public meta import Lemmata.CocubicCovering.Proof.LevelSixSystemData

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringLevelSixSystems

open CoveringQuotient CoveringCoordinates CoveringPackedPair CoveringPolynomial
open CoveringLevelSixReconstruction
open scoped BigOperators

theorem allAffineChecked : ∀ s : Fin 13, AffineChecked s := by
  unfold AffineChecked
  native_decide

theorem affineChecked (s : Fin 13) : AffineChecked s := allAffineChecked s

theorem allOutsideChecked : ∀ s : Fin 13, OutsideChecked s := by
  unfold OutsideChecked
  native_decide

theorem outsideChecked (s : Fin 13) : OutsideChecked s := allOutsideChecked s

theorem outside_annihilate (s : Fin 13) (k : Fin (outsideCount s))
    (target : Fin 87) :
    ∑ pair : Fin 105, ofBool (keep s target pair) *
      Matrix.toBilin' (bitMatrix (outside s k))
        (CoveringBits.decodeMask (outsideBasis s (pairFirst pair)))
        (CoveringBits.decodeMask (outsideBasis s (pairSecond pair))) = 0 := by
  simp_rw [← ofBool_pairBit]
  have h := congrArg ofBool ((outsideChecked s).2 k target)
  rw [ofBool_foldr_xor, ← List.sum_toFinset _ (List.nodup_finRange 105),
    List.toFinset_finRange] at h
  calc
    (∑ pair : Fin 105, ofBool (keep s target pair) *
        ofBool (pairBit (outside s k) (outsideBasis s (pairFirst pair))
          (outsideBasis s (pairSecond pair)))) =
      ∑ pair : Fin 105, ofBool (if keep s target pair then
        pairBit (outside s k) (outsideBasis s (pairFirst pair))
          (outsideBasis s (pairSecond pair)) else false) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      cases keep s target pair <;> simp
    _ = 0 := h


theorem input_vanishes (s : Fin 13) (assignment : Nat → Field)
    (hcanonical : ∀ target, CoveringIdeal.eval assignment (canonical s target) = 0)
    (row : Fin 87) : CoveringIdeal.eval assignment (input s row) = 0 := by
  rw [input, CoveringIdeal.eval_normalize]
  exact hcanonical row

end Lemmata.CocubicCovering.CoveringLevelSixSystems
