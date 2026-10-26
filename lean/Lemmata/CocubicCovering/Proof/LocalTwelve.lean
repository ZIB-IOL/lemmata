module

public import Lemmata.CocubicCovering.Proof.LocalRanks
public meta import Lemmata.CocubicCovering.Proof.LocalRanks

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLocalTwelve

open CoveringLocalRanks CoveringRankWitness

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def representative (i : Fin 4) : Nat :=
  (#[1184, 1188, 1192, 1193][i.val]?).getD 0

def inverseData : Array (Array Nat) :=
  #[
    #[2048, 1024, 512, 32, 224, 280, 16, 272, 160, 4, 2, 1],
    #[2286, 1153, 593, 33, 228, 281, 21, 275, 160, 4, 2, 1],
    #[2560, 1024, 512, 368, 232, 344, 184, 336, 168, 5, 2, 1],
    #[2576, 1364, 682, 372, 235, 348, 186, 340, 170, 5, 2, 1],
  ]

def inverseRows (i : Fin 4) (j : Fin 12) : Nat :=
  (inverseData[i.val]?.getD #[])[j.val]?.getD 0

theorem inverse_checked : ∀ i : Fin 4,
    (rowMatrix (inverseRows i) : Matrix (Fin 12) (Fin 12) Field) *
      localMatrix (representative i) = 1 := by native_decide

theorem local_rank_lower (i : Fin 4) : 12 ≤ (localMatrix (representative i)).rank := by
  have h := Matrix.rank_mul_le_right
    (rowMatrix (inverseRows i) : Matrix (Fin 12) (Fin 12) Field)
    (localMatrix (representative i))
  rw [inverse_checked i] at h
  simpa using h

attribute [local irreducible] localMatrix rootMatrix

theorem rank_lower (root : Nat) (hroot : root ∈ [1184, 1188, 1192, 1193]) :
    12 ≤ (rootMatrix root).rank := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroot
  rcases hroot with rfl | rfl | rfl | rfl
  · rw [← root1184_matrix]
    exact local_rank_lower 0
  · rw [← root1188_matrix]
    exact local_rank_lower 1
  · rw [← root1192_matrix]
    exact local_rank_lower 2
  · rw [← root1193_matrix]
    exact local_rank_lower 3

end Lemmata.CocubicCovering.CoveringLocalTwelve
