module

public import Lemmata.BellFollowup.Positive.Finite

@[expose] public section

namespace Lemmata.BellFollowup.Positive

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Ordered witnesses of the positive and negative coordinate axes. -/
def witnesses2 : List (List Int × List Int × List Int) :=
  [([1,1], [1,1], [1,-1]),
    ([-1,-1], [1,1], [1,-1])]

private theorem bound2 : checkBound 2 inv2 4 = true := by rfl

/-- Exact one-norm bound for every triple of length-2 sign rows. -/
theorem all_rows_2 {a b c : List Int} (ha : a ∈ signRows 2)
    (hb : b ∈ signRows 2) (hc : c ∈ signRows 2) :
    gauge inv2 (threeCoords 2 a b c) ≤ 4 :=
  gauge_le_of_check bound2 ha hb hc

/-- Every signed vertex at radius 4 is attained. -/
theorem signed_axes_2 {v : List Int} (h : v ∈ axes 1 4) :
    ∃ a ∈ signRows 2, ∃ b ∈ signRows 2, ∃ c ∈ signRows 2,
      integerImage inv2 (threeCoords 2 a b c) = v :=
  realizes_axes (W := witnesses2) (by rfl) (by rfl) h

end Lemmata.BellFollowup.Positive
