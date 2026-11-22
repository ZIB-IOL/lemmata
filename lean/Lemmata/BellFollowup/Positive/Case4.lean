module

public import Lemmata.BellFollowup.Positive.Finite

@[expose] public section

namespace Lemmata.BellFollowup.Positive

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Ordered witnesses of the positive and negative coordinate axes. -/
def witnesses4 : List (List Int × List Int × List Int) :=
  [([1,1,1,1], [1,1,1,1], [-1,-1,-1,1]),
    ([-1,-1,-1,-1], [1,1,1,1], [-1,-1,-1,1]),
    ([1,-1,1,1], [1,-1,1,1], [1,1,-1,1]),
    ([-1,1,-1,-1], [1,-1,1,1], [1,1,-1,1])]

private theorem bound4 : checkBound 4 inv4 96 = true := by rfl

/-- Exact one-norm bound for every triple of length-4 sign rows. -/
theorem all_rows_4 {a b c : List Int} (ha : a ∈ signRows 4)
    (hb : b ∈ signRows 4) (hc : c ∈ signRows 4) :
    gauge inv4 (threeCoords 4 a b c) ≤ 96 :=
  gauge_le_of_check bound4 ha hb hc

/-- Every signed vertex at radius 96 is attained. -/
theorem signed_axes_4 {v : List Int} (h : v ∈ axes 2 96) :
    ∃ a ∈ signRows 4, ∃ b ∈ signRows 4, ∃ c ∈ signRows 4,
      integerImage inv4 (threeCoords 4 a b c) = v :=
  realizes_axes (W := witnesses4) (by rfl) (by rfl) h

end Lemmata.BellFollowup.Positive
