module

public import Lemmata.BellFollowup.Positive.Finite

@[expose] public section

namespace Lemmata.BellFollowup.Positive

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Ordered witnesses of the positive and negative coordinate axes. -/
def witnesses3 : List (List Int × List Int × List Int) :=
  [([1,1,1], [1,1,1], [-1,-1,-1]),
    ([-1,-1,-1], [1,1,1], [-1,-1,-1]),
    ([1,-1,1], [1,-1,1], [1,-1,1]),
    ([-1,1,-1], [1,-1,1], [1,-1,1])]

private theorem bound3 : checkBound 3 inv3 144 = true := by rfl

/-- Exact one-norm bound for every triple of length-3 sign rows. -/
theorem all_rows_3 {a b c : List Int} (ha : a ∈ signRows 3)
    (hb : b ∈ signRows 3) (hc : c ∈ signRows 3) :
    gauge inv3 (threeCoords 3 a b c) ≤ 144 :=
  gauge_le_of_check bound3 ha hb hc

/-- Every signed vertex at radius 144 is attained. -/
theorem signed_axes_3 {v : List Int} (h : v ∈ axes 2 144) :
    ∃ a ∈ signRows 3, ∃ b ∈ signRows 3, ∃ c ∈ signRows 3,
      integerImage inv3 (threeCoords 3 a b c) = v :=
  realizes_axes (W := witnesses3) (by rfl) (by rfl) h

end Lemmata.BellFollowup.Positive
