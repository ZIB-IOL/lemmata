module

public import Lemmata.BellFollowup.Frequency.Range
public import Lemmata.BellFollowup.Positive.Main

public section
namespace Lemmata.BellFollowup
open Frequency Lemmata.BellFollowup.Positive

/-- Real convex-hull exclusion for three computed, signed-strategy profiles. -/
theorem three_shifted_separations :
    realProfile (shifted 17) ∉ frequencyHull 17 ∧
    realProfile (shifted 28) ∉ frequencyHull 28 ∧
    realProfile (shifted 32) ∉ frequencyHull 32 :=
  ⟨shifted17_outside, shifted28_outside, shifted32_outside⟩

/-- Finite three-party charts with all deterministic strategy rows allowed. -/
theorem four_small_hulls :
    convexHull ℝ (chartAtoms 2 1 4 inv2) = unitCross 1 ∧
    convexHull ℝ (chartAtoms 3 2 144 inv3) = unitCross 2 ∧
    convexHull ℝ (chartAtoms 4 2 96 inv4) = unitCross 2 ∧
    convexHull ℝ (chartAtoms 5 3 3200 inv5) = unitCross 3 :=
  ⟨positive_2, positive_3, positive_4, positive_5⟩

/-- The closed candidate profiles are strictly separated throughout both finite ranges. -/
theorem closed_range_separation :
    (∀ i : Fin 38, realProfile (reducedShifted (17+2*i.val)) ∉ signedHull (reducedCandidate (17+2*i.val))) ∧
    (∀ i : Fin 32, realProfile (reducedShifted (28+2*i.val)) ∉ signedHull (reducedCandidate (28+2*i.val))) :=
  ⟨oddRange_outside, evenRange_outside⟩


end Lemmata.BellFollowup
