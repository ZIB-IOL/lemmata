module

public import Lemmata.SymmetricBellFacetLifting.Chart
public import Lemmata.SymmetricBellFacetLifting.Facets.RectangleCross
public import Lemmata.SymmetricBellFacetLifting.Parity
public import Lemmata.SymmetricBellFacetLifting.Positive.Archive2
public import Lemmata.SymmetricBellFacetLifting.Positive.Archive3
public import Lemmata.SymmetricBellFacetLifting.Positive.Archive5
public import Lemmata.SymmetricBellFacetLifting.Recovery.BellEnergy
public import Lemmata.SymmetricBellFacetLifting.Recovery.Main
public import Lemmata.SymmetricBellFacetLifting.Certificates
public import Lemmata.SymmetricBellFacetLifting.Shift.Profile

public section

namespace Lemmata.SymmetricBellFacetLifting
open SymmetricBellCrossPolytope Facets

/-- The four-setting common fixed-space projection is a two-dimensional cross-polytope. -/
theorem four_setting_cross :
    ∃ f : V →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2), Set.InjOn f (Gamma 3 4 '' P) ∧
      f '' (Gamma 3 4 '' P) = crossPolytope 2 :=
  reynolds_cross_four reconstruct chart_project reconstruct_chart

/-- Affine equivalence to the standard cross-polytope in the conjectured dimension. -/
def ThreePartyCross (m : ℕ) : Prop :=
  ∃ f : Tensor 3 m →ᵃ[ℝ] EuclideanSpace ℝ (Fin ((m+1)/2)),
    Set.InjOn f (Gamma 3 m '' localPolytope 3 m) ∧
    f '' (Gamma 3 m '' localPolytope 3 m) = crossPolytope ((m+1)/2)

/-- In the original projection model the first four setting counts give cross-polytopes. -/
theorem small_setting_cross (m : ℕ) (hm : 2 ≤ m) (hm' : m ≤ 5) : ThreePartyCross m := by
  interval_cases m
  · exact Positive.Archive.M2.positive
  · exact Positive.Archive.M3.positive
  · exact four_setting_cross
  · exact Positive.Archive.M5.positive

-- DOCS_BEGIN_MAIN
/-- The four-setting projected edge is a facet, and its full-polytope lift
lies strictly inside a second proper exposed face. -/
theorem four_setting_facet_lift :
    IsExposed ℝ reynoldsPolytope reynoldsEdge ∧ reynoldsEdge ⊂ reynoldsPolytope ∧
    (∀ F : Set V, IsExposed ℝ reynoldsPolytope F → reynoldsEdge ⊂ F → F = reynoldsPolytope) ∧
    {p ∈ P | Gamma 3 4 p ∈ reynoldsEdge} = liftedEdge ∧
    IsExposed ℝ P liftedEdge ∧ IsExposed ℝ P intermediateFace ∧
    liftedEdge ⊂ intermediateFace ∧ intermediateFace ⊂ P :=
  reynolds_facet_lift_failure reconstruct chart_project reconstruct_chart
-- DOCS_END_MAIN

end Lemmata.SymmetricBellFacetLifting
