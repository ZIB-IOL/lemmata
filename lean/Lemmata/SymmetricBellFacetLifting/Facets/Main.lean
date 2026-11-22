module

public import Lemmata.SymmetricBellFacetLifting.Facets.Faces

/-! # The edge in the two independent signed-convolution coordinates

The chart uses the coefficient of X⁰ in ABC modulo X⁴+1 and the difference
of the coefficients of X¹ and X³. The formal facet criterion is maximality
among proper exposed faces. -/

@[expose] public section
noncomputable section
open Set Lemmata.SymmetricBellCrossPolytope
namespace Lemmata.SymmetricBellFacetLifting.Facets

/-- The other unnormalized real, even negacyclic coefficient, d₁−d₃. -/
def d13 : V →L[ℝ] ℝ :=
  (entry 0 0 1 + entry 0 1 0 + entry 1 0 0 + entry 1 3 3 +
    entry 2 2 3 + entry 2 3 2 + entry 3 1 3 + entry 3 2 2 +
    entry 3 3 1 + entry 3 3 3) -
  (entry 0 0 3 + entry 0 1 2 + entry 0 2 1 + entry 0 2 3 +
    entry 0 3 0 + entry 0 3 2 + entry 1 0 2 + entry 1 1 1 +
    entry 1 1 3 + entry 1 2 0 + entry 1 2 2 + entry 1 3 1 +
    entry 2 0 1 + entry 2 0 3 + entry 2 1 0 + entry 2 1 2 +
    entry 2 2 1 + entry 2 3 0 + entry 3 0 0 + entry 3 0 2 +
    entry 3 1 1 + entry 3 2 0)

def chart (p : V) : ℝ × ℝ := (d0 p, d13 p)
def chartPolytope : Set (ℝ × ℝ) := chart '' P
def chartEdge : Set (ℝ × ℝ) := {x ∈ chartPolytope | x.1 = 8}

private def lower := atom ![true,true,false,true] ![true,true,false,true] ![false,true,true,false]

private lemma lower_mem : lower ∈ P := atom_mem _ _ _

private theorem two_endpoints :
    chart positive = (8,12) ∧ chart lower = (8,-12) := by
  norm_num [chart, positive, lower, d13, d0, block000, block011, block101, block110,
    mermin, atom, signValue]

theorem top_mem : (8,12) ∈ chartEdge := by
  refine ⟨⟨positive, atom_mem _ _ _, two_endpoints.1⟩, rfl⟩

private theorem bottom_mem : (8,-12) ∈ chartEdge := by
  refine ⟨⟨lower, lower_mem, two_endpoints.2⟩, rfl⟩

theorem first_le {x : ℝ × ℝ} (h : x ∈ chartPolytope) : x.1 ≤ 8 := by
  obtain ⟨v, hv, rfl⟩ := h
  exact d0_le hv

theorem chartEdge_exposed : IsExposed ℝ chartPolytope chartEdge := by
  intro _
  refine ⟨ContinuousLinearMap.fst ℝ ℝ ℝ, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, h8⟩
    refine ⟨hx, ?_⟩
    intro y hy
    change y.1 ≤ x.1
    rw [h8]
    exact first_le hy
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, le_antisymm (first_le hx) ?_⟩
    exact hmax (8,12) top_mem.1

private theorem linear_coordinates (f : (ℝ × ℝ) →L[ℝ] ℝ) (z : ℝ × ℝ) :
    f z = z.1*f (1,0) + z.2*f (0,1) := by
  have hz : z = z.1 • ((1,0) : ℝ × ℝ) + z.2 • ((0,1) : ℝ × ℝ) := by
    ext <;> simp
  calc
    f z = f (z.1 • ((1,0) : ℝ × ℝ) + z.2 • ((0,1) : ℝ × ℝ)) := congrArg f hz
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

/-- Every exposed face strictly containing this edge is the whole chart
polytope. This avoids relying on a particular dimension convention. -/
theorem chartEdge_maximal {F : Set (ℝ × ℝ)} (hF : IsExposed ℝ chartPolytope F)
    (h : chartEdge ⊂ F) : F = chartPolytope := by
  have he : (8,12) ∈ F := h.le top_mem
  have he' : (8,-12) ∈ F := h.le bottom_mem
  obtain ⟨f, hf⟩ := hF ⟨_, he⟩
  have hmax {p : ℝ × ℝ} (hp : p ∈ F) :
      p ∈ chartPolytope ∧ ∀ y ∈ chartPolytope, f y ≤ f p := by
    change p ∈ {x ∈ chartPolytope | ∀ y ∈ chartPolytope, f y ≤ f x}
    rw [← hf]
    exact hp
  have same {p q : ℝ × ℝ} (hp : p ∈ F) (hq : q ∈ F) : f p = f q :=
    le_antisymm ((hmax hq).2 _ (hmax hp).1) ((hmax hp).2 _ (hmax hq).1)
  have eq0 := same he he'
  rw [linear_coordinates f (8,12), linear_coordinates f (8,-12)] at eq0
  have h1 : f (0,1) = 0 := by norm_num at eq0; linarith
  obtain ⟨u, hu, hn⟩ := Set.exists_of_ssubset h
  have hu8 : u.1 ≠ 8 := fun e => hn ⟨(hmax hu).1,e⟩
  have eq1 := same hu he
  rw [linear_coordinates f u, linear_coordinates f (8,12), h1] at eq1
  have eq2 : (u.1 - 8) * f (1,0) = 0 := by
    change u.1 * f (1,0) + u.2 * 0 = 8 * f (1,0) + 12 * 0 at eq1
    linear_combination eq1
  have h0 : f (1,0) = 0 := (mul_eq_zero.mp eq2).resolve_left (sub_ne_zero.mpr hu8)
  have zero (x : ℝ × ℝ) : f x = 0 := by rw [linear_coordinates, h0, h1]; ring
  rw [hf]
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx, fun y _ => by rw [zero y, zero x]⟩

theorem chartEdge_proper : chartEdge ⊂ chartPolytope := by
  refine lt_of_le_of_ne (fun _ h => h.1) ?_
  intro eq
  have h0 : chart intermediate ∈ chartPolytope := ⟨_, atom_mem _ _ _, rfl⟩
  rw [← eq] at h0
  have bad : d0 intermediate = 8 := h0.2
  norm_num [intermediate, d0, block000, block011, block101, block110, mermin, atom, signValue] at bad

/-- The pullback of the coordinate edge inside the local polytope is exactly
the full-space contact set, and we have both facet and nonfacet witnesses. -/
theorem chart_facet_lift_failure :
    IsExposed ℝ chartPolytope chartEdge ∧ chartEdge ⊂ chartPolytope ∧
    (∀ F : Set (ℝ × ℝ), IsExposed ℝ chartPolytope F → chartEdge ⊂ F → F = chartPolytope) ∧
    {p ∈ P | chart p ∈ chartEdge} = liftedEdge ∧
    IsExposed ℝ P liftedEdge ∧ IsExposed ℝ P intermediateFace ∧
      liftedEdge ⊂ intermediateFace ∧ intermediateFace ⊂ P := by
  refine ⟨chartEdge_exposed, chartEdge_proper, fun _ => chartEdge_maximal, ?_,
    full_exposed_face_chain⟩
  ext p
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, ⟨⟨p,h.1,rfl⟩,h.2⟩⟩

end Lemmata.SymmetricBellFacetLifting.Facets
