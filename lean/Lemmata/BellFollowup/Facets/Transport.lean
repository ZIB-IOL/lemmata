module

public import Lemmata.BellFollowup.Facets.Main

/-! # Transferring a facet via linear reconstruction of the Reynolds image -/

@[expose] public section
noncomputable section
open Set Lemmata.SymmetricBellCrossPolytope
namespace Lemmata.BellFollowup.Facets

def reynoldsPolytope : Set V := Gamma 3 4 '' P
def reynoldsEdge : Set V := {v ∈ reynoldsPolytope | d0 v = 8}

/-- A verified coordinate model transfers the maximal-face and nonfacet
conclusions to the orthogonal projection used in the archive's statement. -/
theorem reynolds_facet_lift_failure (R : (ℝ × ℝ) →L[ℝ] V)
    (hchart : ∀ v : V, chart (Gamma 3 4 v) = chart v)
    (hrec : ∀ v : V, R (chart v) = Gamma 3 4 v) :
    IsExposed ℝ reynoldsPolytope reynoldsEdge ∧ reynoldsEdge ⊂ reynoldsPolytope ∧
    (∀ F : Set V, IsExposed ℝ reynoldsPolytope F → reynoldsEdge ⊂ F → F = reynoldsPolytope) ∧
    {p ∈ P | Gamma 3 4 p ∈ reynoldsEdge} = liftedEdge ∧
    IsExposed ℝ P liftedEdge ∧ IsExposed ℝ P intermediateFace ∧
      liftedEdge ⊂ intermediateFace ∧ intermediateFace ⊂ P := by
  have first (v : V) : d0 (Gamma 3 4 v) = d0 v := congrArg Prod.fst (hchart v)
  have forward {v : V} (hv : v ∈ reynoldsPolytope) :
      chart v ∈ chartPolytope ∧ R (chart v) = v := by
    obtain ⟨p, hp, rfl⟩ := hv
    rw [hchart]
    exact ⟨⟨p,hp,rfl⟩, hrec p⟩
  have backward {u : ℝ × ℝ} (hu : u ∈ chartPolytope) :
      R u ∈ reynoldsPolytope ∧ chart (R u) = u := by
    obtain ⟨p, hp, rfl⟩ := hu
    rw [hrec]
    exact ⟨⟨p,hp,rfl⟩, hchart p⟩
  have edge {u : ℝ × ℝ} (hu : u ∈ chartPolytope) : R u ∈ reynoldsEdge ↔ u ∈ chartEdge := by
    have e : d0 (R u) = u.1 := congrArg Prod.fst (backward hu).2
    constructor
    · exact fun h => ⟨hu, e.symm.trans h.2⟩
    · exact fun h => ⟨(backward hu).1, e.trans h.2⟩
  have top : R (8,12) ∈ reynoldsEdge := (edge top_mem.1).2 top_mem
  have bound {v : V} (hv : v ∈ reynoldsPolytope) : d0 v ≤ 8 :=
    first_le (forward hv).1
  refine ⟨?_, ?_, ?_, ?_, full_exposed_face_chain⟩
  · intro _
    refine ⟨d0,?_⟩
    ext v
    constructor
    · rintro ⟨h, e⟩
      exact ⟨h, fun y hy => (bound hy).trans_eq e.symm⟩
    · rintro ⟨h, hmax⟩
      refine ⟨h, le_antisymm (bound h) ?_⟩
      have htop := hmax _ top.1
      rw [top.2] at htop
      exact htop
  · refine lt_of_le_of_ne (fun _ h => h.1) ?_
    obtain ⟨u, hu, hn⟩ := Set.exists_of_ssubset chartEdge_proper
    intro he
    have hmem := (backward hu).1
    rw [← he] at hmem
    exact hn ((edge hu).1 hmem)
  · intro F hF hproper
    have topF := hproper.le top
    obtain ⟨f, hf⟩ := hF ⟨_, topF⟩
    let G : Set (ℝ × ℝ) := {u ∈ chartPolytope | R u ∈ F}
    have exposedG : IsExposed ℝ chartPolytope G := by
      intro _
      refine ⟨f.comp R, ?_⟩
      ext u
      constructor
      · rintro ⟨hu, hFu⟩
        rw [hf] at hFu
        exact ⟨hu, fun y hy => hFu.2 (R y) (backward hy).1⟩
      · rintro ⟨hu, hm⟩
        refine ⟨hu, ?_⟩
        rw [hf]
        refine ⟨(backward hu).1, ?_⟩
        intro y hy
        have hh := hm (chart y) (forward hy).1
        change f (R (chart y)) ≤ f (R u) at hh
        rwa [(forward hy).2] at hh
    have big : chartEdge ⊂ G := by
      refine lt_of_le_of_ne (fun u hu => ⟨hu.1, hproper.le ((edge hu.1).2 hu)⟩) ?_
      obtain ⟨x,hxF,hn⟩ := Set.exists_of_ssubset hproper
      have hxP := (hF.subset hxF)
      have xx := forward hxP
      have hxG : chart x ∈ G := ⟨xx.1, xx.2.symm ▸ hxF⟩
      intro he
      rw [← he] at hxG
      exact hn ⟨hxP,hxG.2⟩
    have eqG := chartEdge_maximal exposedG big
    refine Set.Subset.antisymm hF.subset ?_
    intro x hx
    have xx := forward hx
    have hxG : chart x ∈ G := eqG.symm ▸ xx.1
    exact xx.2 ▸ hxG.2
  · ext p
    constructor
    · rintro ⟨h, hG⟩
      exact ⟨h, (first p).symm.trans hG.2⟩
    · rintro ⟨h, h8⟩
      exact ⟨h, ⟨⟨p,h,rfl⟩, (first p).trans h8⟩⟩

end Lemmata.BellFollowup.Facets
