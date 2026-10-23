module

public import Lemmata.SpanningTreeSymmetricEF.CoordinateLowerBounds

@[expose] public section


/-! Reduction of a nonempty finite affine inequality description to an
irredundant description on its actual affine hull. No dimension or boundedness
hypothesis is needed. -/
namespace Lemmata.SpanningTreeSymmetricEF.PolyhedralReduction

open scoped BigOperators
open CoordinateLowerBounds

noncomputable section
variable {E J : Type*} [AddCommGroup E] [Module ℝ E]

/-- The retained rows describe exactly the original feasible set on its affine
hull, each row is essential, and there is a common strictly feasible point. -/
structure ReducedDescription (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ) where
  I : Finset J
  feasible_eq : feasible (affineSpan ℝ (feasible Q a)) (fun i : I => a i) = feasible Q a
  essential : ∀ i : I, ∃ z ∈ affineSpan ℝ (feasible Q a),
    a i z < 0 ∧ ∀ j : I, j ≠ i → 0 ≤ a j z
  strict : ∃ o ∈ affineSpan ℝ (feasible Q a), ∀ i : I, 0 < a i o

/-- The affine hull of the feasible points stays in the original affine slice. -/
theorem affineSpan_feasible_le (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ) :
    affineSpan ℝ (feasible Q a) ≤ Q :=
  affineSpan_le.mpr (fun _ hz => hz.1)

/-- Each essential row is positive somewhere in the feasible set: otherwise
it vanishes on the entire affine hull, contradicting essentiality. -/
theorem exists_positive_of_essential
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ) (i : J)
    (hi : ∃ z ∈ affineSpan ℝ (feasible Q a), a i z < 0) :
    ∃ x ∈ feasible Q a, 0 < a i x := by
  by_contra h
  push Not at h
  have heq : (feasible Q a).EqOn (a i) (AffineMap.const ℝ E (0 : ℝ)) := by
    intro x hx
    exact le_antisymm (h x hx) (hx.2 i)
  obtain ⟨z, hz, hneg⟩ := hi
  have hz0 : a i z = 0 := AffineMap.eqOn_affineSpan heq hz
  linarith

/-- Finitely many rows, each positive somewhere and all nonnegative everywhere
on the feasible set, have a common positive point. The empty family is allowed. -/
theorem exists_common_strict (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (hP : (feasible Q a).Nonempty) (I : Finset J)
    (hpos : ∀ i : I, ∃ x ∈ feasible Q a, 0 < a i x) :
    ∃ o ∈ feasible Q a, ∀ i : I, 0 < a i o := by
  classical
  by_cases hI : I.Nonempty
  · letI : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
    choose x hx hax using hpos
    let w : I → ℝ := fun _ => (Fintype.card I : ℝ)⁻¹
    have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hwpos (i : I) : 0 < w i := inv_pos.mpr hc
    have hw : ∑ i : I, w i = 1 := by
      simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt hc)
    refine ⟨∑ i : I, w i • x i, ⟨?_, ?_⟩, ?_⟩
    · exact SignedLift.weighted_sum_mem Q x w (fun i => (hx i).1) hw
    · intro j
      rw [SignedLift.map_weighted_sum (a j) x w hw]
      exact Finset.sum_nonneg (fun i _ => smul_nonneg (hwpos i).le ((hx i).2 j))
    · intro j
      rw [SignedLift.map_weighted_sum (a j) x w hw]
      apply Finset.sum_pos'
      · intro i _
        exact smul_nonneg (hwpos i).le ((hx i).2 j)
      · exact ⟨j, Finset.mem_univ _, mul_pos (hwpos j) (hax j)⟩
  · obtain ⟨o, ho⟩ := hP
    refine ⟨o, ho, ?_⟩
    intro i
    exact (hI ⟨i, i.property⟩).elim

/-- Minimum-cardinality selection removes all redundant rows, including those
encoding implicit equations. Strict feasibility is derived, not assumed. -/
theorem reducedDescription_exists [Fintype J]
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (hP : (feasible Q a).Nonempty) : Nonempty (ReducedDescription Q a) := by
  classical
  let H := affineSpan ℝ (feasible Q a)
  let good : Finset J → Prop := fun I => feasible H (fun i : I => a i) = feasible Q a
  have hfull : good Finset.univ := by
    apply Set.ext
    intro z
    constructor
    · intro hz
      exact ⟨affineSpan_feasible_le Q a hz.1, fun j => hz.2 ⟨j, Finset.mem_univ j⟩⟩
    · intro hz
      exact ⟨subset_affineSpan ℝ _ hz, fun j => hz.2 j⟩
  let candidates := Finset.univ.filter good
  have hcandidates : candidates.Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfull⟩⟩
  obtain ⟨I, hIc, hmin⟩ := candidates.exists_min_image Finset.card hcandidates
  have hI : good I := (Finset.mem_filter.mp hIc).2
  have hess : ∀ i : I, ∃ z ∈ H, a i z < 0 ∧ ∀ j : I, j ≠ i → 0 ≤ a j z := by
    intro i
    have hnot : ¬ good (I.erase i) := by
      intro he
      have hle := hmin (I.erase i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      exact (not_le_of_gt (Finset.card_erase_lt_of_mem i.property)) hle
    have hex : ∃ z, z ∈ feasible H (fun j : I.erase i => a j) ∧ z ∉ feasible Q a := by
      by_contra hn
      apply hnot
      apply Set.ext
      intro z
      constructor
      · intro hz
        by_contra hp
        exact hn ⟨z, hz, hp⟩
      · intro hz
        exact ⟨subset_affineSpan ℝ _ hz, fun j => hz.2 j⟩
    obtain ⟨z, hz, hp⟩ := hex
    refine ⟨z, hz.1, ?_, ?_⟩
    · by_contra hn
      apply hp
      rw [← hI]
      refine ⟨hz.1, ?_⟩
      intro j
      by_cases hji : j = i
      · subst j
        exact le_of_not_gt hn
      · exact hz.2 ⟨j, Finset.mem_erase.mpr ⟨fun he => hji (Subtype.ext he), j.property⟩⟩
    · intro j hji
      exact hz.2 ⟨j, Finset.mem_erase.mpr ⟨fun he => hji (Subtype.ext he), j.property⟩⟩
  have hpos : ∀ i : I, ∃ x ∈ feasible Q a, 0 < a i x := by
    intro i
    obtain ⟨z, hz, hneg, _⟩ := hess i
    exact exists_positive_of_essential Q a i ⟨z, hz, hneg⟩
  obtain ⟨o, ho, hstrict⟩ := exists_common_strict Q a hP I hpos
  exact ⟨⟨I, hI, hess, o, subset_affineSpan ℝ _ ho, hstrict⟩⟩

end
end Lemmata.SpanningTreeSymmetricEF.PolyhedralReduction
