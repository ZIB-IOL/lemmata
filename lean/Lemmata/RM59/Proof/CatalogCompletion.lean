module

public import Lemmata.RM59.Proof.CatalogForms
public import Lemmata.RM59.Proof.CubicAction
public import Lemmata.RM59.Proof.PullbackEquiv
public import Lemmata.RM59.Proof.Reduction
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

@[expose] public section

namespace Lemmata.RM59.CatalogCompletion

open scoped symmDiff
open Packed SupportForms

def SupportCompletion (Q : Finset (Point 9)) : Prop :=
  ∀ P : Finset (Point 9), AffineIndependent Field ((↑) : P → Point 9) →
    P.card ∈ ({1, 3, 5, 7, 9} : Finset Nat) →
      ∃ G : Finset (Point 9), MatchSupportMoments 3 G Q ∧ (G ∆ P).card ≤ 31

theorem SupportCompletion.of_match {Q H : Finset (Point 9)}
    (hQ : SupportCompletion Q) (hQH : MatchSupportMoments 3 Q H) : SupportCompletion H := by
  intro P hAI hcard
  obtain ⟨G, hG, hbound⟩ := hQ P hAI hcard
  exact ⟨G, hG.trans hQH, hbound⟩

theorem SupportCompletion.image {Q : Finset (Point 9)} (hQ : SupportCompletion Q)
    (e : Point 9 ≃ₗ[Field] Point 9) : SupportCompletion (Q.image e) := by
  classical
  intro P hAI hcard
  let P' := P.image e.symm
  have hAI' : AffineIndependent Field ((↑) : P' → Point 9) := by
    have hm := hAI.map' e.symm.toAffineEquiv.toAffineMap e.symm.injective
    exact (affineIndependent_equiv (k := Field) (e.symm.toEquiv.imageFinset P)).mp hm
  have hPcard : P'.card = P.card := Finset.card_image_of_injective P e.symm.injective
  obtain ⟨G, hG, hbound⟩ := hQ P' hAI' (hPcard.symm ▸ hcard)
  have hPG : P'.image e = P := by
    dsimp only [P']
    rw [Finset.image_image]
    simp only [Function.comp_def, LinearEquiv.apply_symm_apply, Finset.image_id']
  refine ⟨G.image e, matchSupportMoments_image hG e.toLinearMap e.injective, ?_⟩
  calc
    (G.image e ∆ P).card = ((G ∆ P').image e).card := by
      rw [Finset.image_symmDiff _ _ e.injective, hPG]
    _ = (G ∆ P').card := Finset.card_image_of_injective _ e.injective
    _ ≤ 31 := hbound

theorem matchSupportMoments_of_alternatingSupportForm_eq
    {Q H : Finset (Point 9)} (hQ : LowerZero Q) (hH : LowerZero H)
    (h : alternatingSupportForm Q hQ = alternatingSupportForm H hH) :
    MatchSupportMoments 3 Q H := by
  apply matchSupportMoments_of_supportForm_eq
  · exact congrArg (fun T : CubicForm => T.toMultilinearMap) h
  · exact (hQ ∅ (by simp)).trans (hH ∅ (by simp)).symm

theorem matching_support_of_smul {Q H : Finset (Point 9)}
    (hQ : LowerZero Q) (hH : LowerZero H) (g : CoordinateGroup 9)
    (h : g • alternatingSupportForm Q hQ = alternatingSupportForm H hH) :
    MatchSupportMoments 3 (Q.image (pullbackEquiv g.symm)) H := by
  apply matchSupportMoments_of_supportForm_eq
  · rw [supportForm_image_pullbackEquiv]
    exact congrArg (fun T : CubicForm => T.toMultilinearMap) h
  · have hzero := lowerZero_image Q hQ (pullbackEquiv g.symm).toLinearMap
      (pullbackEquiv g.symm).injective
    exact (hzero ∅ (by simp)).trans (hH ∅ (by simp)).symm

theorem completion_of_smul {Q H : Finset (Point 9)}
    (hQ : LowerZero Q) (hH : LowerZero H) (hcompletion : SupportCompletion Q)
    (g : CoordinateGroup 9)
    (h : g • alternatingSupportForm Q hQ = alternatingSupportForm H hH) :
    SupportCompletion H :=
  (hcompletion.image (pullbackEquiv g.symm)).of_match (matching_support_of_smul hQ hH g h)

theorem completion_of_zero_form (H : Finset (Point 9)) (hH : LowerZero H)
    (hzero : alternatingSupportForm H hH = 0) : SupportCompletion H := by
  intro P hAI hcard
  have hraw : supportForm H = 0 := congrArg (fun T : CubicForm => T.toMultilinearMap) hzero
  refine ⟨∅, ?_, ?_⟩
  · apply matchSupportMoments_of_supportForm_eq
    · simpa only [supportForm, Finset.sum_empty] using hraw.symm
    · simpa only [supportMoment, Finset.sum_empty] using (hH ∅ (by simp)).symm
  · have hc : P.card = 1 ∨ P.card = 3 ∨ P.card = 5 ∨ P.card = 7 ∨ P.card = 9 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcard
    change ((⊥ : Finset (Point 9)) ∆ P).card ≤ 31
    rw [bot_symmDiff]
    omega

theorem geometricCompletion_of_catalog
    (hcover : ∀ T : CubicForm, T = 0 ∨ ∃ family : Fin 348,
      T ∈ MulAction.orbit (CoordinateGroup 9) (CatalogForms.representative family))
    (hseeds : ∀ family : Fin 348,
      SupportCompletion (decodeWord (Certificate.seed (family.val + 1)))) :
    GeometricCompletion := by
  intro H P hH hAI hcard
  rcases hcover (alternatingSupportForm H hH) with hzero | ⟨family, hmem⟩
  · exact completion_of_zero_form H hH hzero P hAI hcard
  · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hmem
    exact completion_of_smul (Certificate.seed_support_properties family).2.2.1 hH
      (hseeds family) g hg P hAI hcard

theorem fullBound_of_catalog
    (hcover : ∀ T : CubicForm, T = 0 ∨ ∃ family : Fin 348,
      T ∈ MulAction.orbit (CoordinateGroup 9) (CatalogForms.representative family))
    (hseeds : ∀ family : Fin 348,
      SupportCompletion (decodeWord (Certificate.seed (family.val + 1)))) :
    FullBound 32 :=
  fullBound_of_geometricCompletion (geometricCompletion_of_catalog hcover hseeds)

end Lemmata.RM59.CatalogCompletion
