module

public import Lemmata.RM59.Proof.TraceFrobenius
public meta import Lemmata.RM59.Proof.FieldData
public meta import Lemmata.RM59.Proof.Packed

@[expose] public section

namespace Lemmata.RM59.TraceVertical

open scoped Matrix
open Lemmata.RM59.SupportForms

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def verticalSupport : Finset (Point 9) := Packed.decodeWord FieldData.verticalFlat

theorem packed_vertical_mem : ∀ p : Packed.PackedPoint,
    p ∈ FieldData.verticalFlat ↔ FieldData.coordinates p 0 = 0 ∧
      FieldData.coordinates p 1 = 0 := by native_decide

theorem verticalSpace_mem (x : FieldPoint) :
    x ∈ TraceGeometry.verticalSpace ↔ x 0 = 0 ∧ x 1 = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [TraceGeometry.vertical]
  · rintro ⟨h0, h1⟩
    refine ⟨x 2, ?_⟩
    ext i
    fin_cases i <;> simp [TraceGeometry.vertical, h0, h1]

theorem decoded_vertical_mem (x : Point 9) :
    x ∈ verticalSupport ↔ FieldCoordinates.pointEquiv x ∈ TraceGeometry.verticalSpace := by
  obtain ⟨p, hp⟩ := Packed.pointEquiv.surjective x
  rw [← hp]
  change Packed.decodePoint p ∈ Packed.decodeWord FieldData.verticalFlat ↔
    FieldCoordinates.pointEquiv (Packed.decodePoint p) ∈ TraceGeometry.verticalSpace
  rw [FieldCoordinates.packed_coordinates, verticalSpace_mem]
  simpa [Packed.decodeWord, Packed.decodePoint_injective.eq_iff] using packed_vertical_mem p

theorem image_vertical_of_coordinates (g : Point 9 → Point 9) (f : FieldPoint → FieldPoint)
    (hg : ∀ x, FieldCoordinates.pointEquiv (g x) = f (FieldCoordinates.pointEquiv x))
    (hf : f '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace) :
    verticalSupport.image g = verticalSupport := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply (decoded_vertical_mem _).2
    rw [hg, ← hf]
    exact ⟨FieldCoordinates.pointEquiv y, (decoded_vertical_mem y).1 hy, rfl⟩
  · intro hx
    have hu : FieldCoordinates.pointEquiv x ∈ f '' TraceGeometry.verticalSpace := by
      rw [hf]
      exact (decoded_vertical_mem x).1 hx
    obtain ⟨u, hu, he⟩ := hu
    apply Finset.mem_image.mpr
    refine ⟨FieldCoordinates.pointEquiv.symm u, ?_, ?_⟩
    · apply (decoded_vertical_mem _).2
      simpa only [FieldCoordinates.pointEquiv.apply_symm_apply] using hu
    · apply FieldCoordinates.pointEquiv.injective
      rw [hg, FieldCoordinates.pointEquiv.apply_symm_apply]
      exact he

theorem matrix_image_vertical (A : FieldMatrix)
    (hK : (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace) :
    verticalSupport.image (TraceActions.pointAction A) = verticalSupport :=
  image_vertical_of_coordinates _ _ (TraceActions.pointAction_coordinates A) hK

theorem square_vertical (c : F8Scalar) :
    TraceFrobenius.squareLinear (TraceGeometry.vertical c) = TraceGeometry.vertical (c ^ 2) := by
  ext i
  fin_cases i <;> simp [TraceFrobenius.squareLinear, TraceGeometry.squarePoint,
    TraceGeometry.vertical]

theorem square_image_vertical :
    TraceFrobenius.squareLinear '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c ^ 2, (square_vertical c).symm⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨TraceGeometry.vertical (c ^ 4), ⟨c ^ 4, rfl⟩, ?_⟩
    change TraceFrobenius.squareLinear (TraceGeometry.vertical (c ^ 4)) = TraceGeometry.vertical c
    rw [square_vertical]
    congr 1
    simpa only [← pow_mul] using F8Scalar.pow_eight c

theorem frobenius_image_vertical :
    verticalSupport.image TraceFrobenius.pointAction = verticalSupport :=
  image_vertical_of_coordinates _ _ TraceFrobenius.pointAction_coordinates square_image_vertical

theorem support53_image_moments (g : Point 9 →ₗ[Field] Point 9)
    (hg : Function.Injective g)
    (htrace : TraceData.traceForm.compLinearMap (fun _ => pullback g) = TraceData.traceForm)
    (hK : verticalSupport.image g = verticalSupport) :
    MatchSupportMoments 3 ((Packed.decodeWord FieldData.support53).image g)
      (Packed.decodeWord FieldData.support53) := by
  have hKform : (supportForm verticalSupport).compLinearMap (fun _ => pullback g) =
      supportForm verticalSupport := by
    rw [← supportForm_image verticalSupport g hg, hK]
  apply matchSupportMoments_of_supportForm_eq
  · calc
      supportForm ((Packed.decodeWord FieldData.support53).image g) =
          (supportForm (Packed.decodeWord FieldData.support53)).compLinearMap
            (fun _ => pullback g) := supportForm_image _ _ hg
      _ = (TraceData.traceForm + supportForm verticalSupport).compLinearMap
          (fun _ => pullback g) := by
        simpa only [verticalSupport] using congrArg
          (fun f : MultilinearMap Field (fun _ : Fin 3 => Point 9) Field =>
            f.compLinearMap (fun _ => pullback g))
          TraceData.support53_form_eq_traceForm_add_vertical
      _ = TraceData.traceForm.compLinearMap (fun _ => pullback g) +
          (supportForm verticalSupport).compLinearMap (fun _ => pullback g) := by
        apply MultilinearMap.ext
        intro v
        rfl
      _ = TraceData.traceForm + supportForm verticalSupport := by rw [htrace, hKform]
      _ = supportForm (Packed.decodeWord FieldData.support53) :=
        TraceData.support53_form_eq_traceForm_add_vertical.symm
  · simp only [supportMoment, monomial_empty]
    rw [Finset.sum_image hg.injOn]

theorem support53_block_moments (D : Matrix (Fin 2) (Fin 2) F8Scalar)
    (t : Fin 2 → F8Scalar) (hD : D.det ≠ 0) :
    MatchSupportMoments 3 ((Packed.decodeWord FieldData.support53).image
      (TraceActions.pointAction (TraceGeometry.blockMatrix D t)))
      (Packed.decodeWord FieldData.support53) := by
  have hA := TraceGeometry.blockMatrix_det_one D t hD
  exact support53_image_moments _
    (TraceActions.pointAction_injective _ (by rw [hA]; exact one_ne_zero))
    (TraceActions.traceForm_comp_pullback _ hA)
    (matrix_image_vertical _ (TraceGeometry.blockMatrix_image_vertical D t hD))

theorem support53_frobenius_moments :
    MatchSupportMoments 3 ((Packed.decodeWord FieldData.support53).image TraceFrobenius.pointAction)
      (Packed.decodeWord FieldData.support53) :=
  support53_image_moments _ TraceFrobenius.pointAction_injective
    TraceFrobenius.traceForm_comp_pullback frobenius_image_vertical

end Lemmata.RM59.TraceVertical
