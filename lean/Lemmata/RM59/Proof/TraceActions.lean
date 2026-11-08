module

public import Lemmata.RM59.Proof.TraceData
public import Lemmata.RM59.Proof.FrameGeometry
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace Lemmata.RM59.TraceActions

open scoped BigOperators Matrix
open Lemmata.RM59.SupportForms

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def blockIndexEquiv : Fin 3 × Fin 3 ≃ Fin 9 where
  toFun p := FieldCoordinates.blockIndex p.1 p.2
  invFun i := (FieldCoordinates.blockOf i, FieldCoordinates.indexInBlock i)
  left_inv p := Prod.ext (FieldCoordinates.blockOf_blockIndex p.1 p.2)
    (FieldCoordinates.indexInBlock_blockIndex p.1 p.2)
  right_inv := FieldCoordinates.blockIndex_parts

theorem chunk_pairing : ∀ s x : Fin 3 → Field,
    TraceGeometry.traceToField (F8Scalar.traceDual (FieldCoordinates.encodeChunk s) *
      FieldCoordinates.encodeChunk x) = ∑ i, s i * x i := by decide

theorem covector_pairing (s x : Point 9) :
    TraceGeometry.covector (FieldCoordinates.covectorEquiv s)
      (FieldCoordinates.pointEquiv x) = ∑ i, s i * x i := by
  change TraceGeometry.traceLinear (∑ j,
    F8Scalar.traceDual (FieldCoordinates.encodeChunk
      (fun k => s (FieldCoordinates.blockIndex j k))) *
      FieldCoordinates.encodeChunk (fun k => x (FieldCoordinates.blockIndex j k))) = _
  rw [map_sum]
  change (∑ j, TraceGeometry.traceToField (F8Scalar.traceDual
    (FieldCoordinates.encodeChunk (fun k => s (FieldCoordinates.blockIndex j k))) *
      FieldCoordinates.encodeChunk (fun k => x (FieldCoordinates.blockIndex j k)))) = _
  simp_rw [chunk_pairing]
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp blockIndexEquiv (fun i => s i * x i)

def matrixLinear (A : FieldMatrix) : FieldPoint →ₗ[Field] FieldPoint where
  toFun x := A *ᵥ x
  map_add' := Matrix.mulVec_add A
  map_smul' r x := by
    rcases field_eq_zero_or_one r with rfl | rfl <;> simp

def pointAction (A : FieldMatrix) : Point 9 →ₗ[Field] Point 9 :=
  FieldCoordinates.pointEquiv.symm.toLinearMap.comp
    ((matrixLinear A).comp FieldCoordinates.pointEquiv.toLinearMap)

def dualAction (A : FieldMatrix) : Point 9 →ₗ[Field] Point 9 :=
  FieldCoordinates.covectorEquiv.symm.toLinearMap.comp
    ((matrixLinear Aᵀ).comp FieldCoordinates.covectorEquiv.toLinearMap)

@[simp] theorem pointAction_coordinates (A : FieldMatrix) (x : Point 9) :
    FieldCoordinates.pointEquiv (pointAction A x) = A *ᵥ FieldCoordinates.pointEquiv x := by
  change FieldCoordinates.pointEquiv (FieldCoordinates.pointEquiv.symm _) = _
  exact FieldCoordinates.pointEquiv.apply_symm_apply _

@[simp] theorem dualAction_coordinates (A : FieldMatrix) (s : Point 9) :
    FieldCoordinates.covectorEquiv (dualAction A s) =
      Aᵀ *ᵥ FieldCoordinates.covectorEquiv s := by
  change FieldCoordinates.covectorEquiv (FieldCoordinates.covectorEquiv.symm _) = _
  exact FieldCoordinates.covectorEquiv.apply_symm_apply _

theorem pointAction_injective (A : FieldMatrix) (hA : A.det ≠ 0) :
    Function.Injective (pointAction A) := by
  intro x y h
  apply FieldCoordinates.pointEquiv.injective
  have hm := congrArg FieldCoordinates.pointEquiv h
  rw [pointAction_coordinates, pointAction_coordinates] at hm
  have hi := congrArg (fun z : FieldPoint => A⁻¹ *ᵥ z) hm
  simpa only [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec] using hi

theorem evaluation_pointAction (A : FieldMatrix) (x s : Point 9) :
    evaluation (pointAction A x) s = evaluation x (dualAction A s) := by
  change (∑ i, s i * pointAction A x i) = ∑ i, dualAction A s i * x i
  calc
    _ = TraceGeometry.covector (FieldCoordinates.covectorEquiv s)
        (FieldCoordinates.pointEquiv (pointAction A x)) :=
      (covector_pairing s (pointAction A x)).symm
    _ = TraceGeometry.covector (Aᵀ *ᵥ FieldCoordinates.covectorEquiv s)
        (FieldCoordinates.pointEquiv x) := by
      rw [pointAction_coordinates, TraceGeometry.covector_pushforward]
    _ = TraceGeometry.covector (FieldCoordinates.covectorEquiv (dualAction A s))
        (FieldCoordinates.pointEquiv x) := by rw [dualAction_coordinates]
    _ = _ := covector_pairing (dualAction A s) x

theorem pullback_pointAction (A : FieldMatrix) : pullback (pointAction A) = dualAction A := by
  apply LinearMap.ext
  intro s
  funext i
  change evaluation (pointAction A (Pi.single i 1)) s = dualAction A s i
  rw [evaluation_pointAction, evaluation_comm, evaluation_single]

theorem traceForm_dualAction (A : FieldMatrix) (hA : A.det = 1)
    (v : Fin 3 → Point 9) :
    TraceData.traceForm (fun r => dualAction A (v r)) = TraceData.traceForm v := by
  let M : FieldMatrix := Matrix.of fun r => FieldCoordinates.covectorEquiv (v r)
  have hm : (Matrix.of fun r => FieldCoordinates.covectorEquiv (dualAction A (v r))) =
      M * A := by
    ext i j
    change FieldCoordinates.covectorEquiv (dualAction A (v i)) j = (M * A) i j
    rw [dualAction_coordinates, Matrix.mulVec_transpose]
    rfl
  change TraceGeometry.tau (Matrix.of fun r =>
    FieldCoordinates.covectorEquiv (dualAction A (v r))) = TraceGeometry.tau M
  rw [hm]
  exact TraceGeometry.tau_mul_right_of_det_one M A hA

theorem traceForm_comp_pullback (A : FieldMatrix) (hA : A.det = 1) :
    TraceData.traceForm.compLinearMap (fun _ => pullback (pointAction A)) =
      TraceData.traceForm := by
  apply MultilinearMap.ext
  intro v
  simp only [MultilinearMap.compLinearMap_apply, pullback_pointAction]
  exact traceForm_dualAction A hA v

theorem support35_image_moments (A : FieldMatrix) (hA : A.det = 1) :
    MatchSupportMoments 3
      ((Packed.decodeWord FieldData.support35).image (pointAction A))
      (Packed.decodeWord FieldData.support35) := by
  have hg := pointAction_injective A (by rw [hA]; exact one_ne_zero)
  apply matchSupportMoments_of_supportForm_eq
  · calc
      supportForm ((Packed.decodeWord FieldData.support35).image (pointAction A)) =
          (supportForm (Packed.decodeWord FieldData.support35)).compLinearMap
            (fun _ => pullback (pointAction A)) := supportForm_image _ _ hg
      _ = TraceData.traceForm.compLinearMap (fun _ => pullback (pointAction A)) := by
        rw [TraceData.support35_form_eq_traceForm]
      _ = TraceData.traceForm := traceForm_comp_pullback A hA
      _ = supportForm (Packed.decodeWord FieldData.support35) :=
        TraceData.support35_form_eq_traceForm.symm
  · simp only [supportMoment, monomial_empty]
    rw [Finset.sum_image hg.injOn]

end Lemmata.RM59.TraceActions
