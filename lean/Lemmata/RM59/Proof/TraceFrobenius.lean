module

public import Lemmata.RM59.Proof.TraceActions

@[expose] public section

namespace Lemmata.RM59.TraceFrobenius

open scoped BigOperators Matrix
open Lemmata.RM59.SupportForms

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def squareLinear : FieldPoint →ₗ[Field] FieldPoint where
  toFun := TraceGeometry.squarePoint
  map_add' x y := by
    funext i
    exact (frobenius F8Scalar 2).map_add (x i) (y i)
  map_smul' r x := by
    rcases field_eq_zero_or_one r with rfl | rfl
    · simp only [RingHom.id_apply, zero_smul]
      funext i
      simp [TraceGeometry.squarePoint]
    · simp only [RingHom.id_apply, one_smul]

def fourthLinear : FieldPoint →ₗ[Field] FieldPoint := squareLinear.comp squareLinear

@[simp] theorem squareLinear_apply (x : FieldPoint) (i : Fin 3) :
    squareLinear x i = x i ^ 2 := rfl

@[simp] theorem fourthLinear_apply (x : FieldPoint) (i : Fin 3) :
    fourthLinear x i = (x i ^ 2) ^ 2 := rfl

theorem square_fourth (x : FieldPoint) : squareLinear (fourthLinear x) = x := by
  funext i
  change ((x i ^ 2) ^ 2) ^ 2 = x i
  simpa only [← pow_mul] using F8Scalar.pow_eight (x i)

theorem fourth_square (x : FieldPoint) : fourthLinear (squareLinear x) = x :=
  square_fourth x

def pointAction : Point 9 →ₗ[Field] Point 9 :=
  FieldCoordinates.pointEquiv.symm.toLinearMap.comp
    (squareLinear.comp FieldCoordinates.pointEquiv.toLinearMap)

def dualAction : Point 9 →ₗ[Field] Point 9 :=
  FieldCoordinates.covectorEquiv.symm.toLinearMap.comp
    (fourthLinear.comp FieldCoordinates.covectorEquiv.toLinearMap)

@[simp] theorem pointAction_coordinates (x : Point 9) :
    FieldCoordinates.pointEquiv (pointAction x) = squareLinear (FieldCoordinates.pointEquiv x) := by
  change FieldCoordinates.pointEquiv (FieldCoordinates.pointEquiv.symm _) = _
  exact FieldCoordinates.pointEquiv.apply_symm_apply _

@[simp] theorem dualAction_coordinates (s : Point 9) :
    FieldCoordinates.covectorEquiv (dualAction s) =
      fourthLinear (FieldCoordinates.covectorEquiv s) := by
  change FieldCoordinates.covectorEquiv (FieldCoordinates.covectorEquiv.symm _) = _
  exact FieldCoordinates.covectorEquiv.apply_symm_apply _

theorem pointAction_injective : Function.Injective pointAction := by
  intro x y h
  apply FieldCoordinates.pointEquiv.injective
  have hm := congrArg FieldCoordinates.pointEquiv h
  rw [pointAction_coordinates, pointAction_coordinates] at hm
  have hi := congrArg fourthLinear hm
  simpa only [fourth_square] using hi

theorem scalar_duality : ∀ a x : F8Scalar,
    TraceGeometry.traceToField (a * x ^ 2) =
      TraceGeometry.traceToField (a ^ 4 * x) := by decide

theorem covector_square (s x : FieldPoint) :
    TraceGeometry.covector s (squareLinear x) =
      TraceGeometry.covector (fourthLinear s) x := by
  change TraceGeometry.traceLinear (∑ i : Fin 3, s i * squareLinear x i) =
    TraceGeometry.traceLinear (∑ i : Fin 3, fourthLinear s i * x i)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [squareLinear_apply, fourthLinear_apply]
  change TraceGeometry.traceToField (s i * x i ^ 2) =
    TraceGeometry.traceToField ((s i ^ 2) ^ 2 * x i)
  rw [← pow_mul]
  change TraceGeometry.traceToField (s i * x i ^ 2) =
    TraceGeometry.traceToField (s i ^ 4 * x i)
  exact scalar_duality (s i) (x i)

theorem evaluation_pointAction (x s : Point 9) :
    evaluation (pointAction x) s = evaluation x (dualAction s) := by
  change (∑ i, s i * pointAction x i) = ∑ i, dualAction s i * x i
  calc
    _ = TraceGeometry.covector (FieldCoordinates.covectorEquiv s)
        (FieldCoordinates.pointEquiv (pointAction x)) :=
      (TraceActions.covector_pairing s (pointAction x)).symm
    _ = TraceGeometry.covector (fourthLinear (FieldCoordinates.covectorEquiv s))
        (FieldCoordinates.pointEquiv x) := by rw [pointAction_coordinates, covector_square]
    _ = TraceGeometry.covector (FieldCoordinates.covectorEquiv (dualAction s))
        (FieldCoordinates.pointEquiv x) := by rw [dualAction_coordinates]
    _ = _ := TraceActions.covector_pairing (dualAction s) x

theorem pullback_pointAction : pullback pointAction = dualAction := by
  apply LinearMap.ext
  intro s
  funext i
  change evaluation (pointAction (Pi.single i 1)) s = dualAction s i
  rw [evaluation_pointAction, evaluation_comm, evaluation_single]

theorem traceForm_dualAction (v : Fin 3 → Point 9) :
    TraceData.traceForm (fun r => dualAction (v r)) = TraceData.traceForm v := by
  change TraceGeometry.tau (Matrix.of fun r =>
    FieldCoordinates.covectorEquiv (dualAction (v r))) =
      TraceGeometry.tau (Matrix.of fun r => FieldCoordinates.covectorEquiv (v r))
  simp_rw [dualAction_coordinates]
  calc
    _ = TraceGeometry.tau (Matrix.of fun r =>
        TraceGeometry.squarePoint (FieldCoordinates.covectorEquiv (v r))) :=
      TraceGeometry.tau_frobenius (Matrix.of fun r =>
        TraceGeometry.squarePoint (FieldCoordinates.covectorEquiv (v r)))
    _ = _ := TraceGeometry.tau_frobenius _

theorem traceForm_comp_pullback :
    TraceData.traceForm.compLinearMap (fun _ => pullback pointAction) =
      TraceData.traceForm := by
  apply MultilinearMap.ext
  intro v
  simp only [MultilinearMap.compLinearMap_apply, pullback_pointAction]
  exact traceForm_dualAction v

theorem support35_image_moments :
    MatchSupportMoments 3 ((Packed.decodeWord FieldData.support35).image pointAction)
      (Packed.decodeWord FieldData.support35) := by
  apply matchSupportMoments_of_supportForm_eq
  · calc
      supportForm ((Packed.decodeWord FieldData.support35).image pointAction) =
          (supportForm (Packed.decodeWord FieldData.support35)).compLinearMap
            (fun _ => pullback pointAction) := supportForm_image _ _ pointAction_injective
      _ = TraceData.traceForm.compLinearMap (fun _ => pullback pointAction) := by
        rw [TraceData.support35_form_eq_traceForm]
      _ = TraceData.traceForm := traceForm_comp_pullback
      _ = supportForm (Packed.decodeWord FieldData.support35) :=
        TraceData.support35_form_eq_traceForm.symm
  · simp only [supportMoment, monomial_empty]
    rw [Finset.sum_image pointAction_injective.injOn]

end Lemmata.RM59.TraceFrobenius
