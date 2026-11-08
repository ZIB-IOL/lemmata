module

public import Lemmata.RM59.Proof.ProjectionEquivalence
public import Lemmata.RM59.Proof.ProjectionTupleChecks
public import Lemmata.RM59.Proof.PackedLinear
public import Lemmata.RM59.Proof.Family35
public import Mathlib.Algebra.BigOperators.Fin
public meta import Lemmata.RM59.Proof.ProjectionChecks
public meta import Lemmata.RM59.Proof.Packed
public meta import Lemmata.RM59.Proof.Family35
public meta import Lemmata.RM59.Proof.FieldCoordinates

@[expose] public section

namespace Lemmata.RM59.ProjectionPacked

open scoped BigOperators

abbrev FieldPoint := TraceGeometry.FieldPoint

theorem coordinates_zero : FieldData.coordinates 0 = 0 := by
  rw [← FieldCoordinates.packed_coordinates, Packed.decodePoint_zero, map_zero]

theorem coordinates_xor (x y : Fin 512) :
    FieldData.coordinates (ProjectionChecks.xorPoint x y) =
      FieldData.coordinates x + FieldData.coordinates y := by
  rw [← FieldCoordinates.packed_coordinates, ← FieldCoordinates.packed_coordinates x,
    ← FieldCoordinates.packed_coordinates y]
  change FieldCoordinates.pointEquiv (Packed.decodePoint (Packed.xorPoint x y)) = _
  rw [Packed.decodePoint_xorPoint, map_add]

theorem coordinates_fold (points : List (Fin 512)) (start : Fin 512) :
    FieldData.coordinates (points.foldl ProjectionChecks.xorPoint start) =
      FieldData.coordinates start + (points.map FieldData.coordinates).sum := by
  induction points generalizing start with
  | nil => simp
  | cons x points ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, coordinates_xor]
    abel

def fieldPoints (codes : Vector (Fin 512) 5) : Fin 5 → FieldPoint :=
  fun i => FieldData.coordinates (codes.get i)

def encodePoints (points : Fin 5 → FieldPoint) : Vector (Fin 512) 5 :=
  Vector.ofFn fun i => Packed.encodePoint (FieldCoordinates.pointEquiv.symm (points i))

@[simp] theorem fieldPoints_encodePoints (points : Fin 5 → FieldPoint) :
    fieldPoints (encodePoints points) = points := by
  funext i
  simp only [fieldPoints, encodePoints, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  change FieldData.coordinates
    (Packed.encodePoint (FieldCoordinates.pointEquiv.symm (points i))) = points i
  rw [← FieldCoordinates.packed_coordinates, Packed.decodePoint_encodePoint,
    FieldCoordinates.pointEquiv.apply_symm_apply]

theorem vector_toList (codes : Vector (Fin 512) 5) :
    codes.toList = List.ofFn (fun i => codes.get i) := by
  have he : codes = Vector.ofFn (fun i => codes.get i) := by
    apply Vector.ext
    intro i hi
    simp [Vector.get]
  conv_lhs => rw [he, Vector.toList_ofFn]

theorem coordinates_center (codes : Vector (Fin 512) 5) :
    FieldData.coordinates (codes.toList.foldl ProjectionChecks.xorPoint 0) =
      ProjectionEquivalence.center (fieldPoints codes) := by
  rw [coordinates_fold, coordinates_zero, zero_add, vector_toList]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def,
    ProjectionEquivalence.center, fieldPoints]

theorem normalizeFive_vector (codes : Vector (Fin 512) 5) :
    ProjectionTupleChecks.normalizeFive codes.toList =
      ProjectionTupleChecks.normalizeRows
        (ProjectionEquivalence.rows (fieldPoints codes) 0)
        (ProjectionEquivalence.rows (fieldPoints codes) 1)
        (ProjectionEquivalence.rows (fieldPoints codes) 2) := by
  simp only [ProjectionTupleChecks.normalizeFive]
  congr 1 <;> funext j
  all_goals
    rw [coordinates_xor, coordinates_center]
    fin_cases j <;> simp [vector_toList, List.getElem?_ofFn, ProjectionEquivalence.rows,
      ProjectionEquivalence.centered, fieldPoints]

theorem decode_frobenius : ∀ (x : Fin 512) (k : Fin 3),
    Packed.decodePoint (ProjectionChecks.frobeniusPoint x k.val) =
      Family35.frobeniusPoint k.val (Packed.decodePoint x) := by native_decide

end Lemmata.RM59.ProjectionPacked
