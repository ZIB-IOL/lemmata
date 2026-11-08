module

public import Lemmata.RM59.Proof.Model
public import Lemmata.RM59.Proof.F8
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.RM59.TraceGeometry

open scoped BigOperators Matrix

abbrev FieldPoint := Fin 3 → F8Scalar
abbrev FieldMatrix := Matrix (Fin 3) (Fin 3) F8Scalar

instance : Algebra Field F8Scalar := ZMod.algebra F8Scalar 2

def traceToField (a : F8Scalar) : Field := if F8Scalar.traceBit a then 1 else 0

@[simp] theorem traceToField_zero : traceToField 0 = 0 := by decide

theorem traceToField_add : ∀ a b : F8Scalar,
    traceToField (a + b) = traceToField a + traceToField b := by decide

theorem traceToField_square (a : F8Scalar) : traceToField (a ^ 2) = traceToField a := by
  simp only [traceToField, F8Scalar.traceBit, F8Scalar.trace_square]
  rfl

def traceLinear : F8Scalar →ₗ[Field] Field where
  toFun := traceToField
  map_add' := traceToField_add
  map_smul' r a := by
    rcases field_eq_zero_or_one r with rfl | rfl <;> simp

def determinantOverF2 : AlternatingMap Field FieldPoint F8Scalar (Fin 3) where
  __ := (Matrix.detRowAlternating :
    AlternatingMap F8Scalar FieldPoint F8Scalar (Fin 3)).toMultilinearMap.restrictScalars Field
  map_eq_zero_of_eq' v i j h hij := by
    change Matrix.det v = 0
    exact (Matrix.detRowAlternating :
      AlternatingMap F8Scalar FieldPoint F8Scalar (Fin 3)).map_eq_zero_of_eq v h hij

def tau : AlternatingMap Field FieldPoint Field (Fin 3) :=
  traceLinear.compAlternatingMap determinantOverF2

@[simp] theorem tau_apply (v : FieldMatrix) : tau v = traceToField v.det := rfl

theorem tau_mul_right (v A : FieldMatrix) :
    tau (v * A) = traceToField (v.det * A.det) := by
  rw [tau_apply, Matrix.det_mul]

theorem tau_mul_right_of_det_one (v A : FieldMatrix) (hA : A.det = 1) :
    tau (v * A) = tau v := by
  simp [tau_mul_right, hA]

theorem tau_mul_left (A v : FieldMatrix) :
    tau (A * v) = traceToField (A.det * v.det) := by
  rw [tau_apply, Matrix.det_mul]

def squarePoint (x : FieldPoint) : FieldPoint := fun i => x i ^ 2

theorem tau_frobenius (v : FieldMatrix) : tau (fun i => squarePoint (v i)) = tau v := by
  change traceToField (((frobenius F8Scalar 2).mapMatrix v).det) = traceToField v.det
  rw [← (frobenius F8Scalar 2).map_det]
  exact traceToField_square v.det

def covector (s x : FieldPoint) : Field := traceToField (s ⬝ᵥ x)

theorem covector_pushforward (A : FieldMatrix) (s x : FieldPoint) :
    covector s (A *ᵥ x) = covector (Aᵀ *ᵥ s) x := by
  unfold covector
  congr 1
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

def blockMatrix (D : Matrix (Fin 2) (Fin 2) F8Scalar) (t : Fin 2 → F8Scalar) :
    FieldMatrix :=
  !![D 0 0, D 0 1, 0; D 1 0, D 1 1, 0; t 0, t 1, D.det⁻¹]

theorem blockMatrix_det (D : Matrix (Fin 2) (Fin 2) F8Scalar) (t : Fin 2 → F8Scalar) :
    (blockMatrix D t).det = D.det * D.det⁻¹ := by
  simp [blockMatrix, Matrix.det_fin_three, Matrix.det_fin_two] <;> ring

theorem blockMatrix_det_one (D : Matrix (Fin 2) (Fin 2) F8Scalar)
    (t : Fin 2 → F8Scalar) (hD : D.det ≠ 0) : (blockMatrix D t).det = 1 := by
  rw [blockMatrix_det, mul_inv_cancel₀ hD]

def vertical (c : F8Scalar) : FieldPoint := ![0, 0, c]

def verticalSpace : Set FieldPoint := Set.range vertical

theorem blockMatrix_mul_vertical (D : Matrix (Fin 2) (Fin 2) F8Scalar)
    (t : Fin 2 → F8Scalar) (c : F8Scalar) :
    blockMatrix D t *ᵥ vertical c = vertical (D.det⁻¹ * c) := by
  ext i
  fin_cases i <;> simp [blockMatrix, vertical, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem blockMatrix_image_vertical (D : Matrix (Fin 2) (Fin 2) F8Scalar)
    (t : Fin 2 → F8Scalar) (hD : D.det ≠ 0) :
    (fun x => blockMatrix D t *ᵥ x) '' verticalSpace = verticalSpace := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨D.det⁻¹ * c, (blockMatrix_mul_vertical D t c).symm⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨vertical (D.det * c), ⟨D.det * c, rfl⟩, ?_⟩
    change blockMatrix D t *ᵥ vertical (D.det * c) = vertical c
    rw [blockMatrix_mul_vertical]
    simp [mul_assoc, hD]

end Lemmata.RM59.TraceGeometry
