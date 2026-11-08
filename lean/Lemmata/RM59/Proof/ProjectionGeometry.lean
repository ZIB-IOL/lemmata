module

public import Lemmata.RM59.Proof.ProjectionChecks
public import Lemmata.RM59.Proof.TraceVertical
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Lemmata.RM59.ProjectionGeometry

open scoped BigOperators Matrix

abbrev Row (K : Type*) := Fin 4 → K

section Algebra

variable {K : Type*} [_root_.Field K]

def pivotMinor (a b : Row K) (p q : Fin 4) : K := a p * b q - a q * b p

def reducer (a b : Row K) (p q : Fin 4) : Matrix (Fin 2) (Fin 2) K :=
  let d := (pivotMinor a b p q)⁻¹
  !![d * b q, -(d * a q); -(d * b p), d * a p]

def topRows (a b : Row K) (p q : Fin 4) : Fin 2 → Row K :=
  fun i j => reducer a b p q i 0 * a j + reducer a b p q i 1 * b j

def residual (a b c : Row K) (p q : Fin 4) : Row K := fun j =>
  pivotMinor a b p q * c j -
    (pivotMinor a b p q * c p) * topRows a b p q 0 j -
    (pivotMinor a b p q * c q) * topRows a b p q 1 j

def lowerRow (a b c : Row K) (p q : Fin 4) : Fin 2 → K := fun i =>
  -(pivotMinor a b p q * c p) * reducer a b p q 0 i -
    (pivotMinor a b p q * c q) * reducer a b p q 1 i

def block (D : Matrix (Fin 2) (Fin 2) K) (t : Fin 2 → K) (d : K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![D 0 0, D 0 1, 0; D 1 0, D 1 1, 0; t 0, t 1, d]

def normalizingMatrix (a b c : Row K) (p q : Fin 4) : Matrix (Fin 3) (Fin 3) K :=
  block (reducer a b p q) (lowerRow a b c p q) (pivotMinor a b p q)

def column (a b c : Row K) (j : Fin 4) : Fin 3 → K := ![a j, b j, c j]

theorem reducer_det (a b : Row K) (p q : Fin 4) (hd : pivotMinor a b p q ≠ 0) :
    (reducer a b p q).det = (pivotMinor a b p q)⁻¹ := by
  have hd' : a p * b q - a q * b p ≠ 0 := hd
  simp only [reducer, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, pivotMinor]
  field_simp [hd'] <;> ring

theorem top_pivots (a b : Row K) (p q : Fin 4) (hd : pivotMinor a b p q ≠ 0) :
    topRows a b p q 0 p = 1 ∧ topRows a b p q 0 q = 0 ∧
      topRows a b p q 1 p = 0 ∧ topRows a b p q 1 q = 1 := by
  have hd' : a p * b q - a q * b p ≠ 0 := hd
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [topRows, reducer, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, pivotMinor] <;>
    field_simp [hd'] <;> ring

theorem residual_pivots (a b c : Row K) (p q : Fin 4) (hd : pivotMinor a b p q ≠ 0) :
    residual a b c p q p = 0 ∧ residual a b c p q q = 0 := by
  obtain ⟨h0p, h0q, h1p, h1q⟩ := top_pivots a b p q hd
  simp only [residual, h0p, h0q, h1p, h1q, mul_one, mul_zero,
    sub_self, sub_zero, and_self]

theorem block_det (D : Matrix (Fin 2) (Fin 2) K) (t : Fin 2 → K) (d : K) :
    (block D t d).det = D.det * d := by
  simp [block, Matrix.det_fin_three, Matrix.det_fin_two] <;> ring

theorem normalizingMatrix_det (a b c : Row K) (p q : Fin 4)
    (hd : pivotMinor a b p q ≠ 0) : (normalizingMatrix a b c p q).det = 1 := by
  rw [normalizingMatrix, block_det, reducer_det a b p q hd, inv_mul_cancel₀ hd]

theorem normalizingMatrix_apply (a b c : Row K) (p q j : Fin 4) :
    normalizingMatrix a b c p q *ᵥ column a b c j =
      column (topRows a b p q 0) (topRows a b p q 1) (residual a b c p q) j := by
  ext i
  fin_cases i <;>
    simp [normalizingMatrix, block, column, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, topRows, residual, lowerRow] <;> ring

theorem top_zero_formula (a b : Row K) (p q j : Fin 4) :
    topRows a b p q 0 j = (pivotMinor a b p q)⁻¹ * (b q * a j - a q * b j) := by
  simp only [topRows, reducer, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem top_one_formula (a b : Row K) (p q j : Fin 4) :
    topRows a b p q 1 j = (pivotMinor a b p q)⁻¹ * (-(b p) * a j + a p * b j) := by
  simp only [topRows, reducer, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end Algebra

theorem f8_neg (a : F8Scalar) : -a = a := rfl

theorem top_one_formula_f8 (a b : Row F8Scalar) (p q j : Fin 4) :
    topRows a b p q 1 j = (pivotMinor a b p q)⁻¹ * (b p * a j - a p * b j) := by
  rw [top_one_formula]
  simp only [sub_eq_add_neg, f8_neg]

theorem normalizingMatrix_eq_block (a b c : Row F8Scalar) (p q : Fin 4)
    (hd : pivotMinor a b p q ≠ 0) :
    normalizingMatrix a b c p q =
      TraceGeometry.blockMatrix (reducer a b p q) (lowerRow a b c p q) := by
  simp only [normalizingMatrix, block, TraceGeometry.blockMatrix,
    reducer_det a b p q hd, inv_inv]

theorem normalizingMatrix_image_vertical (a b c : Row F8Scalar) (p q : Fin 4)
    (hd : pivotMinor a b p q ≠ 0) :
    (fun x => normalizingMatrix a b c p q *ᵥ x) '' TraceGeometry.verticalSpace =
      TraceGeometry.verticalSpace := by
  rw [normalizingMatrix_eq_block a b c p q hd]
  apply TraceGeometry.blockMatrix_image_vertical
  rw [reducer_det a b p q hd]
  exact inv_ne_zero hd

theorem normalizingMatrix_moments (a b c : Row F8Scalar) (p q : Fin 4)
    (hd : pivotMinor a b p q ≠ 0) :
    MatchSupportMoments 3 ((Packed.decodeWord FieldData.support53).image
      (TraceActions.pointAction (normalizingMatrix a b c p q)))
      (Packed.decodeWord FieldData.support53) := by
  rw [normalizingMatrix_eq_block a b c p q hd]
  apply TraceVertical.support53_block_moments
  rw [reducer_det a b p q hd]
  exact inv_ne_zero hd

end Lemmata.RM59.ProjectionGeometry
