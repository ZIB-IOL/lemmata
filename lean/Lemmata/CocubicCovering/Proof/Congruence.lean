module

public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine
public import Lemmata.CocubicCovering.Proof.Linear
public meta import Lemmata.CocubicCovering.Proof.Linear
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringCongruence

open scoped BigOperators
open CoveringAffine

def coefficientMatrix {d n : ℕ} (rows : Fin d → Fin d → ℕ)
    (v : Vector n) : Matrix (Fin d) (Fin d) Field :=
  fun i j => evalRow (rows i j) v

def columnMatrix {d : ℕ} (columns : Fin d → ℕ) : Matrix (Fin d) (Fin d) Field :=
  fun i j => if (columns j).testBit i.val then 1 else 0

def congruenceRow {d : ℕ} (rows : Fin d → Fin d → ℕ) (a b : ℕ) : ℕ :=
  composeRow a (fun i => composeRow b (rows i))

theorem evalRow_congruenceRow {d n : ℕ} (rows : Fin d → Fin d → ℕ)
    (a b : ℕ) (v : Vector n) :
    evalRow (congruenceRow rows a b) v =
      ∑ i : Fin d, if a.testBit i.val then
        ∑ j : Fin d, if b.testBit j.val then evalRow (rows i j) v else 0
      else 0 := by
  rw [congruenceRow, evalRow_composeRow]
  change (∑ i : Fin d, if a.testBit i.val then
    evalRow (composeRow b (rows i)) v else 0) = _
  apply Finset.sum_congr rfl
  intro i hi
  split
  · rw [evalRow_composeRow]
    rfl
  · rfl

theorem covariance_of_rows {d n : ℕ} (rows : Fin d → Fin d → ℕ)
    (columns : Fin d → ℕ) (parameterRows : Fin n → ℕ)
    (identity : ∀ i j, composeRow (rows i j) parameterRows =
      congruenceRow rows (columns i) (columns j)) (v : Vector n) :
    coefficientMatrix rows (rowMap parameterRows v) =
      (columnMatrix columns).transpose *
        (coefficientMatrix rows v * columnMatrix columns) := by
  ext i j
  change evalRow (rows i j) (rowMap parameterRows v) = _
  rw [← evalRow_composeRow, identity i j, evalRow_congruenceRow]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columnMatrix, coefficientMatrix]
  apply Finset.sum_congr rfl
  intro a ha
  cases h : (columns i).testBit a.val
  · simp
  · simp only [ite_true, one_mul]
    apply Finset.sum_congr rfl
    intro b hb
    cases (columns j).testBit b.val <;> simp

theorem columnMatrix_toLin_eq_rowMap {d : ℕ} (columns rows : Fin d → ℕ)
    (transpose : ∀ i j, (rows i).testBit j.val = (columns j).testBit i.val) :
    (columnMatrix columns).toLin' = rowMap rows := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, columnMatrix,
    rowMap, evalRow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [transpose i j]
  cases (columns j).testBit i.val <;> simp

theorem bilinear_covariance_of_rows {d n : ℕ} (rows : Fin d → Fin d → ℕ)
    (columns : Fin d → ℕ) (parameterRows : Fin n → ℕ)
    (identity : ∀ i j, composeRow (rows i j) parameterRows =
      congruenceRow rows (columns i) (columns j)) (v : Vector n) :
    Matrix.toBilin' (coefficientMatrix rows (rowMap parameterRows v)) =
      Covering.gram (Matrix.toBilin' (coefficientMatrix rows v))
        (columnMatrix columns).toLin' := by
  rw [covariance_of_rows rows columns parameterRows identity v,
    ← Matrix.mul_assoc, ← Matrix.toBilin'_comp]
  rfl

theorem rank_covariance_of_rows {d n : ℕ} (rows : Fin d → Fin d → ℕ)
    (columns : Fin d → ℕ) (parameterRows : Fin n → ℕ)
    (identity : ∀ i j, composeRow (rows i j) parameterRows =
      congruenceRow rows (columns i) (columns j))
    (e : Vector d ≃ₗ[Field] Vector d)
    (he : e.toLinearMap = (columnMatrix columns).toLin') (v : Vector n) :
    Module.finrank Field (LinearMap.range
      (Matrix.toBilin' (coefficientMatrix rows (rowMap parameterRows v)))) =
    Module.finrank Field (LinearMap.range
      (Matrix.toBilin' (coefficientMatrix rows v))) := by
  rw [bilinear_covariance_of_rows rows columns parameterRows identity v, ← he]
  exact Covering.gram_rank_linearEquiv _ e

end Lemmata.CocubicCovering.CoveringCongruence
