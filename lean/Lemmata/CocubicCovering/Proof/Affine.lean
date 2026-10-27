module

public import Lemmata.CocubicCovering.Def.Field
public meta import Lemmata.CocubicCovering.Def.Field
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringAffine

open scoped BigOperators

def evalRow {n : ℕ} (row : ℕ) (v : Vector n) : Field :=
  ∑ i, if row.testBit i.val then v i else 0

@[simp] theorem evalRow_zero {n : ℕ} (v : Vector n) : evalRow 0 v = 0 := by
  simp [evalRow]

theorem evalRow_xor {n : ℕ} (a b : ℕ) (v : Vector n) :
    evalRow (a ^^^ b) v = evalRow a v + evalRow b v := by
  rw [evalRow, evalRow, evalRow, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.testBit_xor]
  cases a.testBit i.val <;> cases b.testBit i.val <;>
    simp [CharTwo.add_self_eq_zero]

theorem evalRow_add {n : ℕ} (row : ℕ) (v w : Vector n) :
    evalRow row (v + w) = evalRow row v + evalRow row w := by
  rw [evalRow, evalRow, evalRow, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases row.testBit i.val <;> simp

theorem evalRow_smul {n : ℕ} (row : ℕ) (a : Field) (v : Vector n) :
    evalRow row (a • v) = a • evalRow row v := by
  simp only [evalRow, Pi.smul_apply, Finset.smul_sum, smul_ite, smul_zero]

def rowMap {m n : ℕ} (rows : Fin m → ℕ) : Vector n →ₗ[Field] Vector m where
  toFun v i := evalRow (rows i) v
  map_add' v w := by funext i; exact evalRow_add (rows i) v w
  map_smul' a v := by funext i; exact evalRow_smul (rows i) a v

def xorRows : List ℕ → ℕ
  | [] => 0
  | row :: rest => row ^^^ xorRows rest

theorem evalRow_xorRows {n : ℕ} (rows : List ℕ) (v : Vector n) :
    evalRow (xorRows rows) v = (rows.map fun row => evalRow row v).sum := by
  induction rows with
  | nil => simp [xorRows]
  | cons row rest ih => simp [xorRows, evalRow_xor, ih]

def composeRow {m : ℕ} (row : ℕ) (rows : Fin m → ℕ) : ℕ :=
  xorRows ((List.finRange m).map fun i => if row.testBit i.val then rows i else 0)

theorem evalRow_composeRow {m n : ℕ} (row : ℕ) (rows : Fin m → ℕ) (v : Vector n) :
    evalRow (composeRow row rows) v = evalRow row (rowMap rows v) := by
  rw [composeRow, evalRow_xorRows, List.map_map,
    ← List.sum_toFinset _ (List.nodup_finRange m), List.toFinset_finRange]
  change (∑ i : Fin m, evalRow (if row.testBit i.val then rows i else 0) v) =
    ∑ i : Fin m, if row.testBit i.val then evalRow (rows i) v else 0
  apply Finset.sum_congr rfl
  intro i hi
  cases row.testBit i.val <;> simp

theorem rowMap_inverse_on_basis {n : ℕ} (rows inverse : Fin n → ℕ)
    (h : ∀ i : Fin n,
      rowMap inverse (rowMap rows (Pi.single i 1)) = Pi.single i 1) :
    (rowMap inverse).comp (rowMap rows) = (LinearMap.id : Vector n →ₗ[Field] Vector n) := by
  apply (Pi.basisFun Field (Fin n)).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.id_apply] using h i

def equivOfRows {n : ℕ} (rows inverse : Fin n → ℕ)
    (hl : ∀ i : Fin n,
      rowMap inverse (rowMap rows (Pi.single i 1)) = Pi.single i 1)
    (hr : ∀ i : Fin n,
      rowMap rows (rowMap inverse (Pi.single i 1)) = Pi.single i 1) :
    Vector n ≃ₗ[Field] Vector n where
  toLinearMap := rowMap rows
  invFun := rowMap inverse
  left_inv v := LinearMap.congr_fun (rowMap_inverse_on_basis rows inverse hl) v
  right_inv v := LinearMap.congr_fun (rowMap_inverse_on_basis inverse rows hr) v

end Lemmata.CocubicCovering.CoveringAffine
