module

public import Lemmata.CocubicCovering.Proof.LevelSix
public meta import Lemmata.CocubicCovering.Proof.LevelSix
public import Lemmata.CocubicCovering.Proof.Bits
public meta import Lemmata.CocubicCovering.Proof.Bits

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringMatrixReduction

open scoped BigOperators
open CoveringAffine CoveringBits CoveringPolynomial CoveringCongruence

def combinationRow {d c : ℕ} (directions : Fin c → Fin d → ℕ)
    (coefficients : Fin c → ℕ) (i j : Fin d) : ℕ :=
  xorRows ((List.finRange c).map fun k => if (directions k i).testBit j.val then coefficients k else 0)

def affineRow {d y w : ℕ} (base : Fin d → ℕ)
    (cross : Fin y → Fin d → ℕ) (outside : Fin w → Fin d → ℕ)
    (crossCoefficients : Fin y → ℕ) (outsideCoefficients : Fin w → ℕ) (i j : Fin d) : ℕ :=
  (if (base i).testBit j.val then 2 ^ 126 else 0) ^^^
    combinationRow cross crossCoefficients i j ^^^ combinationRow outside outsideCoefficients i j

theorem evalRow_combination {d c : ℕ} (directions : Fin c → Fin d → ℕ)
    (coefficients : Fin c → ℕ) (i j : Fin d) (v : Vector 127) :
    evalRow (combinationRow directions coefficients i j) v =
      ∑ k, ofBool ((directions k i).testBit j.val) * evalRow (coefficients k) v := by
  rw [combinationRow, evalRow_xorRows, List.map_map,
    ← List.sum_toFinset _ (List.nodup_finRange c), List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro k hk
  cases hbit : (directions k i).testBit j.val <;> simp [hbit]

theorem evalRow_affine {d y w : ℕ} (base : Fin d → ℕ)
    (cross : Fin y → Fin d → ℕ) (outside : Fin w → Fin d → ℕ)
    (crossCoefficients : Fin y → ℕ) (outsideCoefficients : Fin w → ℕ)
    (i j : Fin d) (v : Vector 127) (hpoint : v (Fin.last 126) = 1) :
    evalRow (affineRow base cross outside crossCoefficients outsideCoefficients i j) v =
      ofBool ((base i).testBit j.val) +
        (∑ k, ofBool ((cross k i).testBit j.val) * evalRow (crossCoefficients k) v) +
        ∑ k, ofBool ((outside k i).testBit j.val) * evalRow (outsideCoefficients k) v := by
  unfold affineRow
  rw [evalRow_xor, evalRow_xor, evalRow_combination, evalRow_combination]
  have hp : evalRow (2 ^ 126) v = 1 :=
    (CoveringEncoding.evalRow_two_pow (Fin.last 126) v).trans hpoint
  cases hbit : (base i).testBit j.val
  · change evalRow 0 v + _ + _ = 0 + _ + _
    rw [evalRow_zero]
  · change evalRow (2 ^ 126) v + _ + _ = 1 + _ + _
    rw [hp]

theorem matrix_reconstruction {d y w c : ℕ} (rows : Fin d → Fin d → ℕ)
    (base : Fin d → ℕ) (cross : Fin y → Fin d → ℕ) (outside : Fin w → Fin d → ℕ)
    (crossCoefficients : Fin y → ℕ) (outsideCoefficients : Fin w → ℕ)
    (constraints : Fin c → ℕ) (witnesses : Fin d → Fin d → ℕ)
    (checked : ∀ i j, rows i j =
      affineRow base cross outside crossCoefficients outsideCoefficients i j ^^^
        composeRow (witnesses i j) constraints)
    (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hconstraints : ∀ k, evalRow (constraints k) v = 0) (i j : Fin d) :
    coefficientMatrix rows v i j = ofBool ((base i).testBit j.val) +
      (∑ k, ofBool ((cross k i).testBit j.val) * evalRow (crossCoefficients k) v) +
      ∑ k, ofBool ((outside k i).testBit j.val) * evalRow (outsideCoefficients k) v := by
  have hz : rowMap constraints v = 0 := by
    funext k
    exact hconstraints k
  change evalRow (rows i j) v = _
  rw [checked, evalRow_xor, evalRow_composeRow, hz]
  have hzero : evalRow (witnesses i j) (0 : Vector c) = 0 := by simp [evalRow]
  rw [hzero, add_zero]
  exact evalRow_affine base cross outside crossCoefficients outsideCoefficients i j v hpoint

theorem evalRow_local_assignment (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (assignment : ℕ) (i : Fin 15)
    (hlocal : v ⟨111 + i.val, by omega⟩ = ofBool (assignment.testBit i.val)) :
    evalRow ((2 ^ (111 + i.val)) ^^^
      (if assignment.testBit i.val then 2 ^ 126 else 0)) v = 0 := by
  rw [evalRow_xor, CoveringEncoding.evalRow_two_pow ⟨111 + i.val, by omega⟩ v, hlocal]
  have hp : evalRow (2 ^ 126) v = 1 :=
    (CoveringEncoding.evalRow_two_pow (Fin.last 126) v).trans hpoint
  cases hbit : assignment.testBit i.val
  · change 0 + evalRow 0 v = 0
    rw [evalRow_zero, add_zero]
  · change 1 + evalRow (2 ^ 126) v = 0
    rw [hp]
    exact CharTwo.add_self_eq_zero 1

theorem evalRow_kernel_pairing {d : ℕ} (rows : Fin d → Fin d → ℕ)
    (v : Vector 127) (mask : ℕ) (column : Fin d) :
    evalRow (composeRow mask (fun i : Fin d => rows i column)) v =
      Matrix.toBilin' (coefficientMatrix rows v) (decodeMask mask) (Pi.single column 1) := by
  rw [evalRow_composeRow, Matrix.toBilin'_apply', Matrix.mulVec_single_one]
  change (∑ i : Fin d, if mask.testBit i.val then evalRow (rows i column) v else 0) =
    ∑ i : Fin d, ofBool (mask.testBit i.val) * evalRow (rows i column) v
  apply Finset.sum_congr rfl
  intro i hi
  cases hbit : mask.testBit i.val <;> simp [hbit]

theorem evalRow_kernel_eq_zero {d : ℕ} (rows : Fin d → Fin d → ℕ)
    (v : Vector 127) (mask : ℕ)
    (hkernel : Matrix.toBilin' (coefficientMatrix rows v) (decodeMask mask) = 0)
    (column : Fin d) : evalRow (composeRow mask (fun i : Fin d => rows i column)) v = 0 := by
  rw [evalRow_kernel_pairing]
  exact LinearMap.congr_fun hkernel (Pi.single column 1)

end Lemmata.CocubicCovering.CoveringMatrixReduction
