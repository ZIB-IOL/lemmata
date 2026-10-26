module

public import Lemmata.CocubicCovering.Proof.Bits
public meta import Lemmata.CocubicCovering.Proof.Bits
public import Lemmata.CocubicCovering.Proof.Affine
public meta import Lemmata.CocubicCovering.Proof.Affine
public import Lemmata.CocubicCovering.Proof.Witness
public meta import Lemmata.CocubicCovering.Proof.Witness

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringPackedAction

open CoveringBits CoveringAffine CoveringWitness
open scoped BigOperators

theorem decodeMask_xorRows {n : ℕ} (rows : List ℕ) :
    decodeMask (xorRows rows) = (rows.map fun row => (decodeMask row : Vector n)).sum := by
  induction rows with
  | nil => simp [xorRows]
  | cons row rest ih => simp [xorRows, decodeMask_xor, ih]

theorem decodeMask_composeRow {m n : ℕ} (mask : ℕ) (columns : Fin m → ℕ) :
    (decodeMask (composeRow mask columns) : Vector n) =
      ∑ i, if mask.testBit i.val then decodeMask (columns i) else 0 := by
  rw [composeRow, decodeMask_xorRows, List.map_map,
    ← List.sum_toFinset _ (List.nodup_finRange m), List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro i hi
  cases hbit : mask.testBit i.val <;> simp [hbit]

theorem decodeMask_composeRow_familyLinear {m n : ℕ}
    (mask : ℕ) (columns : Fin m → ℕ) :
    (decodeMask (composeRow mask columns) : Vector n) =
      familyLinear (fun i : Fin m => (decodeMask (columns i) : Vector n))
        (decodeMask mask) := by
  rw [decodeMask_composeRow, familyLinear_apply]
  apply Finset.sum_congr rfl
  intro i hi
  cases hbit : mask.testBit i.val <;> simp [decodeMask, hbit]

/-- The packed column action agrees with its transposed packed rows on every input. -/
theorem rowMap_decodeMask {m n : ℕ} (rows : Fin n → ℕ) (columns : Fin m → ℕ)
    (htranspose : ∀ i j, (rows i).testBit j.val = (columns j).testBit i.val)
    (mask : ℕ) :
    rowMap rows (decodeMask mask : Vector m) =
      (decodeMask (composeRow mask columns) : Vector n) := by
  rw [decodeMask_composeRow]
  funext i
  change (∑ j, if (rows i).testBit j.val then decodeMask mask j else 0) =
    (∑ j, if mask.testBit j.val then (decodeMask (columns j) : Vector n) else 0) i
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [htranspose i j]
  cases hm : mask.testBit j.val <;> cases hc : (columns j).testBit i.val <;>
    simp [decodeMask, hm, hc]

end Lemmata.CocubicCovering.CoveringPackedAction
