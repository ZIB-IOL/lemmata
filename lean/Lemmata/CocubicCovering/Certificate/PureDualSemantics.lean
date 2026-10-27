module

public import Lemmata.CocubicCovering.Certificate.PureDual
public meta import Lemmata.CocubicCovering.Certificate.PureDual
public import Lemmata.CocubicCovering.Proof.PackedWitness
public meta import Lemmata.CocubicCovering.Proof.PackedWitness

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Certificate.PureDual

open CoveringPolynomial CoveringAffine CoveringBits
open scoped BigOperators

theorem ofBool_parity (n mask : Nat) :
    ofBool (parity n mask) = ∑ i : Fin n, ofBool (mask.testBit i.val) := by
  induction n with
  | zero => simp [parity]
  | succ n ih =>
      rw [parity, ofBool_xor, ih, Fin.sum_univ_castSucc]
      rfl

theorem ofBool_pairing (n a b : Nat) :
    ofBool (parity n (a &&& b)) = evalRow a (decodeMask b : Vector n) := by
  rw [ofBool_parity, evalRow]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.testBit_and, ofBool_and]
  cases a.testBit i.val <;> simp [decodeMask]

theorem ofBool_injective : Function.Injective ofBool := by
  intro a b h
  simpa only [toBool_ofBool] using congrArg toBool h

theorem ofBool_diagonal {k : Nat} (i j : Fin k) :
    ofBool (decide (i = j)) = (Pi.single i (1 : Field) : Fin k → Field) j := by
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Pi.single_apply, Ne.symm h]

theorem checkDual_eq (n : Nat) {k : Nat} (columns rows : Fin k → Nat) :
    checkDual n columns rows = CoveringPackedWitness.checkDual n columns rows := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkDual, CoveringPackedWitness.checkDual, decide_eq_true_eq]
  constructor
  · intro h i
    funext j
    change evalRow (rows j) (decodeMask (columns i) : Vector n) =
      (Pi.single i (1 : Field) : Fin k → Field) j
    simpa only [ofBool_pairing, ofBool_diagonal] using congrArg ofBool (h i j)
  · intro h i j
    apply ofBool_injective
    rw [ofBool_pairing, ofBool_diagonal]
    exact congrFun (h i) j

theorem listCheckDual_eq (n : Nat) (columns rows : List Nat) :
    listCheckDual n columns rows = CoveringPackedWitness.listCheckDual n columns rows := by
  exact checkDual_eq n columns.get fun i => rows[i.val]?.getD 0

theorem appendColumns_eq {c d : Nat} (core : Fin c → Nat) (fresh : Fin d → Nat) :
    appendColumns core fresh = CoveringPackedWitness.appendColumns core fresh := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [appendColumns, CoveringPackedWitness.appendColumns]
  · intro j
    simp [appendColumns, CoveringPackedWitness.appendColumns]

theorem listCheckCombinedDual_eq (n : Nat) (core fresh rows : List Nat) :
    listCheckCombinedDual n core fresh rows =
      CoveringPackedWitness.listCheckCombinedDual n core fresh rows := by
  rw [listCheckCombinedDual, checkDual_eq, appendColumns_eq]
  rfl

end Lemmata.CocubicCovering.Certificate.PureDual
