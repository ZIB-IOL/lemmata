module

public import Lemmata.CocubicCovering.Proof.PackedAction
public meta import Lemmata.CocubicCovering.Proof.PackedAction
public import Lemmata.CocubicCovering.Proof.Congruence
public meta import Lemmata.CocubicCovering.Proof.Congruence

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringPackedPair

open CoveringAffine CoveringBits CoveringPackedAction CoveringPolynomial
open scoped BigOperators

theorem ofBool_foldr_xor {ι : Type*} (values : List ι) (bits : ι → Bool) :
    ofBool (values.foldr (fun i bit => Bool.xor (bits i) bit) false) =
      (values.map (fun i => ofBool (bits i))).sum := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.foldr_cons, ofBool_xor, List.map_cons, List.sum_cons, ih]

def bitMatrix {d : ℕ} (rows : Fin d → ℕ) : Matrix (Fin d) (Fin d) Field :=
  fun i j => ofBool ((rows i).testBit j.val)

def pairBit {d : ℕ} (rows : Fin d → ℕ) (left right : ℕ) : Bool :=
  (composeRow right (fun j : Fin d =>
    if (composeRow left rows).testBit j.val then 1 else 0)).testBit 0

theorem ofBool_composeRow_testBit {m : ℕ} (mask : ℕ) (columns : Fin m → ℕ) (bit : ℕ) :
    ofBool ((composeRow mask columns).testBit bit) =
      ∑ i, if mask.testBit i.val then ofBool ((columns i).testBit bit) else 0 := by
  have h := congrFun (decodeMask_composeRow (n := bit + 1) mask columns) ⟨bit, by omega⟩
  simpa only [decodeMask, Finset.sum_apply, Pi.zero_apply, ite_apply] using h

theorem ofBool_pairBit {d : ℕ} (rows : Fin d → ℕ) (left right : ℕ) :
    ofBool (pairBit rows left right) =
      Matrix.toBilin' (bitMatrix rows) (decodeMask left) (decodeMask right) := by
  unfold pairBit
  rw [ofBool_composeRow_testBit]
  have hrow : ∀ j : Fin d,
      ofBool ((if (composeRow left rows).testBit j.val then 1 else 0 : ℕ).testBit 0) =
        ∑ i : Fin d, if left.testBit i.val then ofBool ((rows i).testBit j.val) else 0 := by
    intro j
    rw [← ofBool_composeRow_testBit]
    cases hbit : (composeRow left rows).testBit j.val <;> simp [hbit]
  simp_rw [hrow]
  rw [Matrix.toBilin'_apply]
  have hsum : (∑ j : Fin d, if right.testBit j.val then
      ∑ i : Fin d, if left.testBit i.val then ofBool ((rows i).testBit j.val) else 0 else 0) =
      ∑ i : Fin d, ∑ j : Fin d,
        if left.testBit i.val then
          if right.testBit j.val then ofBool ((rows i).testBit j.val) else 0 else 0 := by
    have hsplit : ∀ j : Fin d,
        (if right.testBit j.val then
          ∑ i : Fin d, if left.testBit i.val then ofBool ((rows i).testBit j.val) else 0 else 0) =
        ∑ i : Fin d, if right.testBit j.val then
          (if left.testBit i.val then ofBool ((rows i).testBit j.val) else 0) else 0 := by
      intro j
      cases right.testBit j.val <;> simp
    simp_rw [hsplit]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    cases left.testBit i.val <;> cases right.testBit j.val <;> rfl
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  cases hl : left.testBit i.val <;> cases hr : right.testBit j.val <;>
    simp [decodeMask, bitMatrix, hl, hr]

end Lemmata.CocubicCovering.CoveringPackedPair
