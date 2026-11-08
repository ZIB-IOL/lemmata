module

public import Lemmata.RM59.Proof.CatalogCompute
public import Lemmata.RM59.Proof.SupportForms
public import Lemmata.RM59.Proof.PackedLinear
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.FinCases
public meta import Lemmata.RM59.Proof.CatalogCompute
public meta import Lemmata.RM59.Proof.Packed

@[expose] public section

namespace Lemmata.RM59.CatalogForms

open scoped BigOperators Matrix
open Packed Certificate SupportForms CatalogCompute

def representative (family : Fin 348) : CubicForm :=
  alternatingSupportForm (decodeWord (seed (family.val + 1)))
    (seed_support_properties family).2.2.1

def natRow (value : Nat) : Point 9 := fun i => bitField (value.testBit i.val)

@[simp] theorem natRow_zero : natRow 0 = 0 := by
  funext i
  simp [natRow]

theorem natRow_xor (a b : Nat) : natRow (a ^^^ b) = natRow a + natRow b := by
  funext i
  simp only [natRow, Nat.testBit_xor, Pi.add_apply, bitField_xor]

@[simp] theorem natRow_packed (value : PackedPoint) : natRow value.val = decodePoint value := rfl

theorem natRow_injective_on_packed (a b : PackedPoint)
    (h : natRow a.val = natRow b.val) : a = b := decodePoint_injective h

def basisDataCheck (family : Nat) : Bool :=
  let rows := coordinateContractions (coefficients family)
  rows.size == 9 &&
    rows.all (fun row => row.size == 9 && row.all (· < 512)) &&
    (List.finRange 9).all (fun i => (List.finRange 9).all (fun j =>
      (List.finRange 9).all (fun k =>
        ((rows[i.val]?.getD #[])[j.val]?.getD 0).testBit k.val ==
          packedMoment (seed family) (encodeMask {i, j, k}).val)))

theorem basis_data_checked : ∀ family : Fin 348, basisDataCheck (family.val + 1) = true := by
  native_decide

theorem basis_bit_eq_moment (family : Fin 348) (i j k : Fin 9) :
    (((coordinateContractions (coefficients (family.val + 1)))[i.val]?.getD #[])[j.val]?.getD 0).testBit k.val =
        packedMoment (seed (family.val + 1)) (encodeMask {i, j, k}).val := by
  have h := basis_data_checked family
  unfold basisDataCheck at h
  have hall := (Bool.and_eq_true_iff.mp h).2
  have hi := List.all_eq_true.mp hall i (by simp)
  have hj := List.all_eq_true.mp hi j (by simp)
  have hk := List.all_eq_true.mp hj k (by simp)
  simpa using hk

theorem representative_basis (family : Fin 348) (i j k : Fin 9) :
    representative family ![Pi.single i 1, Pi.single j 1, Pi.single k 1] =
      natRow (((coordinateContractions (coefficients (family.val + 1)))[i.val]?.getD #[])[j.val]?.getD 0) k := by
  rw [representative, alternatingSupportForm_apply]
  have hv : (fun r : Fin 3 => Pi.single (![i, j, k] r) (1 : Field)) =
      ![Pi.single i 1, Pi.single j 1, Pi.single k 1] := by
    funext r
    fin_cases r <;> rfl
  rw [← hv, packed_supportForm_basis _ (supplied_families_checked family).2.1]
  simpa [natRow] using congrArg bitField (basis_bit_eq_moment family i j k).symm

theorem natRow_xor_fold (indices : List Nat) (values : Nat → Nat)
    (selected : Nat → Bool) (start : Nat) :
    natRow (indices.foldl (fun acc j => if selected j then Nat.xor acc (values j) else acc) start) =
      natRow start + (indices.map fun j => if selected j then natRow (values j) else 0).sum := by
  induction indices generalizing start with
  | nil => simp
  | cons j indices ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    cases h : selected j <;> simp [h, Nat.xor_eq, natRow_xor, add_assoc]

end Lemmata.RM59.CatalogForms
