module

public import Lemmata.RM59.Proof.Packed
public meta import Lemmata.RM59.Proof.Packed
public import Mathlib.Algebra.Module.Equiv.Basic
public meta import Lean.Elab.Tactic.Decide

@[expose] public section

namespace Lemmata.RM59.Packed

open scoped BigOperators

abbrev Columns := Fin 9 → PackedPoint

def xorPoint (x y : PackedPoint) : PackedPoint :=
  ⟨(Nat.xor x.val y.val) % 512, Nat.mod_lt _ (by decide)⟩

@[simp] theorem decodePoint_zero : decodePoint 0 = 0 := by native_decide

theorem decodePoint_xorPoint : ∀ x y : PackedPoint,
    decodePoint (xorPoint x y) = decodePoint x + decodePoint y := by
  native_decide

def columnMap (columns : Columns) : Point 9 →ₗ[Field] Point 9 where
  toFun x := ∑ i, x i • decodePoint (columns i)
  map_add' x y := by
    change (∑ i, (x i + y i) • decodePoint (columns i)) =
      (∑ i, x i • decodePoint (columns i)) + ∑ i, y i • decodePoint (columns i)
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (a * x i) • decodePoint (columns i)) =
      a • ∑ i, x i • decodePoint (columns i)
    simp only [Finset.smul_sum, mul_smul]

def evalColumns (columns : Columns) (x : PackedPoint) : PackedPoint :=
  (List.finRange 9).foldl (fun value i =>
    if x.val.testBit i.val then xorPoint value (columns i) else value) 0

private theorem decodePoint_foldl (columns : Columns) (x : PackedPoint)
    (indices : List (Fin 9)) (start : PackedPoint) :
    decodePoint (indices.foldl (fun value i =>
      if x.val.testBit i.val then xorPoint value (columns i) else value) start) =
      decodePoint start + (indices.map fun i =>
        if x.val.testBit i.val then decodePoint (columns i) else 0).sum := by
  induction indices generalizing start with
  | nil => simp
  | cons i indices ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    cases h : x.val.testBit i.val <;>
      simp [h, decodePoint_xorPoint, add_assoc]

theorem decodePoint_evalColumns (columns : Columns) (x : PackedPoint) :
    decodePoint (evalColumns columns x) = columnMap columns (decodePoint x) := by
  rw [evalColumns, decodePoint_foldl, decodePoint_zero, zero_add]
  change ((List.finRange 9).map fun i =>
    if x.val.testBit i.val then decodePoint (columns i) else 0).sum =
      ∑ i, decodePoint x i • decodePoint (columns i)
  rw [← List.sum_toFinset _ (List.nodup_finRange 9), List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : x.val.testBit i.val <;> simp [decodePoint, bitField, h]

@[simp] theorem evalColumns_zero (columns : Columns) : evalColumns columns 0 = 0 := by
  apply decodePoint_injective
  simp only [decodePoint_evalColumns, decodePoint_zero, map_zero]

abbrev KernelZero (columns : Columns) : Prop :=
  ∀ x : PackedPoint, evalColumns columns x = 0 → x = 0

theorem columnMap_injective_of_kernelZero (columns : Columns)
    (h : KernelZero columns) : Function.Injective (columnMap columns) := by
  intro x y hxy
  have hdiff : columnMap columns (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have heval : evalColumns columns (encodePoint (x - y)) = 0 := by
    apply decodePoint_injective
    rw [decodePoint_evalColumns, decodePoint_encodePoint, hdiff, decodePoint_zero]
  have hencode := h _ heval
  have hzero : x - y = 0 := by
    calc
      x - y = decodePoint (encodePoint (x - y)) := (decodePoint_encodePoint _).symm
      _ = decodePoint 0 := congrArg decodePoint hencode
      _ = 0 := decodePoint_zero
  exact sub_eq_zero.mp hzero

theorem columnMap_injective_of_evalColumns_injective (columns : Columns)
    (h : Function.Injective (evalColumns columns)) :
    Function.Injective (columnMap columns) := by
  apply columnMap_injective_of_kernelZero columns
  intro x hx
  apply h
  rw [hx, evalColumns_zero]

noncomputable def linearEquivOfKernelZero (columns : Columns) (h : KernelZero columns) :
    Point 9 ≃ₗ[Field] Point 9 :=
  LinearEquiv.ofBijective (columnMap columns)
    ⟨columnMap_injective_of_kernelZero columns h,
      Finite.surjective_of_injective (columnMap_injective_of_kernelZero columns h)⟩

@[simp] theorem linearEquivOfKernelZero_apply (columns : Columns) (h : KernelZero columns)
    (x : Point 9) : linearEquivOfKernelZero columns h x = columnMap columns x := rfl

theorem linearEquivOfKernelZero_decode (columns : Columns) (h : KernelZero columns)
    (x : PackedPoint) :
    linearEquivOfKernelZero columns h (decodePoint x) =
      decodePoint (evalColumns columns x) :=
  (decodePoint_evalColumns columns x).symm

end Lemmata.RM59.Packed
