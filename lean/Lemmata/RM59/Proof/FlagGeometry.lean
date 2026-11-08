module

public import Lemmata.RM59.Proof.FlagActions
public import Mathlib.FieldTheory.Finiteness
public meta import Lemmata.RM59.Proof.FlagActions
public meta import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace Lemmata.RM59.FlagGeometry

open Lemmata.RM59.Packed Lemmata.RM59.FlagActions
open scoped Matrix

def mask (i : Fin 3) : Nat := ![506, 338, 2] i

def dimension (i : Fin 3) : Nat := ![2, 5, 8] i

def masked (bits : Nat) : Point 9 →ₗ[Field] Point 9 where
  toFun x i := if bits.testBit i.val then x i else 0
  map_add' x y := by funext i; split_ifs <;> simp_all
  map_smul' r x := by funext i; split_ifs <;> simp_all

def space (i : Fin 3) : Submodule Field (Point 9) := LinearMap.ker (masked (mask i))

instance spaceMemDecidable (i : Fin 3) : DecidablePred (fun x : Point 9 => x ∈ space i) :=
  fun x => by change Decidable (masked (mask i) x = 0); infer_instance

theorem decoded_mem_checked : ∀ (i : Fin 3) (x : PackedPoint),
    decodePoint x ∈ space i ↔ Nat.land x.val (mask i) = 0 := by native_decide

theorem cardinality_checked : ∀ i : Fin 3, Fintype.card (space i) = 2 ^ dimension i := by
  native_decide

theorem space_finrank (i : Fin 3) : Module.finrank Field (space i) = dimension i := by
  have hc := Module.card_eq_pow_finrank (K := Field) (V := space i)
  have hField : Fintype.card Field = 2 := by decide
  rw [cardinality_checked, hField] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm

theorem generator_flags_checked : ∀ (g : Fin 12) (i : Fin 3) (x : PackedPoint),
    decodePoint (packed g x) ∈ space i ↔ decodePoint x ∈ space i := by native_decide

theorem generator_preserves (g : Fin 12) (i : Fin 3) (x : Point 9) :
    linear g x ∈ space i ↔ x ∈ space i := by
  have h := generator_flags_checked g i (encodePoint x)
  simpa only [linear, packed_eq_evalColumns, decodePoint_evalColumns, decodePoint_encodePoint] using h

theorem word_preserves (word : Word) (i : Fin 3) (x : Point 9) :
    wordLinear word x ∈ space i ↔ x ∈ space i := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    change linear g (wordLinear word x) ∈ space i ↔ x ∈ space i
    rw [generator_preserves, ih]

theorem inverse_preserves (word : Word) (i : Fin 3) (x : Point 9) :
    (wordEquiv word).symm x ∈ space i ↔ x ∈ space i := by
  have h := word_preserves word i ((wordEquiv word).symm x)
  change wordEquiv word ((wordEquiv word).symm x) ∈ space i ↔
    (wordEquiv word).symm x ∈ space i at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem hyperplane_mem_checked : ∀ x : PackedPoint,
    decodePoint x ∈ space 2 ↔ decodePoint x 1 = 0 := by native_decide

theorem hyperplane_mem (x : Point 9) : x ∈ space 2 ↔ x 1 = 0 := by
  simpa only [decodePoint_encodePoint] using hyperplane_mem_checked (encodePoint x)

end Lemmata.RM59.FlagGeometry
