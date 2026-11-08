module

public import Lemmata.RM59.Proof.CatalogContractions
public import Init.Data.List.Count

@[expose] public section

namespace Lemmata.RM59.PackedParity

open scoped BigOperators
open Packed CatalogForms CatalogContractions

def parity9 (value : Nat) : Bool :=
  ((List.range 9).countP fun i => value.testBit i) % 2 == 1

theorem bitField_and (a b : Bool) :
    bitField (a && b) = bitField a * bitField b := by
  cases a <;> cases b <;> decide

theorem small_cast_parity : ∀ value : Fin 10,
    bitField (value.val % 2 == 1) = (value.val : Field) := by
  decide

theorem countP_cast {α : Type*} (vertices : List α) (predicate : α → Bool) :
    (vertices.countP predicate : Field) =
      (vertices.map fun w => bitField (predicate w)).sum := by
  induction vertices with
  | nil => simp
  | cons w vertices ih =>
    cases h : predicate w <;>
      simp [List.countP_cons, h, ih, bitField, add_comm]

theorem parity_cast (value : Nat) :
    bitField (parity9 value) =
      ((List.range 9).countP (fun i => value.testBit i) : Field) := by
  have hle := List.countP_le_length (p := fun i => value.testBit i) (l := List.range 9)
  have hlt : (List.range 9).countP (fun i => value.testBit i) < 10 := by
    simpa only [List.length_range] using Nat.lt_succ_of_le hle
  exact small_cast_parity ⟨_, hlt⟩

theorem parity_land (a b : Nat) :
    bitField (parity9 (Nat.land a b)) = SupportForms.evaluation (natRow a) (natRow b) := by
  rw [parity_cast, countP_cast, range_sum_eq]
  change (∑ i : Fin 9, bitField ((Nat.land a b).testBit i.val)) =
    ∑ i : Fin 9, natRow b i * natRow a i
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.land_eq, Nat.testBit_and, bitField_and, natRow, mul_comm]

theorem parity_pairValue (T : CubicForm) (basis : Array (Array Nat))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j)) (x y z : PackedPoint) :
    bitField (parity9 (Nat.land (pairValue basis x y) z.val)) =
      cubicFormValue T (decodePoint x) (decodePoint y) (decodePoint z) := by
  rw [parity_land, natRow_packed, pairValue_semantic T basis hbasis,
    ← value_as_evaluation]

theorem parity_pairValue_eq_true_iff (T : CubicForm) (basis : Array (Array Nat))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j)) (x y z : PackedPoint) :
    parity9 (Nat.land (pairValue basis x y) z.val) = true ↔
      cubicFormValue T (decodePoint x) (decodePoint y) (decodePoint z) = 1 := by
  constructor
  · intro hp
    have h := parity_pairValue T basis hbasis x y z
    rw [hp, bitField_true] at h
    exact h.symm
  · intro ht
    apply bitField_injective
    rw [bitField_true, parity_pairValue T basis hbasis, ht]

theorem family_parity_pairValue (family : Fin 348) (x y z : PackedPoint) :
    bitField (parity9 (Nat.land (pairValue (familyBasis family) x y) z.val)) =
      cubicFormValue (representative family) (decodePoint x) (decodePoint y) (decodePoint z) :=
  parity_pairValue _ _ (family_basis_semantic family) x y z

end Lemmata.RM59.PackedParity
