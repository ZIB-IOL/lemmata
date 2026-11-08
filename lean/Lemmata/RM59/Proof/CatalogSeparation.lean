module

public import Lemmata.RM59.Proof.CatalogGeometry
public import Lemmata.RM59.Proof.CatalogAdditions
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace Lemmata.RM59.CatalogSeparation

open scoped Matrix
open Packed CatalogForms CatalogGeometry CatalogUniform

def keyLE (a b : List Nat) : Bool := compare a b != .gt

theorem keyLE_eq (a b : List Nat) : keyLE a b = (compare a b).isLE := by
  unfold keyLE
  cases compare a b <;> rfl

theorem keyLE_trans (a b c : List Nat) : keyLE a b → keyLE b c → keyLE a c := by
  simp only [keyLE_eq]
  exact Std.TransOrd.isLE_trans

theorem keyLE_total (a b : List Nat) : keyLE a b || keyLE b a := by
  rw [keyLE_eq, keyLE_eq]
  have h : compare b a = (compare a b).swap := Std.OrientedCmp.eq_swap
  rw [h]
  cases compare a b <;> decide

theorem keyLE_antisymm (a b : List Nat) (hab : keyLE a b) (hba : keyLE b a) : a = b := by
  rw [keyLE_eq] at hab hba
  exact Std.LawfulEqOrd.eq_of_compare (Std.OrientedCmp.isLE_antisymm hab hba)

theorem sort_eq_of_perm {a b : List (List Nat)} (hp : a.Perm b) :
    a.mergeSort keyLE = b.mergeSort keyLE := by
  apply List.Perm.eq_of_pairwise
    (fun x y _ _ => keyLE_antisymm x y)
    (List.pairwise_mergeSort keyLE_trans keyLE_total a)
    (List.pairwise_mergeSort keyLE_trans keyLE_total b)
  exact (List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm)

def packedKeys (T : CubicForm) : List (List Nat) :=
  List.ofFn (fun v : PackedPoint => actualKey T (decodePoint v))

def formInvariant (T : CubicForm) : List (List Nat) := (packedKeys T).mergeSort keyLE

theorem formInvariant_action (g : CoordinateGroup 9) (T : CubicForm) :
    formInvariant (g • T) = formInvariant T := by
  let p : Equiv.Perm PackedPoint := pointEquiv.trans (g.toEquiv.trans pointEquiv.symm)
  have hp (w : PackedPoint) : decodePoint (p w) = g (decodePoint w) := by
    change pointEquiv (p w) = g (pointEquiv w)
    simp [p]
  have hcomp : (fun w : PackedPoint => actualKey (g • T) (decodePoint w)) ∘ p =
      (fun w : PackedPoint => actualKey T (decodePoint w)) := by
    funext w
    simp only [Function.comp_apply, hp, actualKey_action]
  have hperm := p.ofFn_comp_perm (fun w : PackedPoint => actualKey (g • T) (decodePoint w))
  rw [hcomp] at hperm
  exact sort_eq_of_perm hperm.symm

theorem geometry_vertexKeys_size (family : Fin 348) :
    (CatalogUniform.geometry (family.val + 1)).vertexKeys.size = 512 := by
  simp only [CatalogUniform.geometry, Array.size_ofFn]

theorem geometry_vertexKeys (family : Fin 348) :
    (CatalogUniform.geometry (family.val + 1)).vertexKeys =
      Array.ofFn (fun v : PackedPoint => actualKey (representative family) (decodePoint v)) := by
  apply Array.ext
  · simp only [geometry_vertexKeys_size, Array.size_ofFn]
  · intro i hi hj
    have hi' : i < 512 := by simpa only [Array.size_ofFn] using hj
    have h := geometry_vertexKey_semantic family ⟨i, hi'⟩
    rw [Array.getElem?_eq_some_getElem _ _ hi, Option.getD_some] at h
    rw [Array.getElem_ofFn]
    exact h

theorem geometry_invariant_semantic (family : Fin 348) :
    (CatalogUniform.geometry (family.val + 1)).vertexKeys.toList.mergeSort
      (fun a b => compare a b != .gt) = formInvariant (representative family) := by
  rw [geometry_vertexKeys, Array.toList_ofFn]
  rfl

theorem geometry_key_invariant (family : Fin 348) (P : CoordinateGroup 9 → Prop)
    (hP : ∀ g, P g → g ∈ MulAction.stabilizer (CoordinateGroup 9) (representative family)) :
    ∀ g, P g → ∀ v,
      readKey (CatalogUniform.geometry (family.val + 1)).vertexKeys (g v) =
        readKey (CatalogUniform.geometry (family.val + 1)).vertexKeys v := by
  intro g hg v
  unfold readKey
  rw [geometry_vertexKey_semantic family (encodePoint (g v)),
    geometry_vertexKey_semantic family (encodePoint v),
    decodePoint_encodePoint, decodePoint_encodePoint]
  exact actualKey_stabilizer g (representative family) (hP g hg) v

theorem geometry_colors_invariant (family : Fin 348) (P : CoordinateGroup 9 → Prop)
    (hP : ∀ g, P g → g ∈ MulAction.stabilizer (CoordinateGroup 9) (representative family)) :
    ColorRefinement.Invariant P
      (readColor (exactColors (CatalogUniform.geometry (family.val + 1)).vertexKeys)) :=
  exactColors_invariant P _ (geometry_vertexKeys_size family) (geometry_key_invariant family P hP)

theorem supportForm_ne_zero (P : Finset (Point 9)) (hP : SupportForms.LowerZero P)
    (hmoment : ∃ s, s.card = 3 ∧ supportMoment P s = 1) :
    SupportForms.alternatingSupportForm P hP ≠ 0 := by
  obtain ⟨s, hcard, hvalue⟩ := hmoment
  obtain ⟨i, j, k, _, _, _, rfl⟩ := Finset.card_eq_three.mp hcard
  intro hz
  have h := congrArg (fun T : CubicForm =>
    T (fun r : Fin 3 => Pi.single (![i, j, k] r) (1 : Field))) hz
  change SupportForms.supportForm P (fun r : Fin 3 => Pi.single (![i, j, k] r) (1 : Field)) = 0 at h
  rw [SupportForms.supportForm_basis] at h
  have hm : supportMoment P {i, j, k} = 0 := by simpa using h
  exact zero_ne_one (hm.symm.trans hvalue)

theorem representative_ne_zero (family : Fin 348) : representative family ≠ 0 := by
  rw [representative]
  exact supportForm_ne_zero _ _ (Certificate.seed_support_properties family).2.2.2

end Lemmata.RM59.CatalogSeparation
