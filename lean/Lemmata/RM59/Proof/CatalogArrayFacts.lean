module

public import Lemmata.RM59.Proof.CatalogColors
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open scoped BigOperators
open Packed

theorem array_eq_ofFn (color : Array Nat) (hsize : color.size = 512) :
    color = Array.ofFn (fun i : PackedPoint => color[i.val]?.getD 0) := by
  apply Array.ext
  · simpa using hsize
  · intro i hi hj
    rw [Array.getElem_ofFn, Array.getElem?_eq_some_getElem _ _ hi]
    rfl

private theorem count_fold (values : List Nat) (target start : Nat) :
    values.foldl (fun n c => n + if c = target then 1 else 0) start =
      start + (values.map fun c => if c = target then 1 else 0).sum := by
  induction values generalizing start with
  | nil => simp
  | cons c values ih => simp [List.foldl_cons, ih, Nat.add_assoc]

theorem classSize_eq_sum (color : Array Nat) (hsize : color.size = 512) (anchor : Nat) :
    classSize color anchor = ∑ i : PackedPoint,
      if color[i.val]?.getD 0 = color[anchor]?.getD 0 then 1 else 0 := by
  unfold classSize
  rw [← Array.foldl_toList, count_fold, zero_add]
  have hlist : color.toList = List.ofFn (fun i : PackedPoint => color[i.val]?.getD 0) := by
    simpa only [Array.toList_ofFn] using congrArg Array.toList (array_eq_ofFn color hsize)
  rw [hlist, List.map_ofFn, List.ofFn_eq_map,
    ← List.sum_toFinset _ (List.nodup_finRange 512), List.toFinset_finRange]
  rfl

theorem classSize_eq_card (color : Array Nat) (hsize : color.size = 512)
    (anchor : PackedPoint) :
    classSize color anchor.val =
      (ColorRefinement.colorClass (readColor color) (decodePoint anchor)).card := by
  rw [classSize_eq_sum color hsize]
  unfold ColorRefinement.colorClass
  rw [Finset.card_filter]
  apply Fintype.sum_equiv pointEquiv _ _
  intro w
  change (if color[w.val]?.getD 0 = color[anchor.val]?.getD 0 then 1 else 0) =
    if readColor color (decodePoint w) = readColor color (decodePoint anchor) then 1 else 0
  simp only [readColor_decodePoint]

theorem readColor_injective (color : Array Nat) (hsize : color.size = 512)
    (hnodup : color.toList.Nodup) : Function.Injective (readColor color) := by
  intro x y hxy
  have hx : (encodePoint x).val < color.size := by rw [hsize]; exact (encodePoint x).isLt
  have hy : (encodePoint y).val < color.size := by rw [hsize]; exact (encodePoint y).isLt
  have heq : color.toList[(encodePoint x).val] = color.toList[(encodePoint y).val] := by
    simpa only [readColor, Array.getElem?_eq_some_getElem _ _ hx,
      Array.getElem?_eq_some_getElem _ _ hy, Option.getD_some, Array.getElem_toList] using hxy
  have hi := hnodup.eq_of_getElem_eq (by simpa using hx) (by simpa using hy) heq
  exact pointEquiv.symm.injective (Fin.ext hi)

end Lemmata.RM59.CatalogUniform
