module

public import Lemmata.RM59.Proof.CatalogColors
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open Packed

theorem range_map_eq_finRange {α : Type*} (n : Nat) (f : Nat → α) :
    (List.range n).map f = (List.finRange n).map (fun i => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem sorted_map_equiv {n : Nat} (e : Equiv.Perm (Fin n)) (f : Fin n → Nat) :
    (((List.finRange n).map (f ∘ e)).mergeSort (· ≤ ·)) =
      (((List.finRange n).map f).mergeSort (· ≤ ·)) := by
  have hp : ((List.finRange n).map (f ∘ e)).Perm ((List.finRange n).map f) := by
    simpa only [List.map_map] using (e.map_finRange_perm.map f)
  apply List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' (· ≤ ·) _)
    (List.pairwise_mergeSort' (· ≤ ·) _)
  exact (List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm)

def additionTerms (color : Array Nat) (v : Point 9) (w : PackedPoint) : Nat :=
  ColorRefinement.pairCode (readColor color (decodePoint w))
    (readColor color (decodePoint w + v))

theorem additionTerms_equiv (color : Array Nat) (e : CoordinateGroup 9)
    (hc : ∀ v, readColor color (e v) = readColor color v) (v : Point 9) :
    (((List.finRange 512).map (additionTerms color (e v))).mergeSort (· ≤ ·)) =
      (((List.finRange 512).map (additionTerms color v)).mergeSort (· ≤ ·)) := by
  let p : Equiv.Perm PackedPoint := pointEquiv.trans (e.toEquiv.trans pointEquiv.symm)
  have hp (w : PackedPoint) : decodePoint (p w) = e (decodePoint w) := by
    change pointEquiv (p w) = e (pointEquiv w)
    simp [p]
  have hcomp : additionTerms color (e v) ∘ p = additionTerms color v := by
    funext w
    simp only [Function.comp_apply, additionTerms, hp, ← e.map_add, hc]
  have h := sorted_map_equiv p (additionTerms color (e v))
  rw [hcomp] at h
  exact h.symm

theorem additionColors_invariant (g : Geometry) (P : CoordinateGroup 9 → Prop)
    (color : Array Nat) (hc : ColorRefinement.Invariant P (readColor color)) :
    ColorRefinement.Invariant P (readColor (additionColors g color)) := by
  apply exactColors_invariant P _ (by simp [Geometry.count])
  intro e he v
  have hkey (x : Point 9) :
      readKey (Array.ofFn fun w : Fin g.count =>
        color[w.val]?.getD 0 :: ((List.range g.count).map fun a =>
          min (color[a]?.getD 0) (color[Nat.xor a w.val]?.getD 0) * 1024 +
            max (color[a]?.getD 0) (color[Nat.xor a w.val]?.getD 0)).mergeSort (· ≤ ·)) x =
      readColor color x :: ((List.finRange 512).map (additionTerms color x)).mergeSort (· ≤ ·) := by
    simp only [readKey, Array.getElem?_ofFn, Geometry.count,
      dif_pos (encodePoint x).isLt, Option.getD_some]
    apply congrArg (List.cons (readColor color x))
    apply congrArg (fun terms : List Nat => terms.mergeSort (· ≤ ·))
    rw [range_map_eq_finRange]
    apply List.map_congr_left
    intro w hw
    have hshift := readColor_shift color (decodePoint w) (encodePoint x).val (encodePoint x).isLt
    simp only [encodePoint_decodePoint, readPoint_encodePoint] at hshift
    simp only [additionTerms, ColorRefinement.pairCode, readColor_decodePoint, hshift]
  rw [hkey, hkey, hc e he v, additionTerms_equiv color e (hc e he) v]

end Lemmata.RM59.CatalogUniform
