module

public import Lemmata.RM59.Proof.CatalogAdditions

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open Packed

theorem sorted_eq_of_perm (a b : List Nat) (h : a.Perm b) :
    a.mergeSort (· ≤ ·) = b.mergeSort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' (· ≤ ·) _)
    (List.pairwise_mergeSort' (· ≤ ·) _)
  exact (List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm)

theorem filter_map_transport (vertices : List PackedPoint) (e : Equiv.Perm PackedPoint)
    (p q : PackedPoint → Bool) (color : PackedPoint → Nat)
    (hp : ∀ w, p (e w) = q w) (hc : ∀ w, color (e w) = color w) :
    (((vertices.map e).filter p).map color) = ((vertices.filter q).map color) := by
  induction vertices with
  | nil => rfl
  | cons w vertices ih =>
    simp only [List.map_cons, List.filter_cons, hp]
    cases h : q w <;> simp [h, hc, ih]

theorem sorted_neighbors_equiv (adj : PackedPoint → PackedPoint → Bool)
    (color : PackedPoint → Nat) (e : Equiv.Perm PackedPoint)
    (ha : ∀ v w, adj (e v) (e w) = adj v w)
    (hc : ∀ w, color (e w) = color w) (v : PackedPoint) :
    ((((List.finRange 512).filter (adj (e v))).map color).mergeSort (· ≤ ·)) =
      ((((List.finRange 512).filter (adj v)).map color).mergeSort (· ≤ ·)) := by
  have hp := (e.map_finRange_perm.filter (adj (e v))).map color
  rw [filter_map_transport _ e (adj (e v)) (adj v) color (ha v) hc] at hp
  exact sorted_eq_of_perm _ _ hp.symm

theorem ordinaryColors_invariant (g : Geometry) (P : CoordinateGroup 9 → Prop)
    (adj : PackedPoint → PackedPoint → Bool)
    (hneighbors : g.neighbors = Array.ofFn fun v : PackedPoint =>
      (((List.finRange 512).filter (adj v)).map Fin.val))
    (anchors : List Nat) (color : Array Nat)
    (hbound : ∀ a ∈ anchors, a < 512)
    (hc : ColorRefinement.Invariant P (readColor color))
    (hadj : ∀ e, P e → ∀ v w, adj (encodePoint (e (decodePoint v)))
      (encodePoint (e (decodePoint w))) = adj v w)
    (ha : ∀ e, P e → ∀ a ∈ anchors, e (readPoint a) = readPoint a) :
    ColorRefinement.Invariant P (readColor (ordinaryColors g anchors color)) := by
  apply exactColors_invariant P _ (by simp [Geometry.count])
  intro e he v
  have hkey (x : Point 9) :
      readKey (Array.ofFn fun w : Fin g.count =>
        [color[w.val]?.getD 0] ++ anchors.map (fun a => color[Nat.xor w.val a]?.getD 0) ++
          (((g.neighbors[w.val]?.getD []).map fun a => color[a]?.getD 0).mergeSort (· ≤ ·))) x =
      [readColor color x] ++ anchors.map (fun a => color[Nat.xor (encodePoint x).val a]?.getD 0) ++
        ((((List.finRange 512).filter (adj (encodePoint x))).map
          (fun w => readColor color (decodePoint w))).mergeSort (· ≤ ·)) := by
    simp only [readKey, Geometry.count, hneighbors, Array.getElem?_ofFn,
      dif_pos (encodePoint x).isLt, Option.getD_some, List.map_map, readColor_decodePoint]
    rfl
  have hshift :
      anchors.map (fun a => color[Nat.xor (encodePoint (e v)).val a]?.getD 0) =
      anchors.map (fun a => color[Nat.xor (encodePoint v).val a]?.getD 0) := by
    apply List.map_congr_left
    intro a hamem
    rw [readColor_shift color (e v) a (hbound a hamem),
      readColor_shift color v a (hbound a hamem)]
    rw [← ha e he a hamem, ← e.map_add, hc e he, ha e he a hamem]
  let p : Equiv.Perm PackedPoint := pointEquiv.trans (e.toEquiv.trans pointEquiv.symm)
  have hp (w : PackedPoint) : p w = encodePoint (e (decodePoint w)) := rfl
  have hdecode (w : PackedPoint) : decodePoint (p w) = e (decodePoint w) := by
    rw [hp, decodePoint_encodePoint]
  have hneighbor := sorted_neighbors_equiv adj (fun w => readColor color (decodePoint w)) p
    (fun a b => by simpa only [hp] using hadj e he a b)
    (fun w => by rw [hdecode, hc e he]) (encodePoint v)
  simp only [hp, decodePoint_encodePoint] at hneighbor
  rw [hkey, hkey, hc e he v, hshift, hneighbor]

end Lemmata.RM59.CatalogUniform
