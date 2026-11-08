module

public import Lemmata.RM59.Proof.CatalogUniform
public import Lemmata.RM59.Proof.ColorRefinement
public import Lemmata.RM59.Proof.Packed
public import Lemmata.RM59.Proof.PackedLinear

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open Packed

def colorEncoder (keys : Array (List Nat)) : Std.TreeMap (List Nat) Nat := Id.run do
  let mut dictionary : Std.TreeMap (List Nat) Nat := {}
  for key in keys do
    dictionary := dictionary.insert key 0
  let mut labels : Std.TreeMap (List Nat) Nat := {}
  for entry in dictionary.toList.zipIdx do
    labels := labels.insert entry.1.1 entry.2
  return labels

theorem exactColors_eq_map (keys : Array (List Nat)) :
    exactColors keys = keys.map (fun key => (colorEncoder keys).getD key 0) := by
  rfl

@[simp] theorem exactColors_size (keys : Array (List Nat)) :
    (exactColors keys).size = keys.size := by
  rw [exactColors_eq_map]
  exact Array.size_map

theorem exactColors_get (keys : Array (List Nat)) (i : Fin keys.size) :
    (exactColors keys)[i.val]?.getD 0 = (colorEncoder keys).getD keys[i.val] 0 := by
  rw [exactColors_eq_map]
  simp only [Array.getElem?_map, Array.getElem?_eq_some_getElem _ _ i.isLt,
    Option.map_some, Option.getD_some]

def readColor (color : Array Nat) (v : Point 9) : Nat :=
  color[(encodePoint v).val]?.getD 0

def readKey (keys : Array (List Nat)) (v : Point 9) : List Nat :=
  keys[(encodePoint v).val]?.getD []

theorem exactColors_invariant (P : CoordinateGroup 9 → Prop)
    (keys : Array (List Nat)) (hsize : keys.size = 512)
    (hkeys : ∀ g, P g → ∀ v, readKey keys (g v) = readKey keys v) :
    ColorRefinement.Invariant P (readColor (exactColors keys)) := by
  intro g hg v
  have hi (x : Point 9) : (encodePoint x).val < keys.size := by
    rw [hsize]
    exact (encodePoint x).isLt
  have hread (x : Point 9) :
      readColor (exactColors keys) x = (colorEncoder keys).getD (readKey keys x) 0 := by
    unfold readColor readKey
    rw [exactColors_get keys ⟨_, hi x⟩, Array.getElem?_eq_some_getElem _ _ (hi x)]
    rfl
  rw [hread (g v), hread v, hkeys g hg v]

def readPoint (a : Nat) : Point 9 := decodePoint ⟨a % 512, Nat.mod_lt _ (by decide)⟩

@[simp] theorem readColor_decodePoint (color : Array Nat) (x : PackedPoint) :
    readColor color (decodePoint x) = color[x.val]?.getD 0 := by
  simp only [readColor, encodePoint_decodePoint]

@[simp] theorem readPoint_encodePoint (x : Point 9) : readPoint (encodePoint x).val = x := by
  unfold readPoint
  simp only [Nat.mod_eq_of_lt (encodePoint x).isLt]
  change decodePoint (encodePoint x) = x
  exact decodePoint_encodePoint x

theorem encodePoint_add_val (x y : Point 9) :
    (encodePoint (x + y)).val = Nat.xor (encodePoint x).val (encodePoint y).val := by
  have hlt : Nat.xor (encodePoint x).val (encodePoint y).val < 512 := by
    rw [Nat.xor_eq]
    exact Nat.xor_lt_two_pow (n := 9) (encodePoint x).isLt (encodePoint y).isLt
  have heq : encodePoint (x + y) = xorPoint (encodePoint x) (encodePoint y) := by
    apply decodePoint_injective
    rw [decodePoint_xorPoint, decodePoint_encodePoint, decodePoint_encodePoint,
      decodePoint_encodePoint]
  have hv := congrArg Fin.val heq
  simpa only [xorPoint, Nat.mod_eq_of_lt hlt] using hv

theorem encodePoint_readPoint (a : Nat) (ha : a < 512) :
    (encodePoint (readPoint a)).val = a := by
  simp only [readPoint, encodePoint_decodePoint, Nat.mod_eq_of_lt ha]

theorem readColor_shift (color : Array Nat) (x : Point 9) (a : Nat) (ha : a < 512) :
    color[Nat.xor (encodePoint x).val a]?.getD 0 = readColor color (x + readPoint a) := by
  unfold readColor
  rw [encodePoint_add_val, encodePoint_readPoint a ha]

theorem shiftColors_invariant (g : Geometry) (P : CoordinateGroup 9 → Prop)
    (anchors : List Nat) (color : Array Nat)
    (hbound : ∀ a ∈ anchors, a < 512)
    (hc : ColorRefinement.Invariant P (readColor color))
    (ha : ∀ e, P e → ∀ a ∈ anchors, e (readPoint a) = readPoint a) :
    ColorRefinement.Invariant P (readColor (shiftColors g anchors color)) := by
  apply exactColors_invariant P _ (by simp [Geometry.count])
  intro e he v
  have hkey (x : Point 9) :
      readKey (Array.ofFn fun w : Fin g.count =>
        color[w.val]?.getD 0 :: anchors.map (fun a => color[Nat.xor w.val a]?.getD 0)) x =
      ColorRefinement.shiftKey (anchors.map readPoint) (readColor color) x := by
    simp only [readKey, Array.getElem?_ofFn, Geometry.count,
      dif_pos (encodePoint x).isLt, Option.getD_some,
      ColorRefinement.shiftKey, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a hamem
    exact readColor_shift color x a (hbound a hamem)
  rw [hkey, hkey]
  apply ColorRefinement.shiftKey_equiv _ _ e (hc e he)
  intro a hamem
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hamem
  exact ha e he b hb

theorem terminalColors_invariant (g : Geometry) (P : CoordinateGroup 9 → Prop)
    (anchors : List Nat) (hbound : ∀ a ∈ anchors, a < 512)
    (ha : ∀ e, P e → ∀ a ∈ anchors, e (readPoint a) = readPoint a)
    (fuel : Nat) (color : Array Nat)
    (hc : ColorRefinement.Invariant P (readColor color)) :
    ColorRefinement.Invariant P (readColor (terminalColors g anchors fuel color)) := by
  induction fuel generalizing color with
  | zero => exact hc
  | succ fuel ih =>
    rw [terminalColors]
    split
    · exact hc
    · apply ih
      exact shiftColors_invariant g P anchors color hbound hc ha

end Lemmata.RM59.CatalogUniform
