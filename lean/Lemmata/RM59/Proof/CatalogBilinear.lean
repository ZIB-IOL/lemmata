module

public import Lemmata.RM59.Proof.CatalogColors
public import Lemmata.RM59.Proof.CatalogGraph
public import Lemmata.RM59.Proof.PackedParity
public import Lemmata.RM59.Proof.HistogramCache

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open scoped BigOperators
open Packed CatalogForms CatalogContractions CatalogGraph

def functionalKeys (color : Array Nat) : Array (List Nat) :=
  Array.ofFn fun f : PackedPoint =>
    (HistogramCache.histogram (classCount color) (List.range 512)
      (fun w => color[w]?.getD 0) (fun w => PackedParity.parity9 (Nat.land f.val w))).toList

set_option maxRecDepth 8192 in
theorem functionalColors_eq (g : Geometry) (color : Array Nat) :
    functionalColors g color = exactColors (functionalKeys color) := rfl

@[simp] theorem functionalKeys_size (color : Array Nat) : (functionalKeys color).size = 512 := by
  simp [functionalKeys]

def palette (color : Array Nat) : List Nat :=
  List.ofFn (fun r : Fin (classCount color) => r.val)

theorem functionalKey_semantic (color : Array Nat) (f : PackedPoint) :
    (functionalKeys color)[f.val]?.getD [] =
      ColorRefinement.functionalHistogram (readColor color) (palette color)
        (SupportForms.evaluation (natRow f.val)) := by
  rw [functionalKeys, Array.getElem?_ofFn, dif_pos f.isLt, Option.getD_some,
    HistogramCache.histogram_range_toList]
  unfold ColorRefinement.functionalHistogram palette
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext r
  apply Fintype.sum_equiv pointEquiv _ _
  intro w
  change (if PackedParity.parity9 (Nat.land f.val w.val) ∧ color[w.val]?.getD 0 = r.val
      then 1 else 0) =
    (if readColor color (decodePoint w) = r.val ∧
      SupportForms.evaluation (natRow f.val) (decodePoint w) = 1 then 1 else 0)
  simp only [readColor, encodePoint_decodePoint]
  rw [← natRow_packed w, ← PackedParity.parity_land]
  cases h : PackedParity.parity9 (Nat.land f.val w.val) <;> simp [h, and_comm]

def profileEncoder (color : Array Nat) (key : List Nat) : Nat :=
  (colorEncoder (functionalKeys color)).getD key 0

theorem functionalColors_lookup (g : Geometry) (color : Array Nat) (f : PackedPoint) :
    (functionalColors g color)[f.val]?.getD 0 =
      profileEncoder color (ColorRefinement.functionalHistogram (readColor color) (palette color)
        (SupportForms.evaluation (natRow f.val))) := by
  have hlt : f.val < (functionalKeys color).size := by simpa using f.isLt
  have hk := functionalKey_semantic color f
  rw [Array.getElem?_eq_some_getElem _ _ hlt, Option.getD_some] at hk
  rw [functionalColors_eq, exactColors_get (functionalKeys color) ⟨f.val, hlt⟩]
  unfold profileEncoder
  rw [hk]

theorem functionalColors_pairValue (g : Geometry) (color : Array Nat)
    (T : CubicForm) (basis : Array (Array Nat))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j))
    (hb : BasisBound basis) (x y : PackedPoint) :
    (functionalColors g color)[pairValue basis x y]?.getD 0 =
      profileEncoder color (ColorRefinement.bilinearHistogram (cubicFormValue T)
        (readColor color) (palette color) (decodePoint x) (decodePoint y)) := by
  let p : PackedPoint := ⟨pairValue basis x y, pairValue_bound basis hb x y⟩
  rw [functionalColors_lookup g color p]
  apply congrArg (profileEncoder color)
  unfold ColorRefinement.bilinearHistogram
  apply congrArg (ColorRefinement.functionalHistogram (readColor color) (palette color))
  funext w
  change SupportForms.evaluation (natRow (pairValue basis x y)) w = _
  rw [pairValue_semantic T basis hbasis, ← value_as_evaluation]

set_option maxRecDepth 8192 in
theorem bilinearColors_invariant (g : Geometry) (P : CoordinateGroup 9 → Prop)
    (T : CubicForm) (basis : Array (Array Nat))
    (hbasis : ∀ i j : Fin 9,
      natRow ((basis[i.val]?.getD #[])[j.val]?.getD 0) =
        contractionPoint T (basisPoint i) (basisPoint j))
    (hb : BasisBound basis) (hvalues : g.values = pairTable basis)
    (anchors : List Nat) (color : Array Nat)
    (hbound : ∀ a ∈ anchors, a < 512)
    (hc : ColorRefinement.Invariant P (readColor color))
    (ht : ∀ e, P e → ∀ u v w,
      cubicFormValue T (e u) (e v) (e w) = cubicFormValue T u v w)
    (ha : ∀ e, P e → ∀ a ∈ anchors, e (readPoint a) = readPoint a) :
    ColorRefinement.Invariant P (readColor (bilinearColors g anchors color)) := by
  apply exactColors_invariant P _ (by simp [Geometry.count])
  intro e he v
  have hkey (x : Point 9) :
      readKey (Array.ofFn fun w : Fin g.count =>
        color[w.val]?.getD 0 :: anchors.map (fun a =>
          (functionalColors g color)[(g.values[a]?.getD #[])[w.val]?.getD 0]?.getD 0)) x =
      ColorRefinement.bilinearKey (cubicFormValue T) (anchors.map readPoint)
        (palette color) (readColor color) (profileEncoder color) x := by
    simp only [readKey, Array.getElem?_ofFn, Geometry.count,
      dif_pos (encodePoint x).isLt, Option.getD_some,
      ColorRefinement.bilinearKey, List.map_map]
    apply congrArg (List.cons (readColor color x))
    apply List.map_congr_left
    intro a hamem
    dsimp only [Function.comp_apply]
    have habound := hbound a hamem
    have hraw : (g.values[a]?.getD #[])[(encodePoint x).val]?.getD 0 =
        pairValue basis (⟨a, habound⟩ : PackedPoint) (encodePoint x) := by
      rw [hvalues]
      rfl
    have haPoint : decodePoint (⟨a, habound⟩ : PackedPoint) = readPoint a := by
      simp only [readPoint, Nat.mod_eq_of_lt habound]
    have hpair := congrArg₂
      (ColorRefinement.bilinearHistogram (cubicFormValue T) (readColor color) (palette color))
      haPoint (decodePoint_encodePoint x)
    exact (congrArg (fun index => (functionalColors g color)[index]?.getD 0) hraw).trans
      ((functionalColors_pairValue g color T basis hbasis hb
        (⟨a, habound⟩ : PackedPoint) (encodePoint x)).trans
          (congrArg (profileEncoder color) hpair))
  calc
    _ = ColorRefinement.bilinearKey (cubicFormValue T) (anchors.map readPoint)
        (palette color) (readColor color) (profileEncoder color) (e v) := hkey (e v)
    _ = ColorRefinement.bilinearKey (cubicFormValue T) (anchors.map readPoint)
        (palette color) (readColor color) (profileEncoder color) v := by
      apply ColorRefinement.bilinearKey_equiv _ _ _ _ _ e (hc e he) (ht e he)
      intro a hamem
      obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hamem
      exact ha e he b hbmem
    _ = _ := (hkey v).symm

end Lemmata.RM59.CatalogUniform
