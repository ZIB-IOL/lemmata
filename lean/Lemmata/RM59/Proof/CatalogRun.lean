module

public import Lemmata.RM59.Proof.CatalogBilinear
public import Lemmata.RM59.Proof.CatalogOrdinary
public import Lemmata.RM59.Proof.CatalogSeparation

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open scoped BigOperators
open Packed CatalogForms CatalogContractions CatalogGraph CatalogGeometry CatalogSeparation

def familyGroup (family : Fin 348) : Subgroup (CoordinateGroup 9) :=
  MulAction.stabilizer (CoordinateGroup 9) (representative family)

def fixedGroup (family : Fin 348) (anchors : List Nat) : Subgroup (CoordinateGroup 9) :=
  familyGroup family ⊓ ⨅ a ∈ anchors, MulAction.stabilizer (CoordinateGroup 9) (readPoint a)

theorem mem_fixedGroup (family : Fin 348) (anchors : List Nat) (e : CoordinateGroup 9) :
    e ∈ fixedGroup family anchors ↔ e ∈ familyGroup family ∧
      ∀ a ∈ anchors, e (readPoint a) = readPoint a := by
  simp only [fixedGroup, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

@[simp] theorem fixedGroup_nil (family : Fin 348) : fixedGroup family [] = familyGroup family := by
  ext e
  simp only [mem_fixedGroup, List.not_mem_nil, false_implies, implies_true, and_true]

theorem fixedGroup_append_singleton (family : Fin 348) (anchors : List Nat) (a : Nat) :
    fixedGroup family (anchors ++ [a]) =
      fixedGroup family anchors ⊓ MulAction.stabilizer (CoordinateGroup 9) (readPoint a) := by
  ext e
  rw [mem_fixedGroup, Subgroup.mem_inf, mem_fixedGroup, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨he, hfix⟩
    exact ⟨⟨he, fun b hb => hfix b (List.mem_append.mpr (Or.inl hb))⟩,
      hfix a (by simp)⟩
  · rintro ⟨⟨he, hfix⟩, ha⟩
    refine ⟨he, ?_⟩
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hfix b hb
    · have hb' : b = a := List.mem_singleton.mp hb
      subst b
      exact ha

theorem family_triple_invariant (family : Fin 348) (e : CoordinateGroup 9)
    (he : e ∈ familyGroup family) (u v w : Point 9) :
    cubicFormValue (representative family) (e u) (e v) (e w) =
      cubicFormValue (representative family) u v w := by
  have h := cubicFormValue_smul_on_images e (representative family) u v w
  rw [MulAction.mem_stabilizer_iff.mp he] at h
  exact h

theorem family_graph_invariant (family : Fin 348) (e : CoordinateGroup 9)
    (he : e ∈ familyGroup family) (v w : PackedPoint) :
    adjacency (familyBasis family) (encodePoint (e (decodePoint v)))
      (encodePoint (e (decodePoint w))) = adjacency (familyBasis family) v w := by
  rw [family_adjacency_semantic, family_adjacency_semantic,
    decodePoint_encodePoint, decodePoint_encodePoint]
  exact CatalogInvariant.contractionAdjacency_equiv
    (cubicFormValue (representative family)) (cubicFormValue (representative family))
    e.toEquiv e.map_zero (family_triple_invariant family e he) _ _

@[simp] theorem individualize_size (g : Geometry) (color : Array Nat) (anchor : Nat) :
    (individualize g color anchor).size = 512 := by
  simp [individualize, Geometry.count]

theorem individualize_invariant (g : Geometry) (P : CoordinateGroup 9 → Prop)
    (color : Array Nat) (anchor : Nat) (hanchor : anchor < 512)
    (hc : ColorRefinement.Invariant P (readColor color)) :
    ColorRefinement.Invariant (fun e => P e ∧ e (readPoint anchor) = readPoint anchor)
      (readColor (individualize g color anchor)) := by
  apply exactColors_invariant _ _ (by simp [Geometry.count])
  intro e he v
  have hindex (x : Point 9) : (encodePoint x).val = anchor ↔ x = readPoint anchor := by
    constructor
    · intro h
      rw [← readPoint_encodePoint x, h]
    · rintro rfl
      exact encodePoint_readPoint anchor hanchor
  have hfix : e v = readPoint anchor ↔ v = readPoint anchor := by
    constructor
    · intro h
      exact e.injective (h.trans he.2.symm)
    · rintro rfl
      exact he.2
  simp only [readKey, Array.getElem?_ofFn, Geometry.count,
    dif_pos (encodePoint (e v)).isLt, dif_pos (encodePoint v).isLt, Option.getD_some,
    hindex, hfix]
  rw [show color[(encodePoint (e v)).val]?.getD 0 = color[(encodePoint v).val]?.getD 0
    from hc e he.1 v]

def refineOnce (g : Geometry) (anchors : List Nat) (color : Array Nat) : Array Nat :=
  let ordinary := ordinaryColors g anchors color
  if classCount ordinary = classCount color && !anchors.isEmpty then
    bilinearColors g anchors ordinary else ordinary

@[simp] theorem refineOnce_size (g : Geometry) (anchors : List Nat) (color : Array Nat) :
    (refineOnce g anchors color).size = 512 := by
  unfold refineOnce
  dsimp only
  split <;> simp [bilinearColors, ordinaryColors, Geometry.count]

theorem refineOnce_invariant (family : Fin 348) (anchors : List Nat) (color : Array Nat)
    (hbound : ∀ a ∈ anchors, a < 512)
    (hc : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family anchors) (readColor color)) :
    ColorRefinement.Invariant (fun e => e ∈ fixedGroup family anchors)
      (readColor (refineOnce (geometry (family.val + 1)) anchors color)) := by
  have hneighbor : (geometry (family.val + 1)).neighbors = Array.ofFn
      (fun v : PackedPoint => (((List.finRange 512).filter
        (adjacency (familyBasis family) v)).map Fin.val)) :=
    geometry_neighbors family
  have ho := ordinaryColors_invariant (geometry (family.val + 1))
    (fun e => e ∈ fixedGroup family anchors) (adjacency (familyBasis family))
    hneighbor anchors color hbound hc
    (fun e he => family_graph_invariant family e ((mem_fixedGroup _ _ _).mp he).1)
    (fun e he => ((mem_fixedGroup _ _ _).mp he).2)
  unfold refineOnce
  dsimp only
  split
  · exact bilinearColors_invariant (geometry (family.val + 1))
      (fun e => e ∈ fixedGroup family anchors) (representative family) (familyBasis family)
      (family_basis_semantic family) (family_basis_bound family) (geometry_values family)
      anchors _ hbound ho
      (fun e he => family_triple_invariant family e ((mem_fixedGroup _ _ _).mp he).1)
      (fun e he => ((mem_fixedGroup _ _ _).mp he).2)
  · exact ho

theorem stabilize_invariant (family : Fin 348) (anchors : List Nat) (anchor fuel : Nat)
    (color : Array Nat) (hbound : ∀ a ∈ anchors, a < 512)
    (hc : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family anchors) (readColor color)) :
    ColorRefinement.Invariant (fun e => e ∈ fixedGroup family anchors)
      (readColor (stabilize (geometry (family.val + 1)) anchors anchor fuel color)) := by
  induction fuel generalizing color with
  | zero => exact hc
  | succ fuel ih =>
    change ColorRefinement.Invariant _ (readColor (if classSize color anchor = 1 then color else
      if classCount (refineOnce _ anchors color) = classCount color then refineOnce _ anchors color
      else stabilize _ anchors anchor fuel (refineOnce _ anchors color)))
    split
    · exact hc
    · have hr := refineOnce_invariant family anchors color hbound hc
      split
      · exact hr
      · exact ih _ hr

theorem stabilize_size (g : Geometry) (anchors : List Nat) (anchor fuel : Nat)
    (color : Array Nat) (hsize : color.size = 512) :
    (stabilize g anchors anchor fuel color).size = 512 := by
  induction fuel generalizing color with
  | zero => exact hsize
  | succ fuel ih =>
    change (if classSize color anchor = 1 then color else
      if classCount (refineOnce g anchors color) = classCount color then refineOnce g anchors color
      else stabilize g anchors anchor fuel (refineOnce g anchors color)).size = 512
    split
    · exact hsize
    · split
      · exact refineOnce_size _ _ _
      · exact ih _ (refineOnce_size _ _ _)

@[simp] theorem anchorLoop_nil (g : Geometry) (state : AnchorState) :
    anchorLoop g [] state = state := by cases state; rfl

theorem anchorLoop_cons (g : Geometry) (anchor : Nat) (anchors : List Nat) (state : AnchorState) :
    anchorLoop g (anchor :: anchors) state = anchorLoop g anchors (anchorStep g state anchor) := by
  simp [anchorLoop, anchorStep, List.forIn_cons]

theorem anchorLoop_fixed (g : Geometry) (anchors : List Nat) (state : AnchorState) :
    (anchorLoop g anchors state).fixed = state.fixed ++ anchors := by
  induction anchors generalizing state with
  | nil => simp
  | cons anchor anchors ih =>
    rw [anchorLoop_cons, ih]
    simp only [anchorStep, List.append_assoc, List.singleton_append]

theorem select_property (a b : Result) (P : Result → Prop) (ha : P a) (hb : P b) :
    P (if a.bound ≤ b.bound then a else b) := by
  by_cases h : a.bound ≤ b.bound
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

theorem run_invariant (family : Nat) :
    (run family).invariant = (geometry family).vertexKeys.toList.mergeSort
      (fun a b => compare a b != .gt) := by
  rfl

end Lemmata.RM59.CatalogUniform
