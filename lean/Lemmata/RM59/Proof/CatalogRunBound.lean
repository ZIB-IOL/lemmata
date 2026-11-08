module

public import Lemmata.RM59.Proof.CatalogRun
public import Lemmata.RM59.Proof.CatalogArrayFacts

@[expose] public section

namespace Lemmata.RM59.CatalogUniform

open scoped BigOperators
open Packed

theorem fixedGroup_step_bound (family : Fin 348) (anchors : List Nat)
    (color : Array Nat) (hsize : color.size = 512) (anchor : Nat) (hanchor : anchor < 512)
    (hc : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family anchors) (readColor color)) :
    Nat.card (fixedGroup family anchors) ≤ classSize color anchor *
      Nat.card (fixedGroup family (anchors ++ [anchor])) := by
  classical
  let K := fixedGroup family anchors
  let L := fixedGroup family (anchors ++ [anchor])
  letI : Fintype K := Fintype.ofFinite K
  have hle : L ≤ K := by
    change fixedGroup family (anchors ++ [anchor]) ≤ fixedGroup family anchors
    rw [fixedGroup_append_singleton]
    exact inf_le_left
  have heq : L.subgroupOf K = MulAction.stabilizer K (readPoint anchor) := by
    change (fixedGroup family (anchors ++ [anchor])).subgroupOf (fixedGroup family anchors) = _
    rw [fixedGroup_append_singleton, Subgroup.inf_subgroupOf_left,
      MulAction.stabilizer_subgroupOf]
  have hcover : MulAction.orbit K (readPoint anchor) ⊆
      (ColorRefinement.colorClass (readColor color) (readPoint anchor) : Set (Point 9)) := by
    intro v hv
    obtain ⟨e, rfl⟩ := MulAction.mem_orbit_iff.mp hv
    apply (ColorRefinement.mem_colorClass _ _ _).mpr
    exact hc (e : CoordinateGroup 9) e.property (readPoint anchor)
  have hs := orbit_stabilizer_step_upper (G := K) (readPoint anchor)
    (ColorRefinement.colorClass (readColor color) (readPoint anchor)) hcover
  have hcard : Nat.card (MulAction.stabilizer K (readPoint anchor)) = Nat.card L := by
    rw [← heq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hcard] at hs
  have hclass := classSize_eq_card color hsize (⟨anchor, hanchor⟩ : PackedPoint)
  have hpoint : decodePoint (⟨anchor, hanchor⟩ : PackedPoint) = readPoint anchor := by
    simp only [readPoint, Nat.mod_eq_of_lt hanchor]
  rw [hpoint] at hclass
  simpa only [← Nat.card_eq_fintype_card, ← hclass] using hs

theorem anchorLoop_sound (family : Fin 348) (anchors : List Nat) (state : AnchorState)
    (hfixed : ∀ a ∈ state.fixed, a < 512) (hbound : ∀ a ∈ anchors, a < 512)
    (hsize : state.colors.size = 512)
    (hc : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family state.fixed)
      (readColor state.colors)) :
    let final := anchorLoop (geometry (family.val + 1)) anchors state
    final.colors.size = 512 ∧
      ColorRefinement.Invariant (fun e => e ∈ fixedGroup family final.fixed) (readColor final.colors) ∧
      state.factors.foldl (· * ·) 1 * Nat.card (fixedGroup family state.fixed) ≤
        final.factors.foldl (· * ·) 1 * Nat.card (fixedGroup family final.fixed) := by
  induction anchors generalizing state with
  | nil => simp only [anchorLoop_nil]; exact ⟨hsize, hc, le_rfl⟩
  | cons anchor anchors ih =>
    let g := geometry (family.val + 1)
    let colors := stabilize g state.fixed anchor g.count state.colors
    let next := anchorStep g state anchor
    have ha : anchor < 512 := hbound anchor (by simp)
    have hcs : colors.size = 512 := stabilize_size g _ _ _ _ hsize
    have hci : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family state.fixed)
        (readColor colors) := stabilize_invariant family _ _ _ _ hfixed hc
    have hstep := fixedGroup_step_bound family state.fixed colors hcs anchor ha hci
    have hnfixed : ∀ a ∈ next.fixed, a < 512 := by
      intro a hamem
      change a ∈ state.fixed ++ [anchor] at hamem
      rcases List.mem_append.mp hamem with hamem | hamem
      · exact hfixed a hamem
      · have haeq := List.mem_singleton.mp hamem
        simpa only [haeq] using ha
    have hnsize : next.colors.size = 512 := individualize_size _ _ _
    have hncolor : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family next.fixed)
        (readColor next.colors) := by
      have hi := individualize_invariant g (fun e => e ∈ fixedGroup family state.fixed)
        colors anchor ha hci
      intro e he v
      apply hi e ?_ v
      change e ∈ fixedGroup family (state.fixed ++ [anchor]) at he
      rw [fixedGroup_append_singleton, Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at he
      exact he
    have hr := ih next hnfixed (fun a hamem => hbound a (by simp [hamem])) hnsize hncolor
    change (anchorLoop g (anchor :: anchors) state).colors.size = 512 ∧ _
    rw [anchorLoop_cons]
    refine ⟨hr.1, hr.2.1, le_trans ?_ hr.2.2⟩
    calc
      state.factors.foldl (· * ·) 1 * Nat.card (fixedGroup family state.fixed) ≤
          state.factors.foldl (· * ·) 1 * (classSize colors anchor *
            Nat.card (fixedGroup family (state.fixed ++ [anchor]))) := Nat.mul_le_mul_left _ hstep
      _ = next.factors.foldl (· * ·) 1 * Nat.card (fixedGroup family next.fixed) := by
        simp only [next, anchorStep, colors, Array.foldl_push, Nat.mul_assoc]

theorem valid_anchors_bound (result : Result) (hvalid : result.valid = true) :
    ∀ a ∈ result.anchors, a < 512 := by
  unfold Result.valid at hvalid
  simp only [Bool.and_eq_true_iff] at hvalid
  have hall := hvalid.1.1.1.1.1.1.2
  intro a ha
  simpa using List.all_eq_true.mp hall a ha

theorem valid_terminal (result : Result) (hvalid : result.valid = true) :
    result.terminal.size = 512 ∧ result.terminal.toList.Nodup := by
  unfold Result.valid at hvalid
  simp only [Bool.and_eq_true_iff] at hvalid
  exact ⟨by simpa using hvalid.1.2, by simpa using hvalid.2⟩

theorem runResult_bound (family : Fin 348) (anchors : List Nat)
    (hvalid : (runResult (geometry (family.val + 1)) anchors).valid = true) :
    Nat.card (familyGroup family) ≤ (runResult (geometry (family.val + 1)) anchors).bound := by
  classical
  let g := geometry (family.val + 1)
  let state := anchorLoop g anchors (initialState g)
  have hbound : ∀ a ∈ anchors, a < 512 := valid_anchors_bound _ hvalid
  have hterminal : (terminalColors g anchors 9 state.colors).size = 512 ∧
      (terminalColors g anchors 9 state.colors).toList.Nodup := valid_terminal _ hvalid
  have hinitial : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family [])
      (readColor (initialState g).colors) := by
    apply additionColors_invariant
    exact CatalogSeparation.geometry_colors_invariant family _
      (fun e he => ((mem_fixedGroup _ _ _).mp he).1)
  have hloop : state.colors.size = 512 ∧
      ColorRefinement.Invariant (fun e => e ∈ fixedGroup family state.fixed) (readColor state.colors) ∧
      (initialState g).factors.foldl (· * ·) 1 * Nat.card (fixedGroup family (initialState g).fixed) ≤
        state.factors.foldl (· * ·) 1 * Nat.card (fixedGroup family state.fixed) :=
    anchorLoop_sound family anchors (initialState g) (by simp [initialState])
      hbound (by simp [initialState, additionColors, Geometry.count]) hinitial
  have hfixed : state.fixed = anchors := by
    calc
      state.fixed = (initialState g).fixed ++ anchors := anchorLoop_fixed g anchors (initialState g)
      _ = anchors := rfl
  have hc : ColorRefinement.Invariant (fun e => e ∈ fixedGroup family anchors)
      (readColor state.colors) := by
    have h := hloop.2.1
    rw [hfixed] at h
    exact h
  have ht := terminalColors_invariant g (fun e => e ∈ fixedGroup family anchors)
    anchors hbound (fun e he => ((mem_fixedGroup _ _ _).mp he).2) 9 state.colors hc
  have hinj : Function.Injective (readColor (terminalColors g anchors 9 state.colors)) :=
    readColor_injective _ hterminal.1 hterminal.2
  have hbot : fixedGroup family anchors = ⊥ := by
    apply le_antisymm _ bot_le
    intro e he
    exact Subgroup.mem_bot.mpr (ColorRefinement.eq_one_of_injective_color _ hinj e (ht e he))
  have hstart : (initialState g).factors.foldl (· * ·) 1 *
      Nat.card (fixedGroup family (initialState g).fixed) = Nat.card (familyGroup family) := by
    change 1 * Nat.card (fixedGroup family []) = Nat.card (familyGroup family)
    rw [Nat.one_mul, fixedGroup_nil]
  change Nat.card (familyGroup family) ≤ state.factors.foldl (· * ·) 1
  calc
    Nat.card (familyGroup family) = (initialState g).factors.foldl (· * ·) 1 *
        Nat.card (fixedGroup family (initialState g).fixed) := hstart.symm
    _ ≤ state.factors.foldl (· * ·) 1 * Nat.card (fixedGroup family state.fixed) := hloop.2.2
    _ = state.factors.foldl (· * ·) 1 := by
      rw [hfixed, hbot, Subgroup.card_bot, Nat.mul_one]

theorem invariant_update_preserves (result : Result) (invariant : List (List Nat))
    (target : Nat) (h : result.valid = true → target ≤ result.bound) :
    ({result with invariant := invariant} : Result).valid = true →
      target ≤ ({result with invariant := invariant} : Result).bound := h

theorem run_stabilizer_bound (family : Fin 348)
    (hvalid : (run (family.val + 1)).valid = true) :
    Nat.card (familyGroup family) <= (run (family.val + 1)).bound := by
  let invariant := (geometry (family.val + 1)).vertexKeys.toList.mergeSort
    (fun a b => compare a b != .gt)
  exact select_property (runResult (geometry (family.val + 1)) standardAnchors)
    (runResult (geometry (family.val + 1)) fixedAnchors)
    (fun result => ({result with invariant := invariant} : Result).valid = true ->
      Nat.card (familyGroup family) <= ({result with invariant := invariant} : Result).bound)
    (invariant_update_preserves _ _ _ (runResult_bound family standardAnchors))
    (invariant_update_preserves _ _ _ (runResult_bound family fixedAnchors)) hvalid

end Lemmata.RM59.CatalogUniform
