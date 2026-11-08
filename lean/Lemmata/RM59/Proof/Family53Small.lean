module

public import Lemmata.RM59.Proof.Family53Five
public import Lemmata.RM59.Proof.VerticalFrames
public meta import Lemmata.RM59.Proof.FieldData
public meta import Lemmata.RM59.Proof.VerticalFrames

@[expose] public section

namespace Lemmata.RM59.Family53Small

open scoped Matrix symmDiff
open Lemmata.RM59.Family53Five Lemmata.RM59.VerticalFrames
open Lemmata.RM59.SupportForms

abbrev FieldPoint := TraceGeometry.FieldPoint

def sourceCodes : Fin 3 → Fin 512 := ![1, 449, 8]

def source : Fin 3 → FieldPoint := fun i => FieldData.coordinates (sourceCodes i)

theorem source_mem (i : Fin 3) : FieldCoordinates.pointEquiv.symm (source i) ∈ seed := by
  have hc : sourceCodes i ∈ FieldData.support53 := by
    fin_cases i <;> decide
  rw [source, ← FieldCoordinates.packed_coordinates,
    FieldCoordinates.pointEquiv.symm_apply_apply]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨sourceCodes i, hc, rfl⟩)

theorem source_vertical : source 1 - source 0 = TraceGeometry.vertical (F8Scalar.ofNat 7) := by
  decide

theorem source_horizontal : horizontal (source 2 - source 0) ≠ 0 := by decide

theorem cover_vertical_triple (target : Fin 3 → FieldPoint) (w : F8Scalar) (hw : w ≠ 0)
    (ht : target 1 - target 0 = TraceGeometry.vertical w)
    (ht2 : horizontal (target 2 - target 0) ≠ 0) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 32 ∧
      ∀ i, FieldCoordinates.pointEquiv.symm (target i) ∈ G := by
  obtain ⟨A, b, hA, hK, hmap⟩ := affine_vertical_triple source target (F8Scalar.ofNat 7) w
    (by decide) hw source_vertical ht source_horizontal ht2
  let t := FieldCoordinates.pointEquiv.symm b
  let G := translateSupport (seed.image (TraceActions.pointAction A)) t
  refine ⟨G, affine_moments (MatchSupportMoments.refl _ _) A hA hK t, ?_, ?_⟩
  · change (translateSupport (seed.image (TraceActions.pointAction A)) t).card = 32
    rw [translateSupport,
      Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h),
      Finset.card_image_of_injective _
        (TraceActions.pointAction_injective A (by rw [hA]; exact one_ne_zero)), seed_card]
  · intro i
    apply Finset.mem_image.mpr
    refine ⟨TraceActions.pointAction A (FieldCoordinates.pointEquiv.symm (source i)),
      Finset.mem_image.mpr ⟨_, source_mem i, rfl⟩, ?_⟩
    apply FieldCoordinates.pointEquiv.injective
    simpa only [t, map_add, TraceActions.pointAction_coordinates,
      FieldCoordinates.pointEquiv.apply_symm_apply] using hmap i

theorem nonzero_vertical_difference (x y : FieldPoint) (hne : x ≠ y)
    (hh : horizontal (y - x) = 0) : (y - x) 2 ≠ 0 := by
  intro hz
  have he := (horizontal_eq_zero_iff_vertical (y - x)).1 hh
  rw [hz] at he
  have hv : TraceGeometry.vertical 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  rw [hv] at he
  exact hne (sub_eq_zero.mp he).symm

theorem cover_vertical_pair_triple (x y z : FieldPoint) (hne : x ≠ y)
    (hh : horizontal (y - x) = 0) (hz : horizontal (z - x) ≠ 0) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 32 ∧
      FieldCoordinates.pointEquiv.symm x ∈ G ∧
      FieldCoordinates.pointEquiv.symm y ∈ G ∧ FieldCoordinates.pointEquiv.symm z ∈ G := by
  obtain ⟨G, hG, hc, hm⟩ := cover_vertical_triple ![x, y, z] ((y - x) 2)
    (nonzero_vertical_difference x y hne hh)
    ((horizontal_eq_zero_iff_vertical (y - x)).1 hh) hz
  exact ⟨G, hG, hc, hm 0, hm 1, hm 2⟩

theorem cover_pair (x y : FieldPoint) (hne : x ≠ y) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 32 ∧
      FieldCoordinates.pointEquiv.symm x ∈ G ∧ FieldCoordinates.pointEquiv.symm y ∈ G := by
  by_cases hh : horizontal (y - x) = 0
  · obtain ⟨G, hG, hc, hx, hy, _⟩ := cover_vertical_pair_triple x y (x + ![1, 0, 0]) hne hh
      (by simpa only [add_sub_cancel_left] using (show horizontal ![1, 0, 0] ≠ 0 by decide))
    exact ⟨G, hG, hc, hx, hy⟩
  · obtain ⟨G, hG, hc, hm⟩ := cover_vertical_triple ![x, x + TraceGeometry.vertical 1, y] 1
      one_ne_zero (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left]) hh
    exact ⟨G, hG, hc, hm 0, hm 2⟩

theorem completion_small (P : Finset (Point 9))
    (hcard : P.card ∈ ({1, 3} : Finset Nat)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  have hcases : P.card = 1 ∨ P.card = 3 := by simpa using hcard
  rcases hcases with h1 | h3
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    let a := FieldCoordinates.pointEquiv.symm (source 0)
    let G := translateSupport seed (p - a)
    have hG : G.card = 32 := by
      change (translateSupport seed (p - a)).card = 32
      rw [translateSupport,
        Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), seed_card]
    have hpG : p ∈ G := by
      apply Finset.mem_image.mpr
      refine ⟨a, source_mem 0, ?_⟩
      simp [sub_eq_add_neg, add_comm, add_left_comm]
    have hi : 0 < (G ∩ P).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpG, hp⟩⟩
    refine ⟨G, matchSupportMoments_translate seed seed_lowerZero _, ?_⟩
    apply symmDiff_card_le_of_intersection
    omega
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    obtain ⟨G, hG, hc, haG, hbG⟩ := cover_pair
      (FieldCoordinates.pointEquiv a) (FieldCoordinates.pointEquiv b)
      (fun he => hab (FieldCoordinates.pointEquiv.injective he))
    simp only [FieldCoordinates.pointEquiv.symm_apply_apply] at haG hbG
    have hi : 2 ≤ (G ∩ P).card := by
      have hs : ({a, b} : Finset (Point 9)) ⊆ G ∩ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨haG, ha⟩
        · exact Finset.mem_inter.mpr ⟨hbG, hb⟩
      have htwo : ({a, b} : Finset (Point 9)).card = 2 := by simp [hab]
      simpa only [htwo] using Finset.card_le_card hs
    refine ⟨G, hG, ?_⟩
    apply symmDiff_card_le_of_intersection
    omega

end Lemmata.RM59.Family53Small
