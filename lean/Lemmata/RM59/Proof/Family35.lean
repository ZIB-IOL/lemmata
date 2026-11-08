module

public import Lemmata.RM59.Proof.TraceFrobenius
public import Lemmata.RM59.Proof.FieldRank
public import Lemmata.RM59.Proof.PullbackEquiv
public import Lemmata.RM59.Proof.Intersections
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public meta import Lemmata.RM59.Proof.TraceFrobenius
public meta import Lemmata.RM59.Proof.FrameGeometry
public meta import Lemmata.RM59.Proof.FieldCoordinates
public meta import Lemmata.RM59.Proof.FieldData
public meta import Lemmata.RM59.Proof.Packed
public meta import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public meta import Mathlib.LinearAlgebra.Alternating.Basic
public meta import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Data.Finset.Image

@[expose] public section

namespace Lemmata.RM59.Family35

open scoped BigOperators Matrix symmDiff
open Lemmata.RM59.SupportForms

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def seed : Finset (Point 9) := Packed.decodeWord FieldData.support35

theorem seed_card : seed.card = 30 := by
  calc
    seed.card = FieldData.support35.length :=
      Packed.decodeWord_card FieldData.support35 FieldData.support35_data.2
    _ = 30 := FieldData.support35_data.1

theorem seed_lowerZero : LowerZero seed :=
  Packed.zero_supportMoments_of_packedMoments (d := 2) FieldData.support35
    FieldData.support35_data.2 (fun mask hmask => (FieldData.lower_moments mask hmask).1)

def frobeniusPoint : Nat → Point 9 → Point 9
  | 0 => id
  | n + 1 => fun x => TraceFrobenius.pointAction (frobeniusPoint n x)

theorem affine_moments {P : Finset (Point 9)} (hP : MatchSupportMoments 3 P seed)
    (A : FieldMatrix) (hA : A.det = 1) (t : Point 9) :
    MatchSupportMoments 3 (translateSupport (P.image (TraceActions.pointAction A)) t) seed := by
  have hinj := TraceActions.pointAction_injective A (by rw [hA]; exact one_ne_zero)
  have hmatrix : MatchSupportMoments 3 (P.image (TraceActions.pointAction A)) seed :=
    (matchSupportMoments_image hP _ hinj).trans (TraceActions.support35_image_moments A hA)
  have hlow : LowerZero (P.image (TraceActions.pointAction A)) := by
    intro s hs
    rw [hmatrix s (hs.trans (by decide : 2 ≤ 3)), seed_lowerZero s hs]
  exact (matchSupportMoments_translate _ hlow t).trans hmatrix

def sourceCodes (r : Fin 7) : Fin 4 → Packed.PackedPoint :=
  ![35, 39, 26, (![64, 136, 196, 261, 322, 400, 484] : Fin 7 → Packed.PackedPoint) r]

def sourcePoint (r : Fin 7) (i : Fin 4) : Point 9 := Packed.decodePoint (sourceCodes r i)

theorem sourcePoint_mem : ∀ r : Fin 7, ∀ i : Fin 4, sourcePoint r i ∈ seed := by
  native_decide

def sourceFrame (r : Fin 7) : Fin 4 → FieldPoint :=
  fun i => FieldCoordinates.pointEquiv (sourcePoint r i)

theorem sourceFrame_determinant : ∀ r : Fin 7,
    FrameGeometry.frameDeterminant (sourceFrame r) =
      F8Scalar.ofNat (r.val + 1) := by native_decide

theorem determinant_sources : ∀ d : F8Scalar, d ≠ 0 →
    ∃ r : Fin 7, d = F8Scalar.ofNat (r.val + 1) := by decide

theorem cover_field_frame (q : Fin 4 → FieldPoint)
    (hq : FrameGeometry.frameDeterminant q ≠ 0) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 30 ∧
      ∀ i, FieldCoordinates.pointEquiv.symm (q i) ∈ G := by
  classical
  obtain ⟨r, hdet⟩ := determinant_sources _ hq
  have hsource : FrameGeometry.frameDeterminant (sourceFrame r) =
      FrameGeometry.frameDeterminant q := by
    rw [sourceFrame_determinant, ← hdet]
  obtain ⟨A, b, hA, hmap⟩ := FrameGeometry.exists_affine_det_one_frame_map
    (sourceFrame r) q (by rw [hsource]; exact hq) hsource.symm
  let t := FieldCoordinates.pointEquiv.symm b
  let G := translateSupport (seed.image (TraceActions.pointAction A)) t
  refine ⟨G, affine_moments (MatchSupportMoments.refl _ _) A hA t, ?_, ?_⟩
  · change (translateSupport (seed.image
      (TraceActions.pointAction A)) t).card = 30
    rw [translateSupport,
      Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h),
      Finset.card_image_of_injective _
        (TraceActions.pointAction_injective A (by rw [hA]; exact one_ne_zero)),
      seed_card]
  · intro i
    apply Finset.mem_image.mpr
    refine ⟨TraceActions.pointAction A (sourcePoint r i),
      Finset.mem_image.mpr ⟨_, sourcePoint_mem r i, rfl⟩, ?_⟩
    apply FieldCoordinates.pointEquiv.injective
    simpa only [sourceFrame, t, map_add, TraceActions.pointAction_coordinates,
      FieldCoordinates.pointEquiv.apply_symm_apply] using hmap i

theorem frame_injective (q : Fin 4 → FieldPoint)
    (hq : FrameGeometry.frameDeterminant q ≠ 0) : Function.Injective q := by
  have hLI := Matrix.linearIndependent_cols_of_det_ne_zero hq
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ b =>
      exfalso
      apply hLI.ne_zero b
      change q b.succ - q 0 = 0
      exact sub_eq_zero.mpr hij.symm
  | succ a =>
    cases j using Fin.cases with
    | zero =>
      exfalso
      apply hLI.ne_zero a
      change q a.succ - q 0 = 0
      exact sub_eq_zero.mpr hij
    | succ b =>
      have hab : a = b := hLI.injective (by
        change q a.succ - q 0 = q b.succ - q 0
        rw [hij])
      exact congrArg Fin.succ hab

theorem prefix_intersection {m : Nat} (hm : m ≤ 4) (P G : Finset (Point 9))
    (q : Fin 4 → FieldPoint) (hq : FrameGeometry.frameDeterminant q ≠ 0)
    (hG : ∀ i, FieldCoordinates.pointEquiv.symm (q i) ∈ G)
    (hP : ∀ i : Fin m, FieldCoordinates.pointEquiv.symm (q (Fin.castLE hm i)) ∈ P) :
    m ≤ (G ∩ P).card := by
  classical
  let f : Fin m → Point 9 := fun i => FieldCoordinates.pointEquiv.symm (q (Fin.castLE hm i))
  have hf : Function.Injective f :=
    FieldCoordinates.pointEquiv.symm.injective.comp
      ((frame_injective q hq).comp (Fin.castLE_injective hm))
  have hsubset : Finset.univ.image f ⊆ G ∩ P := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_inter.mpr ⟨hG _, hP i⟩
  have hc := Finset.card_le_card hsubset
  simpa only [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] using hc

theorem completion (P : Finset (Point 9))
    (hp : AffineIndependent Field ((↑) : P → Point 9))
    (hcard : P.card ∈ ({1, 3, 5, 7, 9} : Finset Nat)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ (G ∆ P).card ≤ 31 := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
  rcases hcard with h1 | h3 | h5 | h7 | h9
  · refine ⟨seed, MatchSupportMoments.refl _ _, ?_⟩
    apply symmDiff_card_le_of_intersection
    rw [seed_card, h1]
    omega
  · obtain ⟨p, hpP⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    let a := sourcePoint 0 0
    let G := translateSupport seed (p - a)
    have hG : G.card = 30 := by
      change (translateSupport seed (p - a)).card = 30
      rw [translateSupport, Finset.card_image_of_injective _
        (fun _ _ h => add_right_cancel h), seed_card]
    have hpG : p ∈ G := by
      apply Finset.mem_image.mpr
      refine ⟨a, sourcePoint_mem 0 0, ?_⟩
      simp [sub_eq_add_neg, add_comm, add_left_comm]
    have hi : 0 < (G ∩ P).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpG, hpP⟩⟩
    refine ⟨G, matchSupportMoments_translate seed seed_lowerZero _, ?_⟩
    apply symmDiff_card_le_of_intersection
    omega
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    have habF : FieldCoordinates.pointEquiv a ≠ FieldCoordinates.pointEquiv b :=
      fun h => hab (FieldCoordinates.pointEquiv.injective h)
    obtain ⟨c, d, hdet⟩ := FrameGeometry.extend_distinct_pair
      (FieldCoordinates.pointEquiv a) (FieldCoordinates.pointEquiv b) habF 1
    let q : Fin 4 → FieldPoint :=
      ![FieldCoordinates.pointEquiv a, FieldCoordinates.pointEquiv b, c, d]
    have hq : FrameGeometry.frameDeterminant q ≠ 0 := by rw [hdet]; exact one_ne_zero
    obtain ⟨G, hG, hGcard, hGmem⟩ := cover_field_frame q hq
    have hprefix : ∀ i : Fin 2,
        FieldCoordinates.pointEquiv.symm (q (Fin.castLE (by decide : 2 ≤ 4) i)) ∈ P := by
      intro i
      fin_cases i
      · simpa [q] using ha
      · simpa [q] using hb
    have hi := prefix_intersection (by decide : 2 ≤ 4) P G q hq hGmem hprefix
    refine ⟨G, hG, ?_⟩
    apply symmDiff_card_le_of_intersection
    omega
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    let base : P := ⟨a, ha⟩
    let p : P → FieldPoint := fun x => FieldCoordinates.pointEquiv (x : Point 9)
    have hpF : AffineIndependent Field p :=
      hp.map' FieldCoordinates.pointEquiv.toAffineEquiv.toAffineMap
        FieldCoordinates.pointEquiv.injective
    obtain ⟨b, c, hbc⟩ := FieldRank.exists_independent_triple p hpF base (by
      simpa only [Fintype.card_coe, h7] using (by decide : 3 < 6))
    obtain ⟨d, hdet⟩ := FrameGeometry.extend_independent_triple
      (p base) (p b) (p c) hbc 1
    let q : Fin 4 → FieldPoint := ![p base, p b, p c, d]
    have hq : FrameGeometry.frameDeterminant q ≠ 0 := by rw [hdet]; exact one_ne_zero
    obtain ⟨G, hG, hGcard, hGmem⟩ := cover_field_frame q hq
    have hprefix : ∀ i : Fin 3,
        FieldCoordinates.pointEquiv.symm (q (Fin.castLE (by decide : 3 ≤ 4) i)) ∈ P := by
      intro i
      fin_cases i
      · simpa [q, p, base] using ha
      · simpa [q, p] using b.property
      · simpa [q, p] using c.property
    have hi := prefix_intersection (by decide : 3 ≤ 4) P G q hq hGmem hprefix
    refine ⟨G, hG, ?_⟩
    apply symmDiff_card_le_of_intersection
    omega
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    let base : P := ⟨a, ha⟩
    let p : P → FieldPoint := fun x => FieldCoordinates.pointEquiv (x : Point 9)
    have hpF : AffineIndependent Field p :=
      hp.map' FieldCoordinates.pointEquiv.toAffineEquiv.toAffineMap
        FieldCoordinates.pointEquiv.injective
    obtain ⟨indices, hdet⟩ := FieldRank.exists_full_frame p hpF base (by
      simpa only [Fintype.card_coe, h9] using (by decide : 6 < 8))
    let q : Fin 4 → FieldPoint := p ∘ indices
    obtain ⟨G, hG, hGcard, hGmem⟩ := cover_field_frame q hdet
    have hprefix : ∀ i : Fin 4,
        FieldCoordinates.pointEquiv.symm (q (Fin.castLE (by decide : 4 ≤ 4) i)) ∈ P := by
      intro i
      simpa [q, p, Function.comp_def] using
        (indices (Fin.castLE (by decide : 4 ≤ 4) i)).property
    have hi := prefix_intersection (by decide : 4 ≤ 4) P G q hdet hGmem hprefix
    refine ⟨G, hG, ?_⟩
    apply symmDiff_card_le_of_intersection
    omega

end Lemmata.RM59.Family35
