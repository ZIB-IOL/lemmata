module

public import Lemmata.RM59.Proof.ProjectionIndependent
public import Lemmata.RM59.Proof.ProjectionWitnessChecks
public import Lemmata.RM59.Proof.ProjectionPacked
public import Lemmata.RM59.Proof.PullbackEquiv

@[expose] public section

namespace Lemmata.RM59.Family53Five

open scoped Matrix
open Lemmata.RM59.SupportForms Lemmata.RM59.ProjectionGeometry Lemmata.RM59.ProjectionTupleChecks

abbrev FieldPoint := TraceGeometry.FieldPoint
abbrev FieldMatrix := TraceGeometry.FieldMatrix

def seed : Finset (Point 9) := Packed.decodeWord FieldData.support53

theorem seed_card : seed.card = 32 := by
  calc
    seed.card = FieldData.support53.length :=
      Packed.decodeWord_card FieldData.support53 FieldData.support53_data.2
    _ = 32 := FieldData.support53_data.1

theorem seed_lowerZero : LowerZero seed :=
  Packed.zero_supportMoments_of_packedMoments (d := 2) FieldData.support53
    FieldData.support53_data.2 (fun mask hmask => (FieldData.lower_moments mask hmask).2.1)

def frobeniusSupport : Nat → Finset (Point 9)
  | 0 => seed
  | n + 1 => (frobeniusSupport n).image TraceFrobenius.pointAction

theorem frobeniusSupport_card (n : Nat) : (frobeniusSupport n).card = 32 := by
  induction n with
  | zero => exact seed_card
  | succ n ih =>
    rw [frobeniusSupport, Finset.card_image_of_injective _ TraceFrobenius.pointAction_injective, ih]

theorem frobeniusSupport_moments (n : Nat) : MatchSupportMoments 3 (frobeniusSupport n) seed := by
  induction n with
  | zero => exact MatchSupportMoments.refl _ _
  | succ n ih =>
    exact (matchSupportMoments_image ih TraceFrobenius.pointAction
      TraceFrobenius.pointAction_injective).trans TraceVertical.support53_frobenius_moments

theorem frobeniusPoint_mem (n : Nat) (x : Point 9) (hx : x ∈ seed) :
    Family35.frobeniusPoint n x ∈ frobeniusSupport n := by
  induction n with
  | zero => exact hx
  | succ n ih => exact Finset.mem_image.mpr ⟨Family35.frobeniusPoint n x, ih, rfl⟩

theorem affine_moments {P : Finset (Point 9)} (hP : MatchSupportMoments 3 P seed)
    (A : FieldMatrix) (hA : A.det = 1)
    (hK : (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace)
    (t : Point 9) :
    MatchSupportMoments 3 (translateSupport (P.image (TraceActions.pointAction A)) t) seed := by
  have hinj := TraceActions.pointAction_injective A (by rw [hA]; exact one_ne_zero)
  have hmatrix : MatchSupportMoments 3 (P.image (TraceActions.pointAction A)) seed :=
    (matchSupportMoments_image hP _ hinj).trans
      (TraceVertical.support53_image_moments _ hinj
        (TraceActions.traceForm_comp_pullback A hA) (TraceVertical.matrix_image_vertical A hK))
  have hlow : LowerZero (P.image (TraceActions.pointAction A)) := by
    intro s hs
    rw [hmatrix s (hs.trans (by decide : 2 ≤ 3)), seed_lowerZero s hs]
  exact (matchSupportMoments_translate _ hlow t).trans hmatrix

theorem equal_normalizers (source target : Fin 5 → FieldPoint) (normal : NormalForm)
    (hs : normalizeRows (ProjectionEquivalence.rows source 0)
      (ProjectionEquivalence.rows source 1) (ProjectionEquivalence.rows source 2) = some normal)
    (ht : normalizeRows (ProjectionEquivalence.rows target 0)
      (ProjectionEquivalence.rows target 1) (ProjectionEquivalence.rows target 2) = some normal) :
    ∃ A : FieldMatrix, ∃ b : FieldPoint, A.det = 1 ∧
      (fun x => A *ᵥ x) '' TraceGeometry.verticalSpace = TraceGeometry.verticalSpace ∧
      ∀ i, A *ᵥ source i + b = target i := by
  obtain ⟨p, q, _, _, hd, he⟩ := ProjectionTupleSound.normalizeRows_sound _ _ _ normal hs
  obtain ⟨p', q', _, _, hd', he'⟩ := ProjectionTupleSound.normalizeRows_sound _ _ _ normal ht
  exact ProjectionEquivalence.equal_five_normal_forms source target p q p' q' hd hd'
    (ProjectionTupleSound.equal_atPivots _ _ _ _ _ _ p q p' q' hd hd' (he.symm.trans he'))

def witnessCodes (w : ProjectionWitnessChecks.Witness) : Vector (Fin 512) 5 :=
  w.codes.map fun x => ProjectionChecks.frobeniusPoint x w.power.val

theorem witness_source_mem (w : ProjectionWitnessChecks.Witness)
    (hw : ∀ i : Fin 5, w.codes.get i ∈ FieldData.support53) (i : Fin 5) :
    FieldCoordinates.pointEquiv.symm (ProjectionPacked.fieldPoints (witnessCodes w) i) ∈
      frobeniusSupport w.power.val := by
  have hcode : Packed.decodePoint (w.codes.get i) ∈ seed := by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨w.codes.get i, hw i, rfl⟩
  have he : FieldCoordinates.pointEquiv.symm
      (ProjectionPacked.fieldPoints (witnessCodes w) i) =
      Family35.frobeniusPoint w.power.val (Packed.decodePoint (w.codes.get i)) := by
    apply FieldCoordinates.pointEquiv.injective
    rw [FieldCoordinates.pointEquiv.apply_symm_apply]
    simp only [ProjectionPacked.fieldPoints, witnessCodes, Vector.get,
      Vector.toArray_map, Array.getElem_map]
    change FieldData.coordinates
      (ProjectionChecks.frobeniusPoint (w.codes.get i) w.power.val) = _
    rw [← FieldCoordinates.packed_coordinates, ProjectionPacked.decode_frobenius] <;> rfl
  rw [he]
  exact frobeniusPoint_mem _ _ hcode

theorem cover_projected_five (target : Fin 5 → FieldPoint)
    (hi : LinearIndependent Field (column (ProjectionEquivalence.rows target 0)
      (ProjectionEquivalence.rows target 1) 0)) :
    ∃ G : Finset (Point 9), MatchSupportMoments 3 G seed ∧ G.card = 32 ∧
      ∀ i, FieldCoordinates.pointEquiv.symm (target i) ∈ G := by
  obtain ⟨normal, ht⟩ := ProjectionIndependent.normalization_exists
    (ProjectionEquivalence.rows target 0) (ProjectionEquivalence.rows target 1)
    (ProjectionEquivalence.rows target 2) hi
  have hp := ProjectionRref.normalization_projection_mem _ _ _ normal ht
  have hind := ProjectionIndependent.normalization_independent _ _ _ normal ht hi
  have hb := (ProjectionTupleSound.independentProjection_iff_of_mem normal.projection hp).2 hind
  obtain ⟨w, hw, hn⟩ := ProjectionWitnessChecks.witness_exists normal.projection hp hb normal.lift
  let source := ProjectionPacked.fieldPoints (witnessCodes w)
  have hs : normalizeRows (ProjectionEquivalence.rows source 0)
      (ProjectionEquivalence.rows source 1) (ProjectionEquivalence.rows source 2) = some normal := by
    rw [← ProjectionPacked.normalizeFive_vector]
    simpa only [ProjectionWitnessChecks.witnessNormal, witnessCodes, Vector.toList_map] using hn
  obtain ⟨A, b, hA, hK, hmap⟩ := equal_normalizers source target normal hs ht
  let t := FieldCoordinates.pointEquiv.symm b
  let G := translateSupport
    ((frobeniusSupport w.power.val).image (TraceActions.pointAction A)) t
  refine ⟨G, affine_moments (frobeniusSupport_moments _) A hA hK t, ?_, ?_⟩
  · change (translateSupport
      ((frobeniusSupport w.power.val).image (TraceActions.pointAction A)) t).card = 32
    rw [translateSupport,
      Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h),
      Finset.card_image_of_injective _
        (TraceActions.pointAction_injective A (by rw [hA]; exact one_ne_zero)),
      frobeniusSupport_card]
  · intro i
    apply Finset.mem_image.mpr
    refine ⟨TraceActions.pointAction A (FieldCoordinates.pointEquiv.symm (source i)),
      Finset.mem_image.mpr ⟨_, witness_source_mem w hw i, rfl⟩, ?_⟩
    apply FieldCoordinates.pointEquiv.injective
    simpa only [t, map_add, TraceActions.pointAction_coordinates,
      FieldCoordinates.pointEquiv.apply_symm_apply] using hmap i

end Lemmata.RM59.Family53Five
