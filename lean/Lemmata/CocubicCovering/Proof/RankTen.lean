module

public import Lemmata.CocubicCovering.Compute.CommonProofs
public meta import Lemmata.CocubicCovering.Compute.CommonProofs
public import Lemmata.CocubicCovering.Proof.LocalForest
public meta import Lemmata.CocubicCovering.Proof.LocalForest

@[expose] public section

namespace Lemmata.CocubicCovering.CoveringRankTen

open Module CoveringAffine CoveringBits CoveringWitness CoveringPackedWitness
open CoveringCongruence CoveringCovarianceData CoveringLocal CoveringSymmetry

private theorem symmetric_rows : ∀ i j : Fin 24, matrixRows i j = matrixRows j i := by
  native_decide

theorem fullForm_isRefl (v : Vector 127) : (fullForm v).IsRefl := by
  have hs : (coefficientMatrix matrixRows v).IsSymm := by
    ext i j
    exact congrArg (fun row => evalRow row v) (symmetric_rows j i)
  exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr hs).isRefl

private theorem projection_rows : CoveringLocalRanks.localParameterRows = projectionRows := by
  native_decide

private theorem root_projection (root : Nat) (v : Vector 127)
    (h : localParameterProjection v = (decodeMask root : Vector 15)) :
    rowMap CoveringLocalRanks.localParameterRows v = (decodeMask root : Vector 15) := by
  rw [projection_rows]
  exact h

private theorem common_allowed (root : Fin 6) (v : Vector 127)
    (hv : CoveringWord.allowed (Lemmata.CocubicCovering.Compute.CommonModel.rootData root).assignment v) :
    Lemmata.CocubicCovering.Compute.CommonModel.allowed root.val v := by
  have ht := kernel_thresholds (fullForm v) (fullForm_isRefl v) hv.2.2
  have hr := CoveringLocalRanks.localForm_rank_root _ v (root_projection _ v hv.2.1)
  have hd : (Lemmata.CocubicCovering.Compute.CommonModel.rootData root).required ≤
      finrank Field (fullKernel (fullForm v)) := by
    fin_cases root
    · exact ht.1 (hr.trans CoveringLocalRanks.root0_rank)
    · exact ht.2.1 (hr.trans CoveringLocalRanks.root1_rank)
    · exact ht.2.1 (hr.trans CoveringLocalRanks.root8_rank)
    · exact ht.2.2 (hr.trans CoveringLocalRanks.root80_rank)
    · exact ht.2.2 (hr.trans CoveringLocalRanks.root88_rank)
    · exact ht.2.2 (hr.trans CoveringLocalRanks.root1400_rank)
  unfold Lemmata.CocubicCovering.Compute.CommonModel.allowed
  refine ⟨hv.1, ?_, ?_⟩
  · rw [Lemmata.CocubicCovering.Compute.CommonModel.roots_val]
    exact hv.2.1
  · change (Lemmata.CocubicCovering.Compute.CommonModel.roots root.val).required ≤ finrank Field (fullKernel (fullForm v))
    rw [Lemmata.CocubicCovering.Compute.CommonModel.roots_val]
    exact hd

private theorem no_low_index (root : Fin 6) (v : Vector 127) :
    ¬CoveringWord.allowed (Lemmata.CocubicCovering.Compute.CommonModel.rootData root).assignment v := by
  intro hv
  exact Lemmata.CocubicCovering.Compute.CommonModel.no_allowed root v (common_allowed root v hv)

private theorem no_low_representative (root : Nat) (hroot : root ∈ CoveringLocalRanks.lowRepresentatives)
    (v : Vector 127) : ¬CoveringWord.allowed root v := by
  simp only [CoveringLocalRanks.lowRepresentatives, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at hroot
  rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_low_index 0 v
  · exact no_low_index 1 v
  · exact no_low_index 2 v
  · exact no_low_index 3 v
  · exact no_low_index 4 v
  · exact no_low_index 5 v

private theorem forest_columns : ∀ g i,
    CoveringLocalForest.columns g i = localColumns g i := by native_decide

private theorem forest_step (g : Fin 4) (i : Fin 32768) :
    CoveringLocalForest.step g i = localStep g i := by
  have he : CoveringLocalForest.columns g = localColumns g := funext (forest_columns g)
  unfold CoveringLocalForest.step localStep
  rw [he]

private theorem forest_roots :
    CoveringLocalForest.forest.roots.map Fin.val = CoveringLocalRanks.representatives := by
  native_decide

private theorem representative_partition :
    CoveringLocalRanks.representatives.all (fun root => decide
      (root ∈ CoveringLocalRanks.lowRepresentatives ∨
        root ∈ CoveringLocalRanks.highRepresentatives)) = true := by native_decide

attribute [local irreducible] CoveringBits.encodeVector CoveringBits.decodeMask
  CoveringSymmetry.localParameterProjection

private theorem projection_val (v : Vector 127) :
    (projection v).val = encodeVector (localParameterProjection v) := rfl

private theorem decode_projection (v : Vector 127) :
    localParameterProjection v = (decodeMask (projection v).val : Vector 15) := by
  have hround : (decodeMask (encodeVector (localParameterProjection v)) : Vector 15) =
      localParameterProjection v := decodeMask_encodeVector (localParameterProjection v)
  exact ((congrArg (decodeMask (n := 15)) (projection_val v)).trans hround).symm

set_option maxHeartbeats 500000 in
theorem rank_at_least_ten (v : Vector 127) (hpoint : v (Fin.last 126) = 1) :
    10 ≤ finrank Field (LinearMap.range (fullForm v)) := by
  by_contra hbad
  have hv : finrank Field (LinearMap.range (fullForm v)) ≤ 9 := by omega
  let admissible (p : Vector 127) : Prop :=
    p (Fin.last 126) = 1 ∧ finrank Field (LinearMap.range (fullForm p)) ≤ 9
  obtain ⟨q, hq, hrepresentative⟩ := CoveringOrbit.reach_root_of_checks
    CoveringLocalForest.forest CoveringLocalForest.step projection (fun g p => move g p) admissible
    (fun g p => (projection_move g p).trans (forest_step g (projection p)).symm)
    (fun g p hp => ⟨(move_last g p).trans hp.1, by rw [fullRank_move]; exact hp.2⟩)
    CoveringLocalForest.checked v ⟨hpoint, hv⟩
  have hp : localParameterProjection q = (decodeMask (projection q).val : Vector 15) :=
    decode_projection q
  have hallowed : CoveringWord.allowed (projection q).val q := by
    change q (Fin.last 126) = 1 ∧
      localParameterProjection q = (decodeMask (projection q).val : Vector 15) ∧
      finrank Field (LinearMap.range (fullForm q)) ≤ 9
    exact ⟨hq.1, hp, hq.2⟩
  have hmember : (projection q).val ∈ CoveringLocalRanks.representatives := by
    rw [← forest_roots]
    exact List.mem_map.mpr ⟨projection q, hrepresentative, rfl⟩
  have hwhich := of_decide_eq_true
    ((List.all_eq_true.mp representative_partition) (projection q).val hmember)
  rcases hwhich with hlow | hhigh
  · exact no_low_representative _ hlow q hallowed
  · have hlower := CoveringLocalRanks.high_ranks _ hhigh
    have hsub := Matrix.rank_submatrix_le (coefficientMatrix matrixRows q)
      CoveringMatrix.localInclusion CoveringMatrix.localInclusion
    have he : (coefficientMatrix matrixRows q).submatrix
        CoveringMatrix.localInclusion CoveringMatrix.localInclusion =
          CoveringLocalRanks.rootMatrix (projection q).val :=
      (CoveringLocalRanks.local_submatrix q).trans
        (congrArg (coefficientMatrix CoveringLocalRanks.localRows) (root_projection _ q hp))
    have hlocal : (CoveringLocalRanks.rootMatrix (projection q).val).rank ≤
        (coefficientMatrix matrixRows q).rank :=
      (congrArg Matrix.rank he).symm.le.trans hsub
    have hfull := CoveringRankWitness.toBilin_rank (coefficientMatrix matrixRows q)
    have hten : 10 ≤ finrank Field (LinearMap.range (fullForm q)) := by
      exact (hlower.trans hlocal).trans hfull.symm.le
    have hsmall := hq.2
    omega

end Lemmata.CocubicCovering.CoveringRankTen
