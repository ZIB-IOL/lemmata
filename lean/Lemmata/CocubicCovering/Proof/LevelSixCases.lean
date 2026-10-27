module

public import Lemmata.CocubicCovering.Proof.LevelSixProblem
public meta import Lemmata.CocubicCovering.Proof.LevelSixProblem
public import Lemmata.CocubicCovering.Proof.LocalTwelve
public meta import Lemmata.CocubicCovering.Proof.LocalTwelve
public import Lemmata.CocubicCovering.Proof.LocalForest
public meta import Lemmata.CocubicCovering.Proof.LocalForest
public import Lemmata.CocubicCovering.Proof.Geometry
public meta import Lemmata.CocubicCovering.Proof.Geometry

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringLevelSixCases

open Module Covering CoveringAffine CoveringBits CoveringCongruence
open CoveringLocalRanks CoveringLevelSixReduction CoveringLevelSixProblem

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def sixRoots : List Nat := [1, 8]
def eightRoots : List Nat := [80, 88, 1400]
def tenRoots : List Nat := [12, 81, 89, 104, 522, 1550, 1573, 1580]
def twelveRoots : List Nat := [1184, 1188, 1192, 1193]

abbrev profile (root k : Nat) : Prop :=
  (root = 0 ∧ k = 7) ∨
    (root ∈ sixRoots ∧ 4 ≤ k ∧ k ≤ 6) ∨
    (root ∈ eightRoots ∧ 3 ≤ k ∧ k ≤ 4) ∨
    (root ∈ tenRoots ∧ k = 2)

private theorem partition : representatives.all (fun root => decide
    (root = 0 ∨ root ∈ sixRoots ∨ root ∈ eightRoots ∨ root ∈ tenRoots ∨
      root ∈ twelveRoots)) = true := by native_decide

private theorem profiles_covered : representatives.all (fun root => decide
    (∀ k : Fin 13, profile root k.val → ∃ i : Fin 21,
      (CoveringLevelSixCoreData.roots (CoveringLevelSixCoreData.searchRoot i)).assignment = root ∧
      (CoveringLevelSixCoreData.roots (CoveringLevelSixCoreData.searchRoot i)).required = k.val)) =
      true := by native_decide

private theorem six_rank (root : Nat) (hroot : root ∈ sixRoots) :
    (rootMatrix root).rank = 6 := by
  simp only [sixRoots, List.mem_cons, List.mem_nil_iff, or_false] at hroot
  rcases hroot with rfl | rfl
  · exact root1_rank
  · exact root8_rank

private theorem eight_rank (root : Nat) (hroot : root ∈ eightRoots) :
    (rootMatrix root).rank = 8 := by
  simp only [eightRoots, List.mem_cons, List.mem_nil_iff, or_false] at hroot
  rcases hroot with rfl | rfl | rfl
  · exact root80_rank
  · exact root88_rank
  · exact root1400_rank

private theorem ten_rank_lower (root : Nat) (hroot : root ∈ tenRoots) :
    10 ≤ (rootMatrix root).rank := by
  apply high_ranks root
  simp only [tenRoots, List.mem_cons, List.mem_nil_iff, or_false] at hroot
  rcases hroot with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem projection_rows :
    localParameterRows = CoveringSymmetry.projectionRows := by native_decide

private theorem projection_def (v : Vector 127) :
    CoveringSymmetry.localParameterProjection v = rowMap CoveringSymmetry.projectionRows v := rfl

private theorem old_localRank_eq (root : Nat) (v : Vector 127)
    (hp : rowMap localParameterRows v = (decodeMask root : Vector 15)) :
    finrank Field (LinearMap.range
      (CoveringLocal.localForm (CoveringSymmetry.fullForm v))) = (rootMatrix root).rank :=
  localForm_rank_root root v hp

attribute [local irreducible] CoveringLevelSixReduction.fullForm CoveringSymmetry.fullForm
  CoveringSymmetry.localParameterProjection CoveringBits.decodeMask CoveringBits.encodeVector
  CoveringLevelSixCoreData.states CoveringLevelSixCoreData.entries

noncomputable def localRank (v : Vector 127) : Nat :=
  finrank Field (LinearMap.range (gram (CoveringLevelSixReduction.fullForm v)
    CoveringLevelSixReduction.localEmbedding))

private theorem localRank_eq (root : Nat) (v : Vector 127)
    (hprojection : CoveringSymmetry.localParameterProjection v = decodeMask root) :
    localRank v = (rootMatrix root).rank := by
  have hp : rowMap localParameterRows v = (decodeMask root : Vector 15) :=
    (congrArg (fun rows : Fin 15 → Nat => rowMap rows v) projection_rows).trans
      ((projection_def v).symm.trans hprojection)
  have he := congrArg (fun B : LinearMap.BilinForm Field (Vector 12) =>
    finrank Field (LinearMap.range B)) (local_restriction v)
  exact he.trans (old_localRank_eq root v hp)

private theorem kernel_add_localRank_le (v : Vector 127) :
    finrank Field (CoveringLevelSixReduction.fullKernel v) + localRank v ≤ 12 := by
  have hle := Submodule.finrank_mono
    ((fullKernel_le_common v).trans
      (CoveringLocal.fullKernel_le_localRadical (CoveringSymmetry.fullForm v)))
  have hnull := (CoveringLocal.localForm (CoveringSymmetry.fullForm v)).finrank_range_add_finrank_ker
  change finrank Field (LinearMap.range (CoveringLocal.localForm (CoveringSymmetry.fullForm v))) +
    finrank Field (CoveringLocal.localRadical (CoveringSymmetry.fullForm v)) =
      finrank Field (Vector 12) at hnull
  have hd : finrank Field (Vector 12) = 12 := Module.finrank_fin_fun Field
  have he := congrArg (fun B : LinearMap.BilinForm Field (Vector 12) =>
    finrank Field (LinearMap.range B)) (local_restriction v)
  change localRank v = _ at he
  omega

theorem representative_allowed (root : Nat) (hroot : root ∈ representatives)
    (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hprojection : CoveringSymmetry.localParameterProjection v = decodeMask root)
    (hrank : finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10) :
    ∃ i : Fin 21, allowed (CoveringLevelSixCoreData.searchRoot i) v := by
  let k := finrank Field (CoveringLevelSixReduction.fullKernel v)
  have hupper : k + localRank v ≤ 12 := kernel_add_localRank_le v
  have hlower := local_dimension_inequality v
  change 24 ≤ finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) +
    localRank v + 2 * k at hlower
  have hlocal : localRank v ≤ 10 :=
    (CoveringGeometry.gram_rank_le (CoveringLevelSixReduction.fullForm v)
      CoveringLevelSixReduction.localEmbedding).trans hrank
  have he := localRank_eq root v hprojection
  have hcases := of_decide_eq_true ((List.all_eq_true.mp partition) root hroot)
  have hprofile : profile root k := by
    rcases hcases with rfl | hsix | height | hten | htwelve
    · have hk : k ≤ 7 := fullKernel_le_seven v hpoint (by
        exact hprojection.trans (decodeMask_zero 15))
      rw [root0_rank] at he
      exact Or.inl ⟨rfl, by omega⟩
    · have h := six_rank root hsix
      exact Or.inr (Or.inl ⟨hsix, by omega, by omega⟩)
    · have h := eight_rank root height
      exact Or.inr (Or.inr (Or.inl ⟨height, by omega, by omega⟩))
    · have h := ten_rank_lower root hten
      exact Or.inr (Or.inr (Or.inr ⟨hten, by omega⟩))
    · have h := CoveringLocalTwelve.rank_lower root htwelve
      omega
  have hcovered := of_decide_eq_true ((List.all_eq_true.mp profiles_covered) root hroot)
  obtain ⟨i, hlocal, hdimension⟩ := hcovered (⟨k, by omega⟩ : Fin 13) hprofile
  refine ⟨i, hpoint, ?_, ?_, hrank⟩
  · exact hprojection.trans (congrArg (decodeMask (n := 15)) hlocal).symm
  · exact hdimension.symm

theorem representative_entry_feasible (root : Nat) (hroot : root ∈ representatives)
    (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hprojection : CoveringSymmetry.localParameterProjection v = decodeMask root)
    (hrank : finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10) :
    ∃ i : Fin 21, CoveringFiniteDAG.feasible allowed CoveringLevelSixReduction.fullKernel
      (CoveringLevelSixCoreData.states (CoveringLevelSixCoreData.entries i)) := by
  obtain ⟨i, hv⟩ := representative_allowed root hroot v hpoint hprojection hrank
  refine ⟨i, ?_⟩
  unfold CoveringFiniteDAG.feasible CoveringSearch.Feasible
  rw [CoveringLevelSixCoreData.entry_roots, CoveringLevelSixCoreData.entry_cores]
  refine ⟨v, hv, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

private theorem forest_columns : ∀ g i,
    CoveringLocalForest.columns g i = CoveringSymmetry.localColumns g i := by native_decide

private theorem forest_step (g : Fin 4) (i : Fin 32768) :
    CoveringLocalForest.step g i = CoveringSymmetry.localStep g i := by
  have he : CoveringLocalForest.columns g = CoveringSymmetry.localColumns g :=
    funext (forest_columns g)
  unfold CoveringLocalForest.step CoveringSymmetry.localStep
  rw [he]

private theorem forest_roots :
    CoveringLocalForest.forest.roots.map Fin.val = representatives := by native_decide

private theorem projection_val (v : Vector 127) :
    (CoveringSymmetry.projection v).val =
      encodeVector (CoveringSymmetry.localParameterProjection v) := rfl

private theorem decode_projection (v : Vector 127) :
    CoveringSymmetry.localParameterProjection v =
      (decodeMask (CoveringSymmetry.projection v).val : Vector 15) := by
  have hround :
      (decodeMask (encodeVector (CoveringSymmetry.localParameterProjection v)) : Vector 15) =
        CoveringSymmetry.localParameterProjection v :=
    decodeMask_encodeVector (CoveringSymmetry.localParameterProjection v)
  exact ((congrArg (decodeMask (n := 15)) (projection_val v)).trans hround).symm

theorem some_entry_feasible (v : Vector 127) (hpoint : v (Fin.last 126) = 1)
    (hrank : finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm v)) ≤ 10) :
    ∃ i : Fin 21, CoveringFiniteDAG.feasible allowed CoveringLevelSixReduction.fullKernel
      (CoveringLevelSixCoreData.states (CoveringLevelSixCoreData.entries i)) := by
  let admissible (p : Vector 127) : Prop :=
    p (Fin.last 126) = 1 ∧
      finrank Field (LinearMap.range (CoveringLevelSixReduction.fullForm p)) ≤ 10
  obtain ⟨q, hq, hrepresentative⟩ := CoveringOrbit.reach_root_of_checks
    CoveringLocalForest.forest CoveringLocalForest.step CoveringSymmetry.projection
    (fun g p => CoveringLevelSixSymmetry.forwardMove g p) admissible
    (fun g p => (CoveringLevelSixSymmetry.projection_forwardMove g p).trans
      (forest_step g (CoveringSymmetry.projection p)).symm)
    (fun g p hp => ⟨(CoveringLevelSixSymmetry.forward_last g p).trans hp.1, by
      rw [CoveringLevelSixSymmetry.forward_rank]
      exact hp.2⟩)
    CoveringLocalForest.checked v ⟨hpoint, hrank⟩
  have hmember : (CoveringSymmetry.projection q).val ∈ representatives := by
    rw [← forest_roots]
    exact List.mem_map.mpr ⟨CoveringSymmetry.projection q, hrepresentative, rfl⟩
  exact representative_entry_feasible _ hmember q hq.1 (decode_projection q) hq.2

end Lemmata.CocubicCovering.CoveringLevelSixCases
