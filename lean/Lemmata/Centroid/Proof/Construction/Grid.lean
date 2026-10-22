module

public import Lemmata.Centroid.Proof.Construction.LowerBound
public import Lemmata.Centroid.Proof.Construction.Relabel
public import Lemmata.Centroid.Proof.Construction.DirectSum
public import Lemmata.Centroid.Proof.Construction.Diagonal
public import Lemmata.Centroid.Def.Bounds
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction

noncomputable section

variable {F : Type*} [Field F]

local instance : DecidableEq (Fin 3) := Classical.decEq _

abbrev CubeCore (n : ℕ) : Fin 3 → Type := fun _ => Fin n

theorem cube_coordinate_card (n : ℕ) (i : Fin 3) :
    Fintype.card (BigCentroid.Coordinates (CubeCore n) i) = n * (n + 1) := by
  have hc : Fintype.card {j : Fin 3 // j ≠ i} = 2 := by
    simp [Fintype.card_subtype_compl]
  simp only [BigCentroid.Coordinates, Fintype.card_sum, BigCentroid.Opposite,
    Fintype.card_pi, CubeCore, Fintype.card_fin, Finset.prod_const, Finset.card_univ, hc]
  ring

def cubeCoordinates (n : ℕ) (i : Fin 3) :
    BigCentroid.Coordinates (CubeCore n) i ≃ Fin (n * (n + 1)) :=
  Fintype.equivFinOfCardEq (cube_coordinate_card n i)

def cube (n : ℕ) : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1))) :=
  Tensor.relabel (cubeCoordinates n) (BigCentroid.tensor (F := F) (U := CubeCore n))

theorem cube_concise (n : ℕ) (hn : 0 < n) : Tensor.Concise (cube (F := F) n) := by
  have : ∀ i, Nonempty (CubeCore n i) := fun _ => ⟨⟨0, hn⟩⟩
  exact (BigCentroid.concise (F := F) (U := CubeCore n)).relabel (cubeCoordinates n)

theorem cube_rationalBorderRank (n : ℕ) (hn : 0 < n) :
    Tensor.rationalBorderRank (cube (F := F) n) = n * (n + 1) := by
  have hbase := BigCentroid.minimal_border_rank (F := F) (fun _ : Fin 3 => n) (fun _ => hn)
  have hmaximum : BigCentroid.maximumSide (fun _ : Fin 3 => n) = n * (n + 1) := by
    have hside (i : Fin 3) : n + ∏ _j : {j : Fin 3 // j ≠ i}, n = n * (n + 1) := by
      have hc : Fintype.card {j : Fin 3 // j ≠ i} = 2 := by
        simp [Fintype.card_subtype_compl]
      simp only [Finset.prod_const, Finset.card_univ, hc]
      ring
    unfold BigCentroid.maximumSide
    simp_rw [hside]
    exact Finset.sup_const Finset.univ_nonempty _
  rw [hmaximum] at hbase
  apply le_antisymm
  · apply (Tensor.rationalBorderRank_le_iff _ _).mpr
    exact ((Tensor.rationalBorderRank_le_iff _ _).mp hbase.le).relabel (cubeCoordinates n)
  · simpa using (cube_concise (F := F) n hn).le_rationalBorderRank 0

theorem cube_centroid_lower_bound (n : ℕ) (hn : 0 < n) :
    n ^ 3 + 1 ≤ Module.finrank F (Tensor.centroid (cube (F := F) n)) := by
  have : ∀ i, Nonempty (CubeCore n i) := fun _ => ⟨⟨0, hn⟩⟩
  have h := Realization.full_centroid_lower_bound (F := F) (U := CubeCore n)
  have hcard : (∏ i : Fin 3, Fintype.card (CubeCore n i)) = n ^ 3 := by
    simp [CubeCore, pow_succ]
  rw [hcard] at h
  have h' : n ^ 3 + 1 ≤ Module.finrank F
      (Tensor.centroid (BigCentroid.tensor (F := F) (U := CubeCore n))) := by
    simpa [Nat.add_comm] using h
  exact h'.trans (Tensor.finrank_centroid_le_relabel (cubeCoordinates n) _)

theorem exists_cube (n : ℕ) (hn : 0 < n) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1))),
      Tensor.Concise T ∧ Tensor.rationalBorderRank T = n * (n + 1) ∧
        generalBoundAt n 0 ≤ Module.finrank F (Tensor.centroid T) := by
  exact ⟨cube n, cube_concise n hn, cube_rationalBorderRank n hn,
    by simpa using cube_centroid_lower_bound n hn⟩

def cubePlus (n s : ℕ) : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + s)) :=
  Tensor.relabel (fun _ => finSumFinEquiv)
    (Tensor.directSum (cube n) (diagonal s))

theorem cubePlus_concise (n s : ℕ) (hn : 0 < n) :
    Tensor.Concise (cubePlus (F := F) n s) :=
  ((cube_concise n hn).directSum (diagonal_concise s)).relabel (fun _ => finSumFinEquiv)

theorem cubePlus_rationalBorderRank (n s : ℕ) (hn : 0 < n) :
    Tensor.rationalBorderRank (cubePlus (F := F) n s) = n * (n + 1) + s := by
  apply le_antisymm
  · apply (Tensor.rationalBorderRank_le_iff _ _).mpr
    have hcube := Tensor.rationalBorderRankAtMost_rank (cube (F := F) n)
    rw [cube_rationalBorderRank n hn] at hcube
    have hdiag := (diagonal_rankAtMost (F := F) s).rationalBorderRankAtMost
    exact (hcube.directSum hdiag).relabel (fun _ => finSumFinEquiv)
  · simpa using (cubePlus_concise (F := F) n s hn).le_rationalBorderRank 0

theorem cubePlus_centroid_lower_bound (n s : ℕ) (hn : 0 < n) :
    n ^ 3 + 1 + s ≤ Module.finrank F (Tensor.centroid (cubePlus (F := F) n s)) := by
  have h := Tensor.finrank_centroid_directSum (cube (F := F) n) (diagonal (F := F) s)
  have h' := (Nat.add_le_add (cube_centroid_lower_bound (F := F) n hn)
    (diagonal_centroid_lower_bound (F := F) s)).trans h
  exact h'.trans (Tensor.finrank_centroid_le_relabel (fun _ => finSumFinEquiv) _)

theorem generalBoundAt_small_remainder (n s : ℕ) (hn : 0 < n) (hs : s ≤ 2) :
    generalBoundAt n s = n ^ 3 + 1 + s := by
  interval_cases s
  · simp [generalBoundAt]
  · simp [generalBoundAt]
  · by_cases h : n = 1
    · subst n; decide
    · have h2 : 2 ≤ n := by omega
      simp [generalBoundAt, h2]

theorem exists_cubePlus (n s : ℕ) (hn : 0 < n) (hs : s ≤ 2) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + s)),
      Tensor.Concise T ∧ Tensor.rationalBorderRank T = n * (n + 1) + s ∧
        generalBoundAt n s ≤ Module.finrank F (Tensor.centroid T) := by
  refine ⟨cubePlus n s, cubePlus_concise n s hn, cubePlus_rationalBorderRank n s hn, ?_⟩
  rw [generalBoundAt_small_remainder n s hn hs]
  exact cubePlus_centroid_lower_bound n s hn

theorem exists_minimal_small_remainder (n s : ℕ) (hn : 0 < n) (hs : s ≤ 2) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + s)),
      Tensor.Concise T ∧ Tensor.rationalBorderRank T = n * (n + 1) + s ∧
        generalBound (n * (n + 1) + s) ≤ Module.finrank F (Tensor.centroid T) := by
  have hN : 2 ≤ n * (n + 1) + s := by nlinarith
  rw [generalBound_eq hN (by omega : s ≤ 2 * n + 1) rfl]
  exact exists_cubePlus n s hn hs

end

end Lemmata.Centroid.Construction
