module

public import Lemmata.Centroid.Proof.General.UpperBound
public import Lemmata.Centroid.Proof.Construction.Grid
public import Lemmata.Centroid.Proof.Construction.Circuit
public import Lemmata.Centroid.Proof.Construction.RectangularConcise
public import Lemmata.Centroid.Proof.Construction.HookConcise

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Construction

variable {F : Type*} [Field F]

theorem exists_rectangular_maximizer (n t : ℕ) (hn : 0 < n) (ht : t ≤ n)
    (htsq : t ^ 2 ≤ n) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin ((n + 1) ^ 2 + t)),
      Tensor.Concise T ∧ Module.finrank F (Tensor.centroid T) = generalBound ((n + 1) ^ 2 + t) := by
  let c (i : Fin 3) := Fintype.equivFinOfCardEq (Rectangular.coordinate_card n t i)
  let T := Tensor.relabel c (Rectangular.tensor (F := F) n t hn ht)
  have hT : Tensor.Concise T := (Rectangular.concise n t hn ht).relabel c
  refine ⟨T, hT, le_antisymm (Tensor.centroid_upper_bound hT _ (by simp)) ?_⟩
  have hlower := (Rectangular.centroid_lower_bound (F := F) n t hn ht).trans
    (Tensor.finrank_centroid_le_relabel c _)
  have hdecomp : (n + 1) ^ 2 + t = n * (n + 1) + (n + 1 + t) := by ring
  rw [generalBound_eq (by nlinarith : 2 ≤ (n + 1) ^ 2 + t)
    (by omega : n + 1 + t ≤ 2 * n + 1) hdecomp,
    generalBoundAt_second hn, Nat.sub_eq_zero_of_le htsq, Nat.add_zero]
  exact hlower

theorem exists_first_band_maximizer (n s : ℕ) (hn : 0 < n) (hs : s ≤ n) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + s)),
      Tensor.Concise T ∧ Module.finrank F (Tensor.centroid T) = generalBound (n * (n + 1) + s) := by
  have hN : 2 ≤ n * (n + 1) + s := by nlinarith
  have hsn : s ≤ 2 * n + 1 := by omega
  have hex : ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + s)), Tensor.Concise T ∧
      generalBoundAt n s ≤ Module.finrank F (Tensor.centroid T) := by
    by_cases hs₂ : s ≤ 2
    · obtain ⟨T, hT, _, hdim⟩ := exists_cubePlus (F := F) n s hn hs₂
      exact ⟨T, hT, hdim⟩
    · obtain ⟨T, hT, _, hdim⟩ := Circuit.exists_minimal (F := F) n s (by omega) hs
      exact ⟨T, hT, hdim⟩
  obtain ⟨T, hT, hlower⟩ := hex
  refine ⟨T, hT, le_antisymm (Tensor.centroid_upper_bound hT _ (by simp)) ?_⟩
  rwa [generalBound_eq hN hsn rfl]

theorem exists_hook_maximizer (n t : ℕ) (hn : 0 < n) (ht : t ≤ n) (htsq : n < t ^ 2) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + t + (n + 1))),
      Tensor.Concise T ∧
        Module.finrank F (Tensor.centroid T) = generalBound (n * (n + 1) + t + (n + 1)) := by
  have ht₀ : 0 < t := by
    by_contra hz
    have ht0 : t = 0 := by omega
    simp only [ht0, zero_pow (by decide : 2 ≠ 0), Nat.not_lt_zero] at htsq
  let c (i : Fin 3) := Fintype.equivFinOfCardEq (Hook.coordinate_card n t i)
  let T := Tensor.relabel c (Hook.tensor (F := F) n t ht)
  have hT : Tensor.Concise T := (Hook.concise n t hn ht₀ ht).relabel c
  refine ⟨T, hT, le_antisymm (Tensor.centroid_upper_bound hT _ (by simp)) ?_⟩
  have hlower := (Hook.centroid_lower_bound (F := F) n t ht).trans
    (Tensor.finrank_centroid_le_relabel c _)
  have hdecomp : n * (n + 1) + t + (n + 1) = n * (n + 1) + (n + 1 + t) := by ring
  rw [generalBound_eq (by nlinarith : 2 ≤ n * (n + 1) + t + (n + 1))
    (by omega : n + 1 + t ≤ 2 * n + 1) hdecomp, generalBoundAt_second hn]
  have hsub : t ^ 2 - n + n = t ^ 2 := Nat.sub_add_cancel htsq.le
  have heq : n ^ 3 + n * (n + 1 + t) + 1 + (t ^ 2 - n) =
      1 + (n * (n * (n + 1) + t) + t ^ 2) := by nlinarith only [hsub]
  rw [heq]
  exact hlower

end Lemmata.Centroid.Construction

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F]

theorem exists_general_maximizer (N : ℕ) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin N),
      Concise T ∧ Module.finrank F (centroid T) = generalBound N := by
  by_cases hsmall : N ≤ 1
  · refine ⟨Construction.diagonal N, Construction.diagonal_concise N,
      le_antisymm (centroid_upper_bound (Construction.diagonal_concise N) N (by simp)) ?_⟩
    simpa only [generalBound, hsmall, ite_true] using Construction.diagonal_centroid_lower_bound (F := F) N
  have hN₂ : 2 ≤ N := by omega
  let n := generalIndex N
  let s := N - n * (n + 1)
  have hn : 0 < n := generalIndex_pos hN₂
  have hs : s ≤ 2 * n + 1 := general_remainder_le hN₂
  have hN : N = n * (n + 1) + s := general_decomposition N
  by_cases hsn : s ≤ n
  · have h := Construction.exists_first_band_maximizer (F := F) n s hn hsn
    exact hN.symm ▸ h
  · let t := s - n - 1
    have ht : t ≤ n := by dsimp [t]; omega
    have hst : s = n + 1 + t := by dsimp [t]; omega
    by_cases hsq : t ^ 2 ≤ n
    · have h := Construction.exists_rectangular_maximizer (F := F) n t hn ht hsq
      have hsize : (n + 1) ^ 2 + t = N := by nlinarith only [hN, hst]
      exact hsize ▸ h
    · have h := Construction.exists_hook_maximizer (F := F) n t hn ht (by omega)
      have hsize : n * (n + 1) + t + (n + 1) = N := by omega
      exact hsize ▸ h

def cubicCentroidDimensions (F : Type*) [Field F] (N : ℕ) : Set ℕ :=
  {d | ∃ T : Tensor F (Fin 3) (fun _ => Fin N), Concise T ∧ Module.finrank F (centroid T) = d}

theorem general_maximum (N : ℕ) : IsGreatest (cubicCentroidDimensions F N) (generalBound N) := by
  refine ⟨exists_general_maximizer N, ?_⟩
  rintro d ⟨T, hT, rfl⟩
  exact centroid_upper_bound hT N (by simp)

end Lemmata.Centroid.Tensor
