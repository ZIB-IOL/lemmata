module

public import Lemmata.Centroid.Proof.GeneralMaximum
public import Lemmata.Centroid.Proof.Construction.Rectangular
public import Lemmata.Centroid.Proof.Construction.HookCertificate

@[expose] public section

open Classical

noncomputable section

namespace Lemmata.Centroid.Construction

variable {F : Type*} [Field F]

private theorem transport_minimal_lower {N M d : ℕ} (hNM : N = M)
    (h : ∃ T : Tensor F (Fin 3) (fun _ => Fin N), Tensor.Concise T ∧
      Tensor.rationalBorderRank T = N ∧ d ≤ Module.finrank F (Tensor.centroid T)) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin M), Tensor.Concise T ∧
      Tensor.rationalBorderRank T = M ∧ d ≤ Module.finrank F (Tensor.centroid T) := by
  cases hNM
  exact h

private theorem exists_minimal_at (n s : ℕ) (hn : 0 < n) (hs : s ≤ 2 * n + 1) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + s)), Tensor.Concise T ∧
      Tensor.rationalBorderRank T = n * (n + 1) + s ∧
        generalBoundAt n s ≤ Module.finrank F (Tensor.centroid T) := by
  by_cases hs₂ : s ≤ 2
  · exact exists_cubePlus n s hn hs₂
  by_cases hsn : s ≤ n
  · exact Circuit.exists_minimal n s (by omega) hsn
  let t := s - n - 1
  have ht : t ≤ n := by dsimp [t]; omega
  have hst : s = n + 1 + t := by dsimp [t]; omega
  by_cases hsq : t ^ 2 ≤ n
  · have h := Rectangular.exists_minimal (F := F) n t hn ht hsq
    have hsize : (n + 1) ^ 2 + t = n * (n + 1) + s := by nlinarith only [hst]
    rw [← hst] at h
    exact transport_minimal_lower hsize h
  · have ht₀ : 0 < t := by
      by_contra hz
      have ht0 : t = 0 := by omega
      exact hsq (by rw [ht0]; simp)
    have h := Hook.exists_minimal (F := F) n t hn ht₀ ht (by omega)
    have hsize : n * (n + 1) + t + (n + 1) = n * (n + 1) + s := by omega
    rw [← hst] at h
    exact transport_minimal_lower hsize h

end Lemmata.Centroid.Construction

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F]

theorem exists_minimal_general_maximizer (N : ℕ) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin N), Concise T ∧
      rationalBorderRank T = N ∧ Module.finrank F (centroid T) = generalBound N := by
  by_cases hsmall : N ≤ 1
  · refine ⟨Construction.diagonal N, Construction.diagonal_concise N,
      Construction.diagonal_rationalBorderRank N,
      le_antisymm (centroid_upper_bound (Construction.diagonal_concise N) N (by simp)) ?_⟩
    simpa only [generalBound, hsmall, ite_true] using Construction.diagonal_centroid_lower_bound (F := F) N
  have hN₂ : 2 ≤ N := by omega
  let n := generalIndex N
  let s := N - n * (n + 1)
  have hn : 0 < n := generalIndex_pos hN₂
  have hs : s ≤ 2 * n + 1 := general_remainder_le hN₂
  have hN : N = n * (n + 1) + s := general_decomposition N
  have hex := Construction.transport_minimal_lower hN.symm
    (Construction.exists_minimal_at (F := F) n s hn hs)
  obtain ⟨T, hT, hrank, hdim⟩ := hex
  refine ⟨T, hT, hrank, le_antisymm (centroid_upper_bound hT N (by simp)) ?_⟩
  rwa [generalBound_eq hN₂ hs hN]

def minimalCubicCentroidDimensions (F : Type*) [Field F] (N : ℕ) : Set ℕ :=
  {d | ∃ T : Tensor F (Fin 3) (fun _ => Fin N), Concise T ∧ rationalBorderRank T = N ∧
    Module.finrank F (centroid T) = d}

theorem minimal_general_maximum (N : ℕ) :
    IsGreatest (minimalCubicCentroidDimensions F N) (generalBound N) := by
  refine ⟨exists_minimal_general_maximizer N, ?_⟩
  rintro d ⟨T, hT, _, rfl⟩
  exact centroid_upper_bound hT N (by simp)

end Lemmata.Centroid.Tensor
