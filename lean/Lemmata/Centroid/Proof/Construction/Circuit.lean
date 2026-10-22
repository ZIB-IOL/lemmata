module

public import Lemmata.Centroid.Proof.Construction.CircuitSplit
public import Lemmata.Centroid.Proof.Construction.LowerBound
public import Lemmata.Centroid.Proof.Construction.Relabel

@[expose] public section

namespace Lemmata.Centroid.Construction.Circuit

noncomputable section

variable {F : Type*} [Field F]

abbrev size (q ν : ℕ) := (q + 1 + ν) * (q + 2 + ν) + (q + 1)

def coordinateEquiv (q ν : ℕ) (i : Fin 3) : Coordinates q ν i ≃ Fin (size q ν) :=
  Fintype.equivFinOfCardEq (coordinate_card q ν i)

def witness (q ν : ℕ) : Tensor F (Fin 3) (fun _ => Fin (size q ν)) :=
  Tensor.relabel (coordinateEquiv q ν) (tensor q ν)

theorem witness_concise (q ν : ℕ) (hq : 0 < q) :
    Tensor.Concise (witness (F := F) q ν) :=
  (concise q ν hq).relabel (coordinateEquiv q ν)

theorem witness_rationalBorderRank (q ν : ℕ) (hq : 0 < q) :
    Tensor.rationalBorderRank (witness (F := F) q ν) = size q ν := by
  apply le_antisymm
  · exact (Tensor.rationalBorderRank_le_iff _ _).mpr
      ((rationalBorderRankAtMost q ν hq).relabel (coordinateEquiv q ν))
  · simpa using (witness_concise (F := F) q ν hq).le_rationalBorderRank 0

theorem witness_centroid_lower_bound (q ν : ℕ) :
    (q + 1 + ν) ^ 3 + q * (q + 1) + 1 ≤
      Module.finrank F (Tensor.centroid (witness (F := F) q ν)) :=
  (centroid_lower_bound q ν).trans (Tensor.finrank_centroid_le_relabel (coordinateEquiv q ν) _)

theorem exists_minimal (n s : ℕ) (hs : 2 ≤ s) (hsn : s ≤ n) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin (n * (n + 1) + s)),
      Tensor.Concise T ∧ Tensor.rationalBorderRank T = n * (n + 1) + s ∧
        generalBoundAt n s ≤ Module.finrank F (Tensor.centroid T) := by
  have hq : 0 < s - 1 := by omega
  have hn : s - 1 + 1 + (n - s) = n := by omega
  have hsize : size (s - 1) (n - s) = n * (n + 1) + s := by
    unfold size
    rw [hn]
    have hnext : s - 1 + 2 + (n - s) = n + 1 := by omega
    rw [hnext]
    omega
  have hbound : generalBoundAt n s = n ^ 3 + (s - 1) * (s - 1 + 1) + 1 := by
    simp only [generalBoundAt, show s ≠ 0 by omega, show s ≠ 1 by omega,
      ite_false, hsn, ite_true]
    congr 2
    have h : s - 1 + 1 = s := by omega
    rw [h, Nat.mul_comm]
  rw [← hsize]
  refine ⟨witness (s - 1) (n - s), witness_concise _ _ hq,
    witness_rationalBorderRank _ _ hq, ?_⟩
  have h := witness_centroid_lower_bound (F := F) (s - 1) (n - s)
  rwa [hn, ← hbound] at h

end

end Lemmata.Centroid.Construction.Circuit
