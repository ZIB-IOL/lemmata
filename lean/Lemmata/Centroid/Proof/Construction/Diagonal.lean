module

public import Lemmata.Centroid.Proof.Construction.LowerBound
public import Lemmata.Centroid.Def.Bounds
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.IntervalCases

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction

noncomputable section

variable {F : Type*} [Field F]

def diagonal (n : ℕ) : Tensor F (Fin 3) (fun _ => Fin n) :=
  fun x => if x 0 = x 1 ∧ x 1 = x 2 then 1 else 0

theorem diagonal_rankAtMost (n : ℕ) : Tensor.RankAtMost (diagonal (F := F) n) n := by
  refine ⟨fun a _ b => if b = a then 1 else 0, ?_⟩
  ext x
  simp only [Tensor.simple, Finset.sum_apply, Fin.prod_univ_three, Lemmata.TensorRank.Tensor.pure]
  rw [Finset.sum_eq_single (x 0)]
  · by_cases h1 : x 0 = x 1 <;> by_cases h2 : x 1 = x 2 <;>
      simp_all [diagonal, eq_comm]
  · intro a ha hax
    simp [Ne.symm hax]
  · simp

theorem diagonal_concise (n : ℕ) : Tensor.Concise (diagonal (F := F) n) := by
  apply Tensor.concise_of_identity_minors _ (fun _ a _ => a)
  intro i
  ext a b
  fin_cases i <;> simp [Tensor.flatteningMinor, diagonal, Matrix.one_apply, eq_comm]

theorem diagonal_rationalBorderRank (n : ℕ) :
    Tensor.rationalBorderRank (diagonal (F := F) n) = n := by
  apply le_antisymm
  · exact (Tensor.rationalBorderRank_le_iff _ _).mpr
      (diagonal_rankAtMost n).rationalBorderRankAtMost
  · simpa using (diagonal_concise (F := F) n).le_rationalBorderRank 0

def diagonalCentroid (n : ℕ) : (Fin n → F) →ₗ[F] Tensor.centroid (diagonal (F := F) n) where
  toFun c := ⟨fun _ => Matrix.diagonal c, fun i j => by
    ext x
    have h (k : Fin 3) : Tensor.legAction (diagonal (F := F) n) k (Matrix.diagonal c) x =
        c (x 0) * diagonal n x := by
      simp only [Tensor.legAction_apply, Matrix.diagonal_apply, ite_mul, zero_mul]
      fin_cases k <;> simp [diagonal] <;> split_ifs <;> simp_all
    exact (h i).trans (h j).symm⟩
  map_add' c d := by
    apply Subtype.ext
    funext i a b
    change (Matrix.diagonal (c + d)) a b = (Matrix.diagonal c) a b + (Matrix.diagonal d) a b
    simp only [Matrix.diagonal_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' a c := by
    apply Subtype.ext
    funext i r s
    simp [Matrix.diagonal_apply, smul_eq_mul, mul_ite]

theorem diagonalCentroid_injective (n : ℕ) :
    Function.Injective (diagonalCentroid (F := F) n) := by
  intro c d h
  ext a
  have hh := congrArg (fun A : Tensor.centroid (diagonal (F := F) n) => A.val 0 a a) h
  change (Matrix.diagonal c) a a = (Matrix.diagonal d) a a at hh
  simpa using hh

theorem diagonal_centroid_lower_bound (n : ℕ) :
    n ≤ Module.finrank F (Tensor.centroid (diagonal (F := F) n)) := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_injective (diagonalCentroid_injective (F := F) n)

theorem exists_diagonal_small (N : ℕ) (hN : 2 ≤ N) (hN' : N ≤ 5) :
    ∃ T : Tensor F (Fin 3) (fun _ => Fin N), Tensor.Concise T ∧
      Tensor.rationalBorderRank T = N ∧ generalBound N ≤ Module.finrank F (Tensor.centroid T) := by
  refine ⟨diagonal N, diagonal_concise N, diagonal_rationalBorderRank N, ?_⟩
  have hbound : generalBound N = N := by interval_cases N <;> decide
  rw [hbound]
  exact diagonal_centroid_lower_bound N

end

end Lemmata.Centroid.Construction
