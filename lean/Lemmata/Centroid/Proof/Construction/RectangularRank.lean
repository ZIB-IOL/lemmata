module

public import Lemmata.Centroid.Proof.Construction.RectangularFrames

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Rectangular

noncomputable section

variable {F : Type*} [Field F]

theorem diagonal_sum (n t : ℕ) (r : Option (Fin n)) :
    (∑ j, lambda (F := F) n t j r • Tensor.simple (diagonalPoint (F := F) n t (j, r))) =
      Tensor.simple (factors n t (fun _ => (1 : RatFunc F))
        (Realization.basisVector (Sum.inl none)) (Realization.basisVector (Sum.inl r))) := by
  ext x
  have h := congrFun (gridPoint_lambda (F := F) n t r) (x 0)
  erw [Finset.sum_apply, Pi.one_apply] at h
  change (∑ j, lambda (F := F) n t j r * gridPoint (F := F) n t j r (x 0)) = 1 at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Tensor.simple, Fin.prod_univ_three,
    diagonalPoint, factors_zero, factors_one, factors_two, one_mul,
    Lemmata.TensorRank.Tensor.pure]
  calc
    _ = (∑ j, lambda (F := F) n t j r * gridPoint (F := F) n t j r (x 0)) *
        Realization.basisVector (Sum.inl none) (x 1) *
        Realization.basisVector (Sum.inl r) (x 2) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [h, one_mul]

theorem basePoint_sum (n t : ℕ) (ht : t ≤ n) :
    (∑ p, Tensor.simple (basePoint (F := F) n t ht p)) =
      ∑ p, Tensor.simple (gridTensorPoint (F := F) n t p) := by
  have hd : (∑ p : Fin n × Option (Fin n), splitScalar (F := F) n t ht p.1 p.2 •
      Tensor.simple (diagonalPoint (F := F) n t p)) =
      ∑ k, Tensor.simple (extraPoint (F := F) n t ht k) := by
    simp only [Fintype.sum_prod_type]
    have hs (j : Fin n) := sum_splitScalar (F := F) n t ht j (fun _ => 1)
      (fun r => Tensor.simple (diagonalPoint (F := F) n t (j, r)))
    simp only [one_mul] at hs
    simp_rw [hs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    exact diagonal_sum (F := F) n t (selected ht k)
  simp only [Fintype.sum_sum_type, basePoint, Sum.elim_inl, Sum.elim_inr]
  simp_rw [oldPoint_simple]
  rw [Finset.sum_sub_distrib, hd, sub_add_cancel]

theorem gridTensor_sum (n t : ℕ) :
    (∑ p, Tensor.simple (gridTensorPoint (F := F) n t p)) =
      ∑ a, Tensor.simple (lowRankPoint (F := F) n t a) := by
  ext x
  rcases h1 : x 1 with (_ | b) | b <;> cases h2 : x 2 <;>
    simp [Finset.sum_apply, Tensor.simple, Fin.prod_univ_three, gridTensorPoint, lowRankPoint,
      factors_zero, factors_one, factors_two, h1, h2, Realization.basisVector,
      Fintype.sum_prod_type, Option.elim, gridPoint, mul_ite, ite_mul, eq_comm]
  let : DecidableEq (Fin n) := fun _ _ => Classical.propDecidable _
  exact (Fintype.sum_ite_eq (x 0)
    (fun c => M (F := F) n c b * H (F := F) n t c _)).symm

theorem basePoint_rankAtMost (n t : ℕ) (ht : t ≤ n) :
    Tensor.RankAtMost (∑ p, Tensor.simple (basePoint (F := F) n t ht p)) n := by
  refine ⟨lowRankPoint (F := F) n t, ?_⟩
  rw [basePoint_sum, gridTensor_sum]

end

end Lemmata.Centroid.Construction.Rectangular
