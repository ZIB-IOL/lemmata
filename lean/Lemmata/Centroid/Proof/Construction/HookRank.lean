module

public import Lemmata.Centroid.Proof.Construction.HookFrames

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Construction.Hook

noncomputable section

variable {F : Type*} [Field F]

def rowGridPoint (n t : ℕ) (p : Option (Fin n) × Fin n) : ∀ i, Core n i → RatFunc F :=
  factors n (liftCore (gridPoint (F := F) n t p.1 p.2))
    (Realization.basisVector p.1) (Realization.basisVector none)

def rowTensorPoint (n t : ℕ) (j : Option (Fin n)) : ∀ i, Core n i → RatFunc F :=
  factors n (liftCore (g (F := F) n t j)) (Realization.basisVector j) (Realization.basisVector none)

theorem sum_rowGridPoint (n t : ℕ) (j : Option (Fin n)) :
    (∑ k, Tensor.simple (rowGridPoint (F := F) n t (j, k))) = Tensor.simple (rowTensorPoint n t j) := by
  ext x
  simp only [Finset.sum_apply, Tensor.simple, Fin.prod_univ_three, rowGridPoint,
    rowTensorPoint, factors_zero, factors_one, factors_two,
    Lemmata.TensorRank.Tensor.pure]
  let a : Option (Fin n) := x 0
  let b : Option (Fin n) := x 1
  let c : Option (Fin n) := x 2
  change (∑ k, liftCore (gridPoint (F := F) n t j k) a * Realization.basisVector j b *
      Realization.basisVector none c) =
    liftCore (g (F := F) n t j) a * Realization.basisVector j b * Realization.basisVector none c
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 2
  cases a with
  | none => simp [liftCore]
  | some a =>
    have h := congrFun (sum_grid_row (F := F) n t j) a
    erw [Finset.sum_apply] at h
    exact h

theorem splitGridPoint_simple (n t : ℕ) (ht : t ≤ n) (p : Option (Fin n) × Fin n) :
    Tensor.simple (splitGridPoint (F := F) n t ht p) = Tensor.simple (gridTensorPoint (F := F) n t p) -
      if SelectedRow ht p.1 then Tensor.simple (rowGridPoint (F := F) n t p) else 0 := by
  ext x
  by_cases hs : SelectedRow ht p.1
  · simp only [Tensor.simple, Fin.prod_univ_three, splitGridPoint, gridTensorPoint, rowGridPoint,
      factors_zero, factors_one, factors_two, splitC, hs, ite_true, Pi.sub_apply,
      Lemmata.TensorRank.Tensor.pure]
    let a := liftCore (gridPoint (F := F) n t p.1 p.2) (x 0)
    let b := Realization.basisVector (F := RatFunc F) p.1 (x 1)
    let c := Realization.basisVector (F := RatFunc F) (some p.2) (x 2)
    let d := Realization.basisVector (F := RatFunc F) none (x 2)
    change a * b * (c - d) = a * b * c - a * b * d
    ring
  · simp only [Tensor.simple, Fin.prod_univ_three, splitGridPoint, gridTensorPoint,
      factors_zero, factors_one, factors_two, splitC, hs, ite_false, sub_zero,
      Lemmata.TensorRank.Tensor.pure]

theorem splitGrid_sum (n t : ℕ) (ht : t ≤ n) :
    (∑ p, Tensor.simple (splitGridPoint (F := F) n t ht p)) =
      (∑ p, Tensor.simple (gridTensorPoint (F := F) n t p)) -
        ∑ r, Tensor.simple (rowPoint (F := F) n t ht r) := by
  simp_rw [splitGridPoint_simple]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  have hs (j : Option (Fin n)) :
      (∑ k, if SelectedRow ht j then Tensor.simple (rowGridPoint (F := F) n t (j, k)) else 0) =
        if SelectedRow ht j then Tensor.simple (rowTensorPoint (F := F) n t j) else 0 := by
    by_cases hj : SelectedRow ht j
    · simp only [hj, ite_true, sum_rowGridPoint]
    · simp only [hj, ite_false, Finset.sum_const_zero]
  simp_rw [hs]
  exact selected_sum n t ht _

theorem corner_sum (n t : ℕ) (ht : t ≤ n) :
    (∑ p : Option (Fin n) × Fin n, (rowEta (F := F) n t ht p.1 * columnNu (F := F) n t ht p.2) •
      Tensor.simple (cornerGridPoint (F := F) n t ht p)) = Tensor.simple (cornerPoint n t ht) := by
  rw [Fintype.sum_prod_type]
  simp only [mul_smul]
  simp_rw [← Finset.smul_sum]
  rw [sum_rowEta]
  simp_rw [sum_columnNu]
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Tensor.simple, Fin.prod_univ_three,
    cornerGridPoint, cornerPoint, factors_zero, factors_one, factors_two, splitC_selected,
    cornerB, cornerC,
    Lemmata.TensorRank.Tensor.pure]
  calc
    _ = ∑ r : Fin t,
        (Realization.basisVector (F := RatFunc F) none (x 0) *
          (eta (F := F) t r * Realization.basisVector (some (r.castLE ht)) (x 1))) *
            (∑ k : Fin t, eta (F := F) t k * fVector (F := F) n (k.castLE ht) (x 2)) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem basePoint_sum (n t : ℕ) (ht : t ≤ n) :
    (∑ p, Tensor.simple (basePoint (F := F) n t ht p)) =
      ∑ p, Tensor.simple (gridTensorPoint (F := F) n t p) := by
  simp only [Fintype.sum_sum_type, basePoint, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique]
  simp_rw [oldPoint_simple]
  rw [Finset.sum_sub_distrib, corner_sum, splitGrid_sum]
  abel

theorem basePoint_rankAtMost (n t : ℕ) (ht : t ≤ n) :
    Tensor.RankAtMost (∑ p, Tensor.simple (basePoint (F := F) n t ht p)) n := by
  refine ⟨lowRankPoint (F := F) n t, ?_⟩
  rw [basePoint_sum, grid_sum]

end

end Lemmata.Centroid.Construction.Hook
