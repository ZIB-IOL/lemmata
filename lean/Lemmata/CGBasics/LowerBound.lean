module

public import Lemmata.CGBasics.Statement
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# A primal gap lower bound (Example 2.7)

The coordinates of a convex combination of `e_i, i ∈ S`, sum to `1` on `S` and vanish outside, so
by Cauchy–Schwarz `‖x‖² ≥ 1/|S|`. The barycenter of the simplex has `‖·‖² = 1/n`.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

namespace Proof

theorem simplex_lower_bound : SimplexLowerBound := by
  intro n S hS xStar hxs x hx
  classical
  set K : Set (EuclideanSpace ℝ (Fin n)) := {y | ∑ i ∈ S, y i = 1 ∧ ∀ i ∉ S, y i = 0} with hK
  have hKconv : Convex ℝ K := by
    intro a ha b hb s t hs ht hst
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ha.1, hb.1]
      linarith
    · simp [ha.2 i hi, hb.2 i hi]
  have hsub : (fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) '' (S : Set (Fin n)) ⊆ K := by
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨?_, fun i hi => ?_⟩
    · simp
      exact_mod_cast hj
    · have : i ≠ j := fun e => hi (e ▸ hj)
      simp [this]
  have hxK := convexHull_min hsub hKconv hx
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ 2 = ∑ i, y i ^ 2 := fun y => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs, sq_abs]
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hS1 : (1 : ℝ) / S.card ≤ ∑ i ∈ S, x i ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => x i)
    rw [hxK.1] at hcs
    rw [div_le_iff₀ hcard]
    simp only [one_pow] at hcs
    linarith
  have hsum_le : ∑ i ∈ S, x i ^ 2 ≤ ∑ i, x i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => sq_nonneg _)
  have hn : (0 : ℝ) < n := by
    obtain ⟨i, _⟩ := hS
    have : 0 < n := Fin.pos i
    exact_mod_cast this
  set c : EuclideanSpace ℝ (Fin n) := ∑ i, (1 / n : ℝ) • EuclideanSpace.single i (1 : ℝ) with hc
  have hc_mem : c ∈ convexHull ℝ (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) := by
    refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_
      (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hci : ∀ i, c i = 1 / n := by
    intro i
    simp [hc]
    rw [← Finset.mul_sum]
    simp [Pi.single_apply]
  have hc_norm : ‖c‖ ^ 2 = 1 / n := by
    rw [hnorm]
    simp only [hci, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hmin := hxs.2 c hc_mem
  simp only at hmin
  rw [hnorm x]
  linarith

end Proof

end Lemmata.CGBasics
