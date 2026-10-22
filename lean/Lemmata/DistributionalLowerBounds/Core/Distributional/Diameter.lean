module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.HardFamily
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact diameter of the permuted hard set

This module formalizes equation `eq:diameter` of the manuscript.
-/

open Set

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Euclidean norm is bounded by the coordinate ℓ₁ norm. -/
lemma euclidean_norm_le_sum_abs {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hsum0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hsum0).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg (x i))

lemma hardWeight_ge_first {d : ℕ} (i : Fin d) :
    hardC d * Real.sqrt 2 ≤ hardWeight d i := by
  dsimp [hardWeight]
  apply mul_le_mul_of_nonneg_left _ (hardC_pos d).le
  apply Real.sqrt_le_sqrt
  have hi : (1 : ℝ) ≤ i.val + 1 := by norm_num
  nlinarith

/-- Radius appearing in the diameter formula. -/
noncomputable def hardRadius (d : ℕ) : ℝ := hardC d * (2 - Real.sqrt 2)

lemma hardRadius_pos (d : ℕ) : 0 < hardRadius d := by
  dsimp [hardRadius]
  have hs : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_pos (hardC_pos d) (sub_pos.mpr hs)

lemma radial_quadratic_bound {C r : ℝ} (hC : 0 < C) (hr : 0 ≤ r)
    (h : (1 / 2 : ℝ) * r ^ 2 + C * Real.sqrt 2 * r ≤ C ^ 2) :
    r ≤ C * (2 - Real.sqrt 2) := by
  let R := C * (2 - Real.sqrt 2)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslt : Real.sqrt 2 < 2 := by nlinarith
  have hR : 0 < R := by
    dsimp [R]
    exact mul_pos hC (sub_pos.mpr hslt)
  have hroot : (1 / 2 : ℝ) * R ^ 2 + C * Real.sqrt 2 * R = C ^ 2 := by
    dsimp [R]
    nlinarith
  by_contra hnot
  have hrR : R < r := lt_of_not_ge hnot
  have hfactor : 0 < (r - R) * ((1 / 2 : ℝ) * (r + R) + C * Real.sqrt 2) := by
    apply mul_pos (sub_pos.mpr hrR)
    positivity
  have : C ^ 2 < (1 / 2 : ℝ) * r ^ 2 + C * Real.sqrt 2 * r := by
    nlinarith
  linarith

lemma concreteHardSet_norm_le_radius {d : ℕ} (π : Equiv.Perm (Fin d))
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ weightedHardSet (hardC d) (permutedHardWeight d π)) :
    ‖x‖ ≤ hardRadius d := by
  change (1 / 2 : ℝ) * ‖x‖ ^ 2 +
      ∑ i, permutedHardWeight d π i * |x i| ≤ hardC d ^ 2 at hx
  have hweighted : hardC d * Real.sqrt 2 * ∑ i, |x i| ≤
      ∑ i, permutedHardWeight d π i * |x i| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hardWeight_ge_first (π i)) (abs_nonneg _))
  have hl1 := euclidean_norm_le_sum_abs x
  have hcoeff : 0 ≤ hardC d * Real.sqrt 2 :=
    mul_nonneg (hardC_pos d).le (Real.sqrt_nonneg _)
  have hradial : (1 / 2 : ℝ) * ‖x‖ ^ 2 +
      hardC d * Real.sqrt 2 * ‖x‖ ≤ hardC d ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl1 hcoeff]
  exact radial_quadratic_bound (hardC_pos d) (norm_nonneg _) hradial

/-- Upper diameter bound. -/
lemma concreteHardSet_diam_le {d : ℕ} (π : Equiv.Perm (Fin d)) :
    Metric.diam (weightedHardSet (hardC d) (permutedHardWeight d π)) ≤
      2 * hardRadius d := by
  apply Metric.diam_le_of_subset_closedBall (hardRadius_pos d).le
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact concreteHardSet_norm_le_radius π hx

/-- A coordinate carrying the smallest weight. -/
noncomputable def minWeightCoordinate {d : ℕ} (π : Equiv.Perm (Fin d))
    (hd : 0 < d) : Fin d :=
  π.symm ⟨0, hd⟩

lemma minWeightCoordinate_rank_zero {d : ℕ} (π : Equiv.Perm (Fin d))
    (hd : 0 < d) : π (minWeightCoordinate π hd) = ⟨0, hd⟩ := by
  simp [minWeightCoordinate]

/-- The two antipodal radius points are feasible. -/
lemma hardRadius_single_mem {d : ℕ} (π : Equiv.Perm (Fin d)) (hd : 0 < d)
    (sgn : ℝ) (hsgn : |sgn| = 1) :
    EuclideanSpace.single (minWeightCoordinate π hd) (sgn * hardRadius d) ∈
      weightedHardSet (hardC d) (permutedHardWeight d π) := by
  let i := minWeightCoordinate π hd
  let x : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i (sgn * hardRadius d)
  change (1 / 2 : ℝ) * ‖x‖ ^ 2 +
      ∑ j, permutedHardWeight d π j * |x j| ≤ hardC d ^ 2
  have hnorm : ‖x‖ = hardRadius d := by
    dsimp [x]
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_mul, hsgn, one_mul,
      abs_of_pos (hardRadius_pos d)]
  have hsum : (∑ j, permutedHardWeight d π j * |x j|) =
      hardC d * Real.sqrt 2 * hardRadius d := by
    classical
    rw [Finset.sum_eq_single i]
    · have hpi : π i = ⟨0, hd⟩ := by
        dsimp [i]
        exact minWeightCoordinate_rank_zero π hd
      rw [show permutedHardWeight d π i = hardC d * Real.sqrt 2 by
        dsimp [permutedHardWeight, hardWeight]
        rw [hpi]
        norm_num]
      simp [x, hsgn, abs_of_pos (hardRadius_pos d)]
    · intro j _ hji
      simp [x, hji]
    · simp
  rw [hnorm, hsum]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [hardRadius]
  nlinarith

/-- Paper-facing exact diameter endpoint. -/
theorem concreteHardSet_diameter {d : ℕ} (π : Equiv.Perm (Fin d)) (hd : 0 < d) :
    Metric.diam (weightedHardSet (hardC d) (permutedHardWeight d π)) =
      2 * hardC d * (2 - Real.sqrt 2) := by
  have hu := concreteHardSet_diam_le π
  have hp := hardRadius_single_mem π hd 1 (by norm_num)
  have hm := hardRadius_single_mem π hd (-1) (by norm_num)
  have hbdd : Bornology.IsBounded
      (weightedHardSet (hardC d) (permutedHardWeight d π)) := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * hardRadius d, ?_⟩
    intro x hx y hy
    calc
      dist x y ≤ ‖x‖ + ‖y‖ := by simpa [dist_eq_norm] using norm_sub_le x y
      _ ≤ 2 * hardRadius d := by
        linarith [concreteHardSet_norm_le_radius π hx,
          concreteHardSet_norm_le_radius π hy]
  have hlower := Metric.dist_le_diam_of_mem hbdd hp hm
  have hdist :
      dist (EuclideanSpace.single (minWeightCoordinate π hd) (1 * hardRadius d))
        (EuclideanSpace.single (minWeightCoordinate π hd) (-1 * hardRadius d)) =
        2 * hardRadius d := by
    rw [dist_eq_norm, ← PiLp.single_sub, PiLp.norm_single,
      Real.norm_eq_abs]
    rw [show (1 : ℝ) * hardRadius d - -1 * hardRadius d = 2 * hardRadius d by ring,
      abs_of_pos (mul_pos (by norm_num) (hardRadius_pos d))]
  rw [hdist] at hlower
  dsimp [hardRadius] at hu hlower ⊢
  nlinarith

end Lemmata.DistributionalLowerBounds.Core.Distributional
