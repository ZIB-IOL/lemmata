module

public import Lemmata.Centroid.Proof.General.AverageBound
public import Lemmata.Centroid.Proof.General.BalancedAlgebra
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Lemmata.Centroid.General

theorem geometric_mean3_le_average {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x * y * z) ^ (1 / 3 : ℝ) ≤ (x + y + z) / 3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (show (0 : ℝ) ≤ 1 / 3 by norm_num) (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    (show (0 : ℝ) ≤ 1 / 3 by norm_num) hx hy hz (by norm_num)
  rw [Real.mul_rpow (mul_nonneg hx hy) hz, Real.mul_rpow hx hy]
  nlinarith

theorem root_three_pow {r : ℝ} (hr : 0 ≤ r) : (r ^ (1 / 3 : ℝ)) ^ 3 = r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  norm_num

theorem root_three_square {r : ℝ} (hr : 0 ≤ r) :
    (r ^ (1 / 3 : ℝ)) ^ 2 = r ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  norm_num

theorem supportCost_le_u_add_div {r u : ℝ} (hr : 1 ≤ r) (hu : r ^ (2 / 3 : ℝ) ≤ u) :
    supportCost r ≤ u + r / u := by
  let z := r ^ (1 / 3 : ℝ)
  have hr0 : 0 ≤ r := by linarith
  have hz1 : 1 ≤ z := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hr
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    simpa only [Real.one_rpow] using h
  have hz3 : z ^ 3 = r := root_three_pow hr0
  have hz2 : z ^ 2 = r ^ (2 / 3 : ℝ) := root_three_square hr0
  have huz : z ≤ u := by nlinarith
  have hu0 : 0 < u := by linarith
  have hp : 0 ≤ (u - z ^ 2) * (u - z) := mul_nonneg (by linarith) (by linarith)
  have heq : (u + r / u - (z ^ 2 + z)) * u = u ^ 2 + r - (z ^ 2 + z) * u := by
    field_simp
  change r ^ (2 / 3 : ℝ) + z ≤ u + r / u
  rw [← hz2]
  nlinarith

theorem geometric_mean3_module_bound {r q₁ q₂ q₃ m₁ m₂ m₃ : ℝ} (hr : 0 ≤ r)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hq₃ : 0 < q₃)
    (hm₁ : q₁ + r / q₁ ≤ m₁) (hm₂ : q₂ + r / q₂ ≤ m₂) (hm₃ : q₃ + r / q₃ ≤ m₃) :
    (q₁ * q₂ * q₃) ^ (1 / 3 : ℝ) + r / (q₁ * q₂ * q₃) ^ (1 / 3 : ℝ) ≤
      (m₁ + m₂ + m₃) / 3 := by
  let u := (q₁ * q₂ * q₃) ^ (1 / 3 : ℝ)
  have hq := geometric_mean3_le_average hq₁.le hq₂.le hq₃.le
  have hd := geometric_mean3_le_average (div_nonneg hr hq₁.le)
    (div_nonneg hr hq₂.le) (div_nonneg hr hq₃.le)
  have hdiv : r / q₁ * (r / q₂) * (r / q₃) = r ^ 3 / (q₁ * q₂ * q₃) := by ring
  rw [hdiv, Real.div_rpow (pow_nonneg hr _) (by positivity) (1 / 3 : ℝ),
    ← Real.rpow_natCast, ← Real.rpow_mul hr] at hd
  norm_num at hd
  change u ≤ (q₁ + q₂ + q₃) / 3 at hq
  change r / u ≤ (r / q₁ + r / q₂ + r / q₃) / 3 at hd
  linarith

theorem supportCost_le_average {r q₁ q₂ q₃ m₁ m₂ m₃ : ℝ} (hr : 1 ≤ r)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hq₃ : 0 < q₃)
    (hm₁ : q₁ + r / q₁ ≤ m₁) (hm₂ : q₂ + r / q₂ ≤ m₂) (hm₃ : q₃ + r / q₃ ≤ m₃)
    (hprod : r ^ 2 ≤ q₁ * q₂ * q₃) : supportCost r ≤ (m₁ + m₂ + m₃) / 3 := by
  have hr0 : 0 ≤ r := by linarith
  have hu : r ^ (2 / 3 : ℝ) ≤ (q₁ * q₂ * q₃) ^ (1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (sq_nonneg r) hprod (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0] at h
    norm_num at h
    exact h
  exact (supportCost_le_u_add_div hr hu).trans
    (geometric_mean3_module_bound hr0 hq₁ hq₂ hq₃ hm₁ hm₂ hm₃)

theorem dimension_sum_le_envelope {ι : Type*} [Fintype ι] (d : ι → ℕ) (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hd : ∀ i, dimensionCost (d i) ≤ m i) :
    (∑ i, d i : ℕ) ≤ 1 + envelope (∑ i, m i) := by
  apply dimension_le_envelope (Finset.sum_nonneg (fun i _ => hm i))
  exact (dimensionCost_sum Finset.univ d).trans (Finset.sum_le_sum (fun i _ => hd i))

theorem ideal_dimension_split {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A] (I : Ideal A) :
    Module.finrank F (A ⧸ I) + Module.finrank F I = Module.finrank F A := by
  let q := (Ideal.Quotient.mkₐ F I).toLinearMap
  let : FiniteDimensional F (A ⧸ I) := Module.Finite.of_surjective q Ideal.Quotient.mk_surjective
  have hk : q.ker = I.restrictScalars F := by
    ext a
    simp [q, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have h := LinearMap.finrank_range_add_finrank_ker q
  rw [LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective, finrank_top, hk] at h
  exact h

end Lemmata.Centroid.General
