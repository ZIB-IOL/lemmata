module

public import Lemmata.TensorRank.Proof.Growth

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology

namespace Lemmata.TensorRank

theorem le_of_polynomial_power_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (C : ℝ) (hC : 0 < C) (d : ℕ)
    (h : ∀ n : ℕ, 0 < n → x ^ n ≤ C * ((n : ℝ) + 1) ^ d * y ^ n) : x ≤ y := by
  have ht := (tendsto_polynomial_root C hC d).mul_const y
  have hh : x ≤ 1 * y := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    calc
      x = (x ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hx hn.ne').symm
      _ ≤ (C * ((n : ℝ) + 1) ^ d * y ^ n) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg hx n) (h n hn) (by positivity)
      _ = (C * ((n : ℝ) + 1) ^ d) ^ ((n : ℝ)⁻¹) * y := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg hy n),
          Real.pow_rpow_inv_natCast hy hn.ne']
  simpa only [one_mul] using hh

end Lemmata.TensorRank
