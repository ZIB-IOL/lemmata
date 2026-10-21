module

public import Lemmata.TensorRank.Proof.Asymptotic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology

namespace Lemmata.TensorRank

theorem tendsto_polynomial_root (C : ℝ) (hC : 0 < C) (d : ℕ) :
    Tendsto (fun n : ℕ => (C * ((n : ℝ) + 1) ^ d) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hc : Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).rpow
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) (Or.inl (ne_of_gt hC))
  have hn : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := (tendsto_rpow_div_mul_add 1 1 (-1) zero_ne_one).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, one_mul, add_neg_cancel_right, one_div] using h
  have h := hc.mul (hn.pow d)
  have hp : Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹) *
      (((n : ℝ) + 1) ^ ((n : ℝ)⁻¹)) ^ d) atTop (𝓝 1) := by simpa using h
  apply hp.congr
  intro n
  rw [Real.mul_rpow hC.le (pow_nonneg (by positivity) d),
    ← Real.rpow_pow_comm (by positivity : 0 ≤ (n : ℝ) + 1)]

namespace Tensor

universe u v w z

variable {R : Type u} [CommSemiring R] [Nontrivial R] [NoZeroDivisors R]
variable {I : Type v} [Fintype I] {V : I → Type w} [∀ i, Fintype (V i)]

theorem asymptoticRank_le_of_polynomial_power_bound (T : Tensor R I V)
    (C b : ℝ) (hC : 0 < C) (hb : 0 ≤ b) (d : ℕ)
    (h : ∀ n : ℕ, 0 < n → (rank (power T n) : ℝ) ≤ C * ((n : ℝ) + 1) ^ d * b ^ n) :
    asymptoticRank T ≤ b := by
  have hl := (tendsto_polynomial_root C hC d).mul_const b
  have hle : asymptoticRank T ≤ 1 * b := by
    apply le_of_tendsto_of_tendsto (tendsto_power_rank_root T) hl
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    calc
      (rank (power T n) : ℝ) ^ ((n : ℝ)⁻¹) ≤
          (C * ((n : ℝ) + 1) ^ d * b ^ n) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (h n hn) (by positivity)
      _ = (C * ((n : ℝ) + 1) ^ d) ^ ((n : ℝ)⁻¹) * b := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg hb n),
          Real.pow_rpow_inv_natCast hb (Nat.ne_of_gt hn)]
  simpa using hle

variable {W : I → Type z} [∀ i, Fintype (W i)]

theorem asymptoticRank_le_of_polynomial_rank_power (S : Tensor R I W) (T : Tensor R I V)
    (C : ℝ) (hC : 0 < C) (d : ℕ)
    (h : ∀ n : ℕ, 0 < n → (rank (power S n) : ℝ) ≤
      C * ((n : ℝ) + 1) ^ d * (rank (power T n) : ℝ)) :
    asymptoticRank S ≤ asymptoticRank T := by
  have hl := (tendsto_polynomial_root C hC d).mul (tendsto_power_rank_root T)
  have hle : asymptoticRank S ≤ 1 * asymptoticRank T := by
    apply le_of_tendsto_of_tendsto (tendsto_power_rank_root S) hl
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    calc
      (rank (power S n) : ℝ) ^ ((n : ℝ)⁻¹) ≤
          (C * ((n : ℝ) + 1) ^ d * (rank (power T n) : ℝ)) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (h n hn) (by positivity)
      _ = (C * ((n : ℝ) + 1) ^ d) ^ ((n : ℝ)⁻¹) *
          (rank (power T n) : ℝ) ^ ((n : ℝ)⁻¹) :=
        Real.mul_rpow (by positivity) (Nat.cast_nonneg _)
  simpa using hle

theorem asymptoticRank_le_of_linear_rank_power (S : Tensor R I W) (T : Tensor R I V)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ n : ℕ, 0 < n → (rank (power S n) : ℝ) ≤
      (C * n + D) * (rank (power T n) : ℝ)) : asymptoticRank S ≤ asymptoticRank T := by
  apply asymptoticRank_le_of_polynomial_rank_power S T (C + D + 1) (by positivity) 1
  intro n hn
  apply (h n hn).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [pow_one]
  nlinarith [Nat.cast_nonneg (α := ℝ) n, mul_nonneg hD (Nat.cast_nonneg (α := ℝ) n)]

end Tensor
end Lemmata.TensorRank
