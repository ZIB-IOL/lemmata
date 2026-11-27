module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Optimizing the dimension-dependent bound of Grimmer and Liu

Grimmer and Liu's lower bound for smooth sets (their Theorem 4.1) is the square of the positive
part of an expression `A_d` in the dimension `d`, for `d > T > 0` calls, `δ = D - 2/β`. However
the dimension is chosen, `A_d ≤ β δ² / (4 √2 T)`: at fixed parameters their bound is at most of
order `1/T²`, while the bound of this entry is of order `1/T`.
-/

namespace Lemmata.FrankWolfePS

/-- The expression `A_d` inside Grimmer and Liu's dimension-dependent bound. -/
noncomputable def glExpression (β δ d T : ℝ) : ℝ :=
  δ / (2 * Real.sqrt d) * Real.sqrt (1 - T / d) - (1 - Real.sqrt (1 - T / d)) / (Real.sqrt 2 * β)

/-- Whatever the dimension, `A_d ≤ β δ² / (4 √2 T)`. -/
theorem glExpression_le {β δ d T : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hT : 0 < T) (hd : T < d) :
    glExpression β δ d T ≤ β * δ ^ 2 / (4 * Real.sqrt 2 * T) := by
  have d0 : 0 < d := hT.trans hd
  set w := Real.sqrt 2 with hw
  have w0 : 0 < w := by positivity
  have w2 : w ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set q := Real.sqrt d with hq
  have q0 : 0 < q := Real.sqrt_pos.mpr d0
  have q2 : q ^ 2 = d := Real.sq_sqrt d0.le
  set s := Real.sqrt (1 - T / d) with hs
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have hTd : T / d < 1 := (div_lt_one d0).mpr hd
  have s2 : s ^ 2 = 1 - T / d := Real.sq_sqrt (by linarith)
  have hTd0 : 0 < T / d := div_pos hT d0
  have s1 : s ≤ 1 := by
    rw [hs]
    calc Real.sqrt (1 - T / d) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  -- 1 - s ≥ T / (2d), and δ s ≤ δ
  have h1 : T / (2 * d) ≤ 1 - s := by
    have hprod : (1 - s) * (1 + s) = T / d := by
      rw [show (1 - s) * (1 + s) = 1 - s ^ 2 by ring, s2]; ring
    have hs1 : 0 ≤ 1 - s := by linarith
    have hle : T / d ≤ (1 - s) * 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (show 1 + s ≤ 2 by linarith) hs1]
    rw [div_le_iff₀ (by positivity)]
    have hT' : T = T / d * d := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hle d0.le]
  have h2 : δ / (2 * q) * s ≤ δ / (2 * q) := by
    have := div_nonneg hδ (by positivity : (0 : ℝ) ≤ 2 * q)
    nlinarith
  have h3 : (1 - s) / (w * β) ≥ T / (2 * d) / (w * β) :=
    div_le_div_of_nonneg_right h1 (by positivity)
  have key : δ / (2 * q) - T / (2 * d) / (w * β) ≤ β * δ ^ 2 / (4 * w * T) := by
    rw [← q2]
    have poly : 2 * δ * w * T * q * β - w ^ 2 * T ^ 2 ≤ β ^ 2 * δ ^ 2 * q ^ 2 := by
      nlinarith [sq_nonneg (β * δ * q - w * T)]
    rw [w2] at poly
    rw [show δ / (2 * q) - T / (2 * q ^ 2) / (w * β) =
        (2 * δ * w * T * q * β - 2 * T ^ 2) / (4 * w * T * q ^ 2 * β) by field_simp; ring,
      show β * δ ^ 2 / (4 * w * T) = β ^ 2 * δ ^ 2 * q ^ 2 / (4 * w * T * q ^ 2 * β) by
        field_simp]
    exact div_le_div_of_nonneg_right poly (by positivity)
  unfold glExpression
  rw [← hw, ← hq, ← hs]
  linarith

end Lemmata.FrankWolfePS
