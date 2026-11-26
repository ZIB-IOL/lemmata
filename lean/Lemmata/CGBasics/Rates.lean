module

public import Lemmata.CGBasics.Statement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# From contractions to convergence rates (Lemmas 2.22 and 2.23)

For the power case, `u_t = h_t^{-α}` grows by at least `α c₂` per step: with
`s = 1 - c₂ h_t^α ∈ (0, 1]`, `h_{t+1} ≤ h_t s` and
`s^{-α} = exp(-α log s) ≥ 1 - α log s ≥ 1 + α (1 - s)`.
-/

namespace Lemmata.CGBasics

namespace Proof

theorem contraction_linear : ContractionLinear := by
  intro h c₀ c₁ hnn hc1 hc1' h1 hrec t ht
  induction t, ht using Nat.le_induction with
  | base => simpa using h1
  | succ t ht ih =>
    have := hrec t ht
    have hc : 0 ≤ 1 - c₁ := by linarith
    calc h (t + 1) ≤ (1 - c₁) * h t := by linarith
      _ ≤ (1 - c₁) * (c₀ * (1 - c₁) ^ (t - 1)) := mul_le_mul_of_nonneg_left ih hc
      _ = c₀ * (1 - c₁) ^ (t + 1 - 1) := by
        rw [show t + 1 - 1 = (t - 1) + 1 by omega, pow_succ]; ring

theorem contraction_power : ContractionPower := by
  intro h c₀ c₂ α hpos hc₀ hc₂ hα h1 hrec t ht
  have hstep : ∀ t, 1 ≤ t → h t ^ (-α) + α * c₂ ≤ h (t + 1) ^ (-α) := by
    intro t ht
    have hr := hrec t ht
    have ha := hpos t
    have hb := hpos (t + 1)
    set a := h t with ha_def
    have hapow : 0 < a ^ α := Real.rpow_pos_of_pos ha α
    have e1 : a ^ (1 + α) = a * a ^ α := by rw [Real.rpow_add ha, Real.rpow_one]
    rw [e1] at hr
    set s := 1 - c₂ * a ^ α with hs
    have has : a * s = a - c₂ * (a * a ^ α) := by rw [hs]; ring
    have hle : h (t + 1) ≤ a * s := by linarith
    have hs_pos : 0 < s := by
      by_contra hns
      push Not at hns
      have : a * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hns
      linarith
    have h2 : (a * s) ^ (-α) ≤ h (t + 1) ^ (-α) := Real.rpow_le_rpow_of_nonpos hb hle (by linarith)
    rw [Real.mul_rpow ha.le hs_pos.le] at h2
    have hbern : 1 + α * (1 - s) ≤ s ^ (-α) := by
      rw [Real.rpow_def_of_pos hs_pos]
      have h3 := Real.add_one_le_exp (Real.log s * (-α))
      have h4 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hs_pos) hα.le
      nlinarith
    have hapn : 0 < a ^ (-α) := Real.rpow_pos_of_pos ha _
    have e2 : a ^ (-α) * a ^ α = 1 := by rw [← Real.rpow_add ha]; simp
    have e3 : a ^ (-α) * (1 + α * (1 - s)) = a ^ (-α) + α * c₂ := by
      have e4 : 1 - s = c₂ * a ^ α := by rw [hs]; ring
      rw [e4]
      calc a ^ (-α) * (1 + α * (c₂ * a ^ α)) = a ^ (-α) + α * c₂ * (a ^ (-α) * a ^ α) := by ring
        _ = a ^ (-α) + α * c₂ := by rw [e2, mul_one]
    have := mul_le_mul_of_nonneg_left hbern hapn.le
    linarith
  have hu : ∀ t : ℕ, 1 ≤ t → h 1 ^ (-α) + α * c₂ * ((t : ℝ) - 1) ≤ h t ^ (-α) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      have := hstep t ht
      push_cast
      linarith
  have hu1 : c₀ ^ (-α) ≤ h 1 ^ (-α) := Real.rpow_le_rpow_of_nonpos (hpos 1) h1 (by linarith)
  have ht1 : (0 : ℝ) ≤ (t : ℝ) - 1 := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hc₀α : 0 < c₀ ^ α := Real.rpow_pos_of_pos hc₀ α
  set B := c₀ ^ (-α) + α * c₂ * ((t : ℝ) - 1) with hB
  have hBpos : 0 < B := by
    have := Real.rpow_pos_of_pos hc₀ (-α)
    have := mul_nonneg (mul_nonneg hα.le hc₂.le) ht1
    linarith
  have hBle : B ≤ h t ^ (-α) := by linarith [hu t ht]
  have hht : h t = (h t ^ (-α)) ^ (-1 / α) := by
    rw [← Real.rpow_mul (hpos t).le]
    have : -α * (-1 / α) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hmono : (h t ^ (-α)) ^ (-1 / α) ≤ B ^ (-1 / α) :=
    Real.rpow_le_rpow_of_nonpos hBpos hBle (by
      have : 0 < 1 / α := by positivity
      linarith [show -1 / α = -(1 / α) by ring])
  have hX : 0 < 1 + c₂ * c₀ ^ α * α * ((t : ℝ) - 1) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hc₂.le hc₀α.le) hα.le) ht1
    linarith
  have hB' : B = c₀ ^ (-α) * (1 + c₂ * c₀ ^ α * α * ((t : ℝ) - 1)) := by
    have e : c₀ ^ (-α) * c₀ ^ α = 1 := by rw [← Real.rpow_add hc₀]; simp
    calc B = c₀ ^ (-α) + α * c₂ * ((t : ℝ) - 1) * (c₀ ^ (-α) * c₀ ^ α) := by
          rw [e, mul_one]
      _ = c₀ ^ (-α) * (1 + c₂ * c₀ ^ α * α * ((t : ℝ) - 1)) := by ring
  have hfin : B ^ (-1 / α) = c₀ / (1 + c₂ * c₀ ^ α * α * ((t : ℝ) - 1)) ^ (1 / α) := by
    rw [hB', Real.mul_rpow (Real.rpow_pos_of_pos hc₀ _).le hX.le, ← Real.rpow_mul hc₀.le]
    have e1 : -α * (-1 / α) = 1 := by field_simp
    rw [e1, Real.rpow_one, show (-1 / α) = -(1 / α) by ring, Real.rpow_neg hX.le]
    ring
  calc h t = (h t ^ (-α)) ^ (-1 / α) := hht
    _ ≤ B ^ (-1 / α) := hmono
    _ = c₀ / (1 + c₂ * c₀ ^ α * α * ((t : ℝ) - 1)) ^ (1 / α) := hfin

end Proof

end Lemmata.CGBasics
