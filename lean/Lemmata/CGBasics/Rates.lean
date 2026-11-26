module

public import Lemmata.CGBasics.Statement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

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

theorem contraction_mixed : ContractionMixed := by
  intro h c₀ c₁ c₂ α hpos hc₀ hc₁ hc₁' hc₂ hα h1 hrec
  set τ := (c₁ / c₂) ^ (1 / α) with hτ
  set ℓ := Real.logb (1 - c₁) (τ / c₀) with hℓ
  set T : ℤ := max (⌊ℓ⌋ + 2) 1 with hT
  have hb0 : 0 < 1 - c₁ := by linarith
  have hb1 : 1 - c₁ < 1 := by linarith
  have hτpos : 0 < τ := Real.rpow_pos_of_pos (div_pos hc₁ hc₂) _
  have hτα : c₂ * τ ^ α = c₁ := by
    rw [hτ, ← Real.rpow_mul (div_pos hc₁ hc₂).le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]
    field_simp
  have hmono : ∀ t, 1 ≤ t → h (t + 1) ≤ h t := by
    intro t ht
    have := hrec t ht
    have hm : 0 ≤ min c₁ (c₂ * h t ^ α) :=
      le_min hc₁.le (mul_nonneg hc₂.le (Real.rpow_pos_of_pos (hpos t) α).le)
    nlinarith [mul_nonneg (hpos t).le hm]
  have hbig : ∀ t, 1 ≤ t → τ ≤ h t → h (t + 1) ≤ (1 - c₁) * h t := by
    intro t ht hτt
    have hge : c₁ ≤ c₂ * h t ^ α := by
      rw [← hτα]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hτpos.le hτt hα.le) hc₂.le
    have := hrec t ht
    rw [min_eq_left hge] at this
    linarith
  have hpowℓ : (1 - c₁) ^ ℓ = τ / c₀ := Real.rpow_logb hb0 hb1.ne (div_pos hτpos hc₀)
  have K1 : ∀ k : ℕ, (k : ℤ) ≤ ⌊ℓ⌋ → τ ≤ c₀ * (1 - c₁) ^ k := by
    intro k hk
    have hkℓ : (k : ℝ) ≤ ℓ := by
      have h2 : ((k : ℤ) : ℝ) ≤ (⌊ℓ⌋ : ℝ) := Int.cast_le.mpr hk
      push_cast at h2
      exact h2.trans (Int.floor_le ℓ)
    have := Real.rpow_le_rpow_of_exponent_ge hb0 hb1.le hkℓ
    rw [hpowℓ, Real.rpow_natCast, div_le_iff₀ hc₀] at this
    linarith
  have K2 : ∀ k : ℕ, ⌊ℓ⌋ < (k : ℤ) → c₀ * (1 - c₁) ^ k < τ := by
    intro k hk
    have hkℓ : ℓ < (k : ℝ) := by
      have h2 : (⌊ℓ⌋ : ℝ) + 1 ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hk
      push_cast at h2
      linarith [Int.lt_floor_add_one ℓ]
    have := Real.rpow_lt_rpow_of_exponent_gt hb0 hb1 hkℓ
    rw [hpowℓ, Real.rpow_natCast, lt_div_iff₀ hc₀] at this
    linarith
  have phase1 : ∀ t : ℕ, 1 ≤ t → (t : ℤ) < T → h t ≤ c₀ * (1 - c₁) ^ (t - 1) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro _; simpa using h1
    | succ t ht ih =>
      intro htT
      have ih' := ih (by omega)
      by_cases hτt : τ ≤ h t
      · calc h (t + 1) ≤ (1 - c₁) * h t := hbig t ht hτt
          _ ≤ (1 - c₁) * (c₀ * (1 - c₁) ^ (t - 1)) := mul_le_mul_of_nonneg_left ih' hb0.le
          _ = c₀ * (1 - c₁) ^ (t + 1 - 1) := by
            rw [show t + 1 - 1 = (t - 1) + 1 by omega, pow_succ]; ring
      · push Not at hτt
        have hk : ((t + 1 - 1 : ℕ) : ℤ) ≤ ⌊ℓ⌋ := by
          rcases lt_max_iff.mp htT with h2 | h2
          · push_cast at h2 ⊢; omega
          · push_cast at h2; omega
        exact (hmono t ht).trans (hτt.le.trans (K1 _ hk))
  have hT1 : 1 ≤ T := le_max_right _ _
  set t₀ := T.toNat with ht₀
  have ht₀T : (t₀ : ℤ) = T := Int.toNat_of_nonneg (by omega)
  have ht₀1 : 1 ≤ t₀ := by omega
  have hbase2 : h t₀ ≤ τ := by
    by_cases hTeq : T = 1
    · have ht₀' : t₀ = 1 := by omega
      have hfl : ⌊ℓ⌋ < ((0 : ℕ) : ℤ) := by
        have := le_max_left (⌊ℓ⌋ + 2) 1
        rw [← hT, hTeq] at this
        push_cast
        omega
      have := K2 0 hfl
      rw [pow_zero, mul_one] at this
      rw [ht₀']
      linarith
    · have hTval : T = ⌊ℓ⌋ + 2 := by
        rcases le_total (⌊ℓ⌋ + 2) 1 with h2 | h2
        · exfalso; apply hTeq; rw [hT, max_eq_right h2]
        · rw [hT, max_eq_left h2]
      have hprev := phase1 (t₀ - 1) (by omega) (by omega)
      have hk : ⌊ℓ⌋ < ((t₀ - 1 + 1 - 1 : ℕ) : ℤ) := by push_cast; omega
      by_cases hτt : τ ≤ h (t₀ - 1)
      · have h3 := hbig (t₀ - 1) (by omega) hτt
        rw [show t₀ - 1 + 1 = t₀ by omega] at h3
        have h4 := K2 (t₀ - 1 + 1 - 1) hk
        rw [show t₀ - 1 + 1 - 1 = (t₀ - 1 - 1) + 1 by omega, pow_succ] at h4
        nlinarith [mul_le_mul_of_nonneg_left hprev hb0.le]
      · push Not at hτt
        have h3 := hmono (t₀ - 1) (by omega)
        rw [show t₀ - 1 + 1 = t₀ by omega] at h3
        linarith
  have hle_τ : ∀ t, t₀ ≤ t → h t ≤ τ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hbase2
    | succ t ht ih => exact (hmono t (by omega)).trans ih
  refine ⟨phase1, fun t ht => ?_⟩
  have htt₀ : t₀ ≤ t := by omega
  set h' : ℕ → ℝ := fun k => h (k + t₀ - 1) with hh'
  have hrec' : ∀ k, 1 ≤ k → c₂ * h' k ^ (1 + α) ≤ h' k - h' (k + 1) := by
    intro k hk
    have hrt := hrec (k + t₀ - 1) (by omega)
    have hle := hle_τ (k + t₀ - 1) (by omega)
    have hsmall : c₂ * h (k + t₀ - 1) ^ α ≤ c₁ := by
      rw [← hτα]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos _).le hle hα.le) hc₂.le
    rw [min_eq_right hsmall] at hrt
    have e1 : h (k + t₀ - 1) ^ (1 + α) = h (k + t₀ - 1) * h (k + t₀ - 1) ^ α := by
      rw [Real.rpow_add (hpos _), Real.rpow_one]
    have e2 : k + 1 + t₀ - 1 = k + t₀ - 1 + 1 := by omega
    simp only [hh', e2]
    rw [e1]
    linarith
  have hmain := contraction_power h' τ c₂ α (fun k => hpos _) hτpos hc₂ hα
    (by simp only [hh']; rw [show 1 + t₀ - 1 = t₀ by omega]; exact hbase2) hrec' (t - t₀ + 1)
    (by omega)
  have e3 : h' (t - t₀ + 1) = h t := by simp only [hh']; congr 1; omega
  have e4 : ((t - t₀ + 1 : ℕ) : ℝ) - 1 = (t : ℝ) - (T : ℝ) := by
    rw [← ht₀T]; push_cast [Nat.cast_sub htt₀]; ring
  rw [e3, e4, hτα] at hmain
  exact hmain

end Proof

end Lemmata.CGBasics
