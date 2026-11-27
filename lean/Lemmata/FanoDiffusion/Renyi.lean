module

public import Lemmata.FanoDiffusion.Proof
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

/-!
# The information diffusion inequality for Rényi divergences (Proposition 2.1, `α ≠ 1`)

Hölder's inequality on `R` and on its complement compares the Hellinger integral
`∫ (dP/dQ)^α dQ` with its two-point version `q^{1-α} p^α + (1 - q)^{1-α} (1 - p)^α`: it is at least
that for `α > 1` and at most that for `α < 1`. The rest is real algebra.
-/

namespace Lemmata.FanoDiffusion

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

universe u

namespace Proof

section Renyi

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Hölder on a cell for `α > 1`: `P(R)^α ≤ (∫_R (dP/dQ)^α dQ) Q(R)^{α-1}`. -/
theorem holder_cell_gt (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] (hac : P ≪ Q)
    {α : ℝ} (hα : 1 < α) (R : Set Ω) :
    P R ^ α ≤ (∫⁻ x in R, P.rnDeriv Q x ^ α ∂Q) * Q R ^ (α - 1) := by
  have hpq := Real.HolderConjugate.conjExponent hα
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Q.restrict R) hpq (f := P.rnDeriv Q) (g := 1)
    (Measure.measurable_rnDeriv P Q).aemeasurable aemeasurable_const
  simp only [Pi.mul_apply, Pi.one_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at h
  rw [Measure.setLIntegral_rnDeriv hac R] at h
  have h2 := ENNReal.rpow_le_rpow h (by linarith : (0 : ℝ) ≤ α)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    at h2
  have e1 : 1 / α * α = 1 := by field_simp
  have e2 : 1 / Real.conjExponent α * α = α - 1 := by
    rw [Real.conjExponent]
    field_simp
  rw [e1, e2, ENNReal.rpow_one] at h2
  exact h2

/-- Hölder on a cell for `0 < α < 1`: `∫_R (dP/dQ)^α dQ ≤ P(R)^α Q(R)^{1-α}`. -/
theorem holder_cell_lt (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (R : Set Ω) :
    ∫⁻ x in R, P.rnDeriv Q x ^ α ∂Q ≤ P R ^ α * Q R ^ (1 - α) := by
  have hpq : α⁻¹.HolderConjugate (1 - α)⁻¹ :=
    Real.HolderConjugate.inv_inv hα0 (by linarith) (by ring)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Q.restrict R) hpq
    (f := fun x => P.rnDeriv Q x ^ α) (g := 1)
    ((Measure.measurable_rnDeriv P Q).pow_const α).aemeasurable aemeasurable_const
  simp only [Pi.mul_apply, Pi.one_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at h
  have e0 : ∀ x, (P.rnDeriv Q x ^ α) ^ α⁻¹ = P.rnDeriv Q x := fun x => by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hα0.ne', ENNReal.rpow_one]
  simp only [e0] at h
  have e1 : 1 / α⁻¹ = α := by field_simp
  have e2 : 1 / (1 - α)⁻¹ = 1 - α := by field_simp
  rw [e1, e2] at h
  calc ∫⁻ x in R, P.rnDeriv Q x ^ α ∂Q ≤ (∫⁻ x in R, P.rnDeriv Q x ∂Q) ^ α * Q R ^ (1 - α) := h
    _ ≤ P R ^ α * Q R ^ (1 - α) := by
      gcongr
      exact Measure.setLIntegral_rnDeriv_le R

/-- The two-point comparison for `α > 1`. -/
theorem renyi_two_point_gt (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P ≪ Q) {α : ℝ} (hα : 1 < α) {R : Set Ω} (hR : MeasurableSet R)
    (hfin : hellingerInt α P Q ≠ ∞) :
    Q.real R ^ (1 - α) * P.real R ^ α +
        (1 - Q.real R) ^ (1 - α) * (1 - P.real R) ^ α ≤ (hellingerInt α P Q).toReal := by
  have hsplit : hellingerInt α P Q = (∫⁻ x in R, P.rnDeriv Q x ^ α ∂Q) +
      ∫⁻ x in Rᶜ, P.rnDeriv Q x ^ α ∂Q := (lintegral_add_compl _ hR).symm
  have hI1 : (∫⁻ x in R, P.rnDeriv Q x ^ α ∂Q) ≠ ∞ := by
    intro h
    rw [hsplit, h, top_add] at hfin
    exact hfin rfl
  have hI2 : (∫⁻ x in Rᶜ, P.rnDeriv Q x ^ α ∂Q) ≠ ∞ := by
    intro h
    rw [hsplit, h, add_top] at hfin
    exact hfin rfl
  -- one cell
  have cell : ∀ S : Set Ω, MeasurableSet S → (∫⁻ x in S, P.rnDeriv Q x ^ α ∂Q) ≠ ∞ →
      Q.real S ^ (1 - α) * P.real S ^ α ≤ (∫⁻ x in S, P.rnDeriv Q x ^ α ∂Q).toReal := by
    intro S hS hIS
    have h := holder_cell_gt P Q hac hα S
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top hIS
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top Q S))) h
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h'
    change P.real S ^ α ≤ (∫⁻ x in S, P.rnDeriv Q x ^ α ∂Q).toReal * Q.real S ^ (α - 1) at h'
    rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ Q.real S) with hq | hq
    · have hQ0 : Q S = 0 := (measureReal_eq_zero_iff (measure_ne_top Q S)).mp hq.symm
      have hP0 : P.real S = 0 := (measureReal_eq_zero_iff (measure_ne_top P S)).mpr (hac hQ0)
      rw [← hq, hP0, Real.zero_rpow (by linarith), zero_mul]
      exact ENNReal.toReal_nonneg
    · have h3 := mul_le_mul_of_nonneg_left h' (Real.rpow_nonneg hq.le (1 - α))
      rw [show Q.real S ^ (1 - α) * ((∫⁻ x in S, P.rnDeriv Q x ^ α ∂Q).toReal *
          Q.real S ^ (α - 1)) = (∫⁻ x in S, P.rnDeriv Q x ^ α ∂Q).toReal *
          (Q.real S ^ (1 - α) * Q.real S ^ (α - 1)) by ring,
        ← Real.rpow_add hq, show 1 - α + (α - 1) = (0 : ℝ) by ring, Real.rpow_zero,
        mul_one] at h3
      exact h3
  have c1 := cell R hR hI1
  have c2 := cell Rᶜ hR.compl hI2
  rw [measureReal_compl hR, probReal_univ, measureReal_compl hR, probReal_univ] at c2
  rw [hsplit, ENNReal.toReal_add hI1 hI2]
  linarith

/-- The two-point comparison for `0 < α < 1`. -/
theorem renyi_two_point_lt (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {R : Set Ω} (hR : MeasurableSet R) :
    (hellingerInt α P Q).toReal ≤
      Q.real R ^ (1 - α) * P.real R ^ α + (1 - Q.real R) ^ (1 - α) * (1 - P.real R) ^ α := by
  have hsplit : hellingerInt α P Q = (∫⁻ x in R, P.rnDeriv Q x ^ α ∂Q) +
      ∫⁻ x in Rᶜ, P.rnDeriv Q x ^ α ∂Q := (lintegral_add_compl _ hR).symm
  have cell : ∀ S : Set Ω, (∫⁻ x in S, P.rnDeriv Q x ^ α ∂Q) ≠ ∞ ∧
      (∫⁻ x in S, P.rnDeriv Q x ^ α ∂Q).toReal ≤ Q.real S ^ (1 - α) * P.real S ^ α := by
    intro S
    have h := holder_cell_lt P Q hα0 hα1 S
    have hne : P S ^ α * Q S ^ (1 - α) ≠ ∞ := ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hα0.le (measure_ne_top P S))
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (measure_ne_top Q S))
    refine ⟨ne_top_of_le_ne_top hne h, ?_⟩
    have h' := ENNReal.toReal_mono hne h
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h'
    change _ ≤ P.real S ^ α * Q.real S ^ (1 - α) at h'
    linarith [mul_comm (P.real S ^ α) (Q.real S ^ (1 - α))]
  obtain ⟨hI1, c1⟩ := cell R
  obtain ⟨hI2, c2⟩ := cell Rᶜ
  rw [measureReal_compl hR, probReal_univ, measureReal_compl hR, probReal_univ] at c2
  rw [hsplit, ENNReal.toReal_add hI1 hI2]
  linarith

/-- The real algebra behind Proposition 2.1 for `α ≠ 1`. -/
theorem renyi_algebra {α p q H pmin pmax : ℝ} (hα0 : 0 < α) (hα1 : α ≠ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hpmin : 0 ≤ pmin) (hpmax : 0 < pmax) (hsum : pmin + pmax < 1)
    (hlo : pmin ≤ q) (hhi : q ≤ pmax) (hH : 0 < H)
    (hgt : 1 < α → q ^ (1 - α) * p ^ α + (1 - q) ^ (1 - α) * (1 - p) ^ α ≤ H)
    (hlt : α < 1 → H ≤ q ^ (1 - α) * p ^ α + (1 - q) ^ (1 - α) * (1 - p) ^ α)
    (hqpos : 1 < α → 0 < p → 0 < q) :
    p ^ α / (p ^ α + (1 - p) ^ α) ≤
      (exp ((α - 1) * (log H / (α - 1) + log (p ^ α + (1 - p) ^ α) / (1 - α) +
        log (1 - pmin))) - 1) / (((1 - pmin) / pmax) ^ (α - 1) - 1) := by
  have hq0 : 0 ≤ q := hpmin.trans hlo
  have h1p : 0 ≤ 1 - p := by linarith
  have h1m : 0 < 1 - pmin := by linarith
  have hS : 0 < p ^ α + (1 - p) ^ α := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h, Real.zero_rpow hα0.ne', zero_add, sub_zero, Real.one_rpow]
      norm_num
    · have := Real.rpow_pos_of_pos h α
      have := Real.rpow_nonneg h1p α
      linarith
  set S := p ^ α + (1 - p) ^ α with hSdef
  set B := (1 - pmin) / pmax with hBdef
  have hB : 1 < B := by
    rw [hBdef, one_lt_div hpmax]
    linarith
  have hα1' : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
  -- the exponent
  have hexp : exp ((α - 1) * (log H / (α - 1) + log S / (1 - α) + log (1 - pmin))) =
      H * (1 - pmin) ^ (α - 1) / S := by
    have e : (α - 1) * (log H / (α - 1) + log S / (1 - α) + log (1 - pmin)) =
        log H - log S + log (1 - pmin) * (α - 1) := by
      have : (1 - α) = -(α - 1) := by ring
      rw [this]
      field_simp
      ring
    rw [e, exp_add, exp_sub, exp_log hH, exp_log hS, Real.rpow_def_of_pos h1m]
    ring
  rw [hexp]
  -- `B^{α-1} = (1 - p_min)^{α-1} p_max^{1-α}`
  have hBpow : B ^ (α - 1) = (1 - pmin) ^ (α - 1) * pmax ^ (1 - α) := by
    rw [hBdef, Real.div_rpow h1m.le hpmax.le, show (1 : ℝ) - α = -(α - 1) by ring,
      Real.rpow_neg hpmax.le, div_eq_mul_inv]
  have hcancel : (1 - pmin) ^ (1 - α) * (1 - pmin) ^ (α - 1) = 1 := by
    rw [← Real.rpow_add h1m, show 1 - α + (α - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  have hm : 0 < (1 - pmin) ^ (α - 1) := Real.rpow_pos_of_pos h1m _
  set T := p ^ α * B ^ (α - 1) + (1 - p) ^ α with hTdef
  have hTS : p ^ α * (B ^ (α - 1) - 1) + S = T := by rw [hTdef, hSdef]; ring
  rcases lt_or_gt_of_ne hα1 with hlt1 | hgt1
  · -- `α < 1`
    have hden : B ^ (α - 1) - 1 < 0 := by
      have := Real.rpow_lt_one_of_one_lt_of_neg hB (by linarith : α - 1 < 0)
      linarith
    have hmono1 : q ^ (1 - α) * p ^ α ≤ pmax ^ (1 - α) * p ^ α :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hq0 hhi (by linarith))
        (Real.rpow_nonneg hp0 α)
    have hmono2 : (1 - q) ^ (1 - α) * (1 - p) ^ α ≤ (1 - pmin) ^ (1 - α) * (1 - p) ^ α :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
        (Real.rpow_nonneg h1p α)
    have hHle := hlt hlt1
    have hkey : H * (1 - pmin) ^ (α - 1) ≤ T := by
      have h2 := mul_le_mul_of_nonneg_right (hHle.trans (add_le_add hmono1 hmono2)) hm.le
      have h3 : (pmax ^ (1 - α) * p ^ α + (1 - pmin) ^ (1 - α) * (1 - p) ^ α) *
          (1 - pmin) ^ (α - 1) = T := by
        rw [hTdef, hBpow]
        linear_combination (1 - p) ^ α * hcancel
      linarith
    rw [le_div_iff_of_neg hden]
    have e : p ^ α / S * (B ^ (α - 1) - 1) - (H * (1 - pmin) ^ (α - 1) / S - 1) =
        (T - H * (1 - pmin) ^ (α - 1)) / S := by
      rw [← hTS]
      field_simp
      ring
    have : 0 ≤ (T - H * (1 - pmin) ^ (α - 1)) / S := div_nonneg (by linarith) hS.le
    linarith
  · -- `α > 1`
    have hden : 0 < B ^ (α - 1) - 1 := by
      have := Real.one_lt_rpow hB (by linarith : 0 < α - 1)
      linarith
    have hmono1 : pmax ^ (1 - α) * p ^ α ≤ q ^ (1 - α) * p ^ α := by
      rcases eq_or_lt_of_le hp0 with h | h
      · rw [← h, Real.zero_rpow hα0.ne', mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos (hqpos hgt1 h) hhi (by linarith))
          (Real.rpow_nonneg hp0 α)
    have hmono2 : (1 - pmin) ^ (1 - α) * (1 - p) ^ α ≤ (1 - q) ^ (1 - α) * (1 - p) ^ α := by
      rcases eq_or_lt_of_le hp1 with h | h
      · rw [h, sub_self, Real.zero_rpow hα0.ne', mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
            (by linarith))
          (Real.rpow_nonneg h1p α)
    have hHge := hgt hgt1
    have hkey : T ≤ H * (1 - pmin) ^ (α - 1) := by
      have h2 := mul_le_mul_of_nonneg_right ((add_le_add hmono1 hmono2).trans hHge) hm.le
      have h3 : (pmax ^ (1 - α) * p ^ α + (1 - pmin) ^ (1 - α) * (1 - p) ^ α) *
          (1 - pmin) ^ (α - 1) = T := by
        rw [hTdef, hBpow]
        linear_combination (1 - p) ^ α * hcancel
      linarith
    rw [le_div_iff₀ hden]
    have e : (H * (1 - pmin) ^ (α - 1) / S - 1) - p ^ α / S * (B ^ (α - 1) - 1) =
        (H * (1 - pmin) ^ (α - 1) - T) / S := by
      rw [← hTS]
      field_simp
      ring
    have : 0 ≤ (H * (1 - pmin) ^ (α - 1) - T) / S := div_nonneg (by linarith) hS.le
    linarith

theorem info_diffusion_fano_renyi : InfoDiffusionFanoRenyi.{u} := by
  intro Ω _ P Q _ _ R pmin pmax α hR hpmin hpmax hsum hlo hhi hα0 hα1 hac hpos hfin
  have hH : 0 < (hellingerInt α P Q).toReal := ENNReal.toReal_pos hpos hfin
  have hp0 : 0 ≤ P.real R := measureReal_nonneg
  have hp1 : P.real R ≤ 1 := measureReal_le_one
  have hqpos : 1 < α → 0 < P.real R → 0 < Q.real R := fun hgt hp => by
    rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ Q.real R) with h | h
    · exfalso
      have hQ0 : Q R = 0 := (measureReal_eq_zero_iff (measure_ne_top Q R)).mp h.symm
      have : P.real R = 0 := (measureReal_eq_zero_iff (measure_ne_top P R)).mpr (hac hgt hQ0)
      linarith
    · exact h
  have key := renyi_algebra (q := Q.real R) (H := (hellingerInt α P Q).toReal) hα0 hα1 hp0 hp1
    hpmin hpmax hsum hlo hhi hH (fun hgt => renyi_two_point_gt P Q (hac hgt) hgt hR hfin)
    (fun hlt => renyi_two_point_lt P Q hα0 hlt hR) hqpos
  unfold renyiDiv binRenyiEntropy
  exact key

theorem info_diffusion_fano_renyi_gt_one : InfoDiffusionFanoRenyiGtOne.{u} := by
  intro Ω _ P Q _ _ R pmin pmax α hR hpmin hpmax hsum hlo hhi hα hac hfin
  have hp0 : 0 ≤ P.real R := measureReal_nonneg
  have hp1 : P.real R ≤ 1 := measureReal_le_one
  have h2pt := renyi_two_point_gt P Q hac hα hR hfin
  have hqpos : 0 < P.real R → 0 < Q.real R := fun hp => by
    rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ Q.real R) with h | h
    · exfalso
      have hQ0 : Q R = 0 := (measureReal_eq_zero_iff (measure_ne_top Q R)).mp h.symm
      have : P.real R = 0 := (measureReal_eq_zero_iff (measure_ne_top P R)).mpr (hac hQ0)
      linarith
    · exact h
  have hq1 : Q.real R < 1 := by linarith
  have hh2pos : 0 < Q.real R ^ (1 - α) * P.real R ^ α +
      (1 - Q.real R) ^ (1 - α) * (1 - P.real R) ^ α := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h, Real.zero_rpow (by linarith), mul_zero, zero_add, sub_zero, Real.one_rpow,
        mul_one]
      exact Real.rpow_pos_of_pos (by linarith) _
    · have h3 := mul_pos (Real.rpow_pos_of_pos (hqpos h) (1 - α)) (Real.rpow_pos_of_pos h α)
      have h4 := mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - Q.real R) (1 - α))
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - P.real R) α)
      linarith
  have hpos : hellingerInt α P Q ≠ 0 := by
    intro h0
    rw [h0, ENNReal.toReal_zero] at h2pt
    linarith
  have hmain := info_diffusion_fano_renyi P Q R pmin pmax α hR hpmin hpmax hsum hlo hhi
    (by linarith) (by linarith : α ≠ 1) (fun _ => hac) hpos hfin
  have hS : P.real R ^ α + (1 - P.real R) ^ α ≤ 1 := by
    have h5 := Real.add_rpow_le_rpow_add hp0 (by linarith : (0 : ℝ) ≤ 1 - P.real R) hα.le
    rwa [add_sub_cancel, Real.one_rpow] at h5
  have hSpos : 0 < P.real R ^ α + (1 - P.real R) ^ α := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h, Real.zero_rpow (by linarith), zero_add, sub_zero, Real.one_rpow]
      norm_num
    · have := Real.rpow_pos_of_pos h α
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 - P.real R) α
      linarith
  have h1 : P.real R ^ α ≤ P.real R ^ α / (P.real R ^ α + (1 - P.real R) ^ α) :=
    le_div_self (Real.rpow_nonneg hp0 α) hSpos hS
  have h2 := h1.trans hmain
  calc P.real R = (P.real R ^ α) ^ (1 / α) := by
        rw [← Real.rpow_mul hp0, mul_one_div_cancel (by linarith : α ≠ 0), Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hp0 α) h2 (by positivity)

end Renyi

end Proof

end Lemmata.FanoDiffusion
