module

public import Lemmata.LPHardnessInP.ParityExtension.Witness
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

/-- The coefficient of the high-violation distribution. -/
noncomputable def parityCoefficientA (ε : ℝ) (k : ℕ) : ℝ :=
  10 * (k : ℝ) * (1 + ε) ^ 2 /
    ((1 - ε) * ((2 * k + 3).choose 3 : ℝ))

/-- The coefficient of the one-violation distribution. -/
noncomputable def parityCoefficientB (ε : ℝ) : ℝ :=
  3 * (1 + ε) ^ 6 / (1 - ε)

/-- The exact triple-count identity used in the coefficient estimates. -/
theorem triple_count_identity (k : ℕ) :
    6 * ((2 * k + 3).choose 3 : ℝ) =
      (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by
  have h := Nat.choose_succ_right_eq (2 * k + 3) 2
  have hs : 2 * k + 3 - 2 = 2 * k + 1 := by omega
  rw [hs] at h
  have hcast :
      ((2 * k + 3).choose 3 : ℝ) * 3 =
        ((2 * k + 3).choose 2 : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_choose_two] at hcast
  push_cast at hcast
  nlinarith

theorem triple_count_pos (k : ℕ) : 0 < ((2 * k + 3).choose 3 : ℝ) := by
  exact_mod_cast (Nat.choose_pos (show 3 ≤ 2 * k + 3 by omega))

theorem triple_count_lower (k : ℕ) :
    (4 / 3 : ℝ) * (k : ℝ) ^ 3 ≤ ((2 * k + 3).choose 3 : ℝ) := by
  have h := triple_count_identity k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [sq_nonneg (k : ℝ)]

/-- A small polynomial estimate, sufficient for the one-violation coefficient. -/
theorem sixth_power_small {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 100) :
    (1 + ε) ^ 6 ≤ 1 + 7 * ε := by
  have hε1 : ε ≤ 1 := by linarith
  have hp (t : ℕ) (ht : 2 ≤ t) : ε ^ t ≤ ε / 100 := by
    calc
      ε ^ t ≤ ε ^ 2 := pow_le_pow_of_le_one hε hε1 ht
      _ ≤ ε / 100 := by nlinarith [mul_nonneg hε (sub_nonneg.mpr hεsmall)]
  nlinarith [hp 2 (by omega), hp 3 (by omega), hp 4 (by omega),
    hp 5 (by omega), hp 6 (by omega)]

theorem parityCoefficientB_bound {ε : ℝ}
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 100) :
    parityCoefficientB ε - 3 ≤ 25 * ε := by
  have hden : 0 < 1 - ε := by linarith
  have hpow := sixth_power_small hε hεsmall
  have hsq : ε ^ 2 ≤ ε / 100 := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hεsmall)]
  have hdiv : parityCoefficientB ε ≤ 3 + 25 * ε := by
    unfold parityCoefficientB
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

theorem parityCoefficientA_nonneg {ε : ℝ} (hεsmall : ε ≤ 1 / 100) (k : ℕ) :
    0 ≤ parityCoefficientA ε k := by
  unfold parityCoefficientA
  have hden : 0 < 1 - ε := by linarith
  positivity

theorem parityCoefficientA_bound {ε : ℝ} (hε : 0 ≤ ε)
    (hεsmall : ε ≤ 1 / 100) {k : ℕ} (hk : 0 < k) :
    parityCoefficientA ε k ≤ 8 / (k : ℝ) ^ 2 := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < 1 - ε := by linarith
  have hp := triple_count_pos k
  have hplower := triple_count_lower k
  have hsq : ε ^ 2 ≤ ε / 100 := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hεsmall)]
  have hcoef : 10 * (1 + ε) ^ 2 ≤ (32 / 3 : ℝ) * (1 - ε) := by
    nlinarith
  unfold parityCoefficientA
  apply (div_le_div_iff₀ (mul_pos hden hp) (sq_pos_of_pos hkp)).mpr
  calc
    10 * (k : ℝ) * (1 + ε) ^ 2 * (k : ℝ) ^ 2 =
        (10 * (1 + ε) ^ 2) * (k : ℝ) ^ 3 := by ring
    _ ≤ ((32 / 3 : ℝ) * (1 - ε)) * (k : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (8 * (1 - ε)) * ((4 / 3 : ℝ) * (k : ℝ) ^ 3) := by ring
    _ ≤ (8 * (1 - ε)) * ((2 * k + 3).choose 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hplower (by positivity)
    _ = 8 * ((1 - ε) * ((2 * k + 3).choose 3 : ℝ)) := by ring

-- DOCS_BEGIN_MAIN
/-- The explicit choices `ε=r/100` and `k≥400/r` give small enough
coefficient errors. The estimates are derived from the actual formulas. -/
theorem calibrated_coefficients {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {k : ℕ} (hk : 400 / r ≤ (k : ℝ)) :
    0 ≤ parityCoefficientA (r / 100) k ∧
      parityCoefficientA (r / 100) k * (4 * (k : ℝ) + 3) ≤ r / 10 ∧
      parityCoefficientB (r / 100) - 3 ≤ r / 4 := by
  have hε : 0 ≤ r / 100 := by positivity
  have hεsmall : r / 100 ≤ 1 / 100 := by linarith
  have hkr : 400 ≤ (k : ℝ) * r := (div_le_iff₀ hr).mp hk
  have hk400 : 400 ≤ (k : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hr1 (Nat.cast_nonneg k)
    nlinarith
  have hkp : 0 < (k : ℝ) := by linarith
  have hkn : 0 < k := by exact_mod_cast hkp
  refine ⟨parityCoefficientA_nonneg hεsmall k, ?_, ?_⟩
  · calc
      parityCoefficientA (r / 100) k * (4 * (k : ℝ) + 3) ≤
          (8 / (k : ℝ) ^ 2) * (4 * (k : ℝ) + 3) :=
        mul_le_mul_of_nonneg_right (parityCoefficientA_bound hε hεsmall hkn)
          (by positivity)
      _ ≤ (8 / (k : ℝ) ^ 2) * (5 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 40 / (k : ℝ) := by field_simp; ring
      _ ≤ r / 10 := (div_le_iff₀ hkp).mpr (by nlinarith)
  · have hb := parityCoefficientB_bound hε hεsmall
    linarith

/-- The explicitly calibrated corruption witness has a strictly positive
margin greater than `3r/2` for every fixed positive shift `r≤1`. -/
theorem calibrated_witness_gap {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {k : ℕ} (hk : 400 / r ≤ (k : ℝ)) :
    3 * r / 2 <
      (3 - r) - parityCoefficientA (r / 100) k * (4 * (k : ℝ) + 3 - r) -
        parityCoefficientB (r / 100) * (1 - r) := by
  obtain ⟨hA, hAh, hB⟩ := calibrated_coefficients hr hr1 hk
  rw [witness_gap_identity]
  have hAr : 0 ≤ parityCoefficientA (r / 100) k * r := mul_nonneg hA hr.le
  have hBr := mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr hr1)
  nlinarith [sq_nonneg r]
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
