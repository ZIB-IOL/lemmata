module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.HardFamily
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact LMO water-level algebra

This module verifies the algebraic core of Lemma `lem:exact-lmo` in
`tex/sc-lmo-distributional.tex`.  The KKT theorem itself remains an analytic
interface; once the coordinatewise soft-threshold formula is supplied, all
information-recovery identities below are fully proved.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Nonnegative magnitude of one coordinate of the soft-threshold LMO answer. -/
noncomputable def softAmount (p w lam : ℝ) : ℝ := max 0 (|p| / lam - w)

lemma softAmount_nonneg (p w lam : ℝ) : 0 ≤ softAmount p w lam := by
  simp [softAmount]

lemma softAmount_eq_of_active {p w lam : ℝ} (h : w < |p| / lam) :
    softAmount p w lam = |p| / lam - w := by
  rw [softAmount, max_eq_right]
  linarith

lemma softAmount_eq_zero_of_inactive {p w lam : ℝ} (h : |p| / lam ≤ w) :
    softAmount p w lam = 0 := by
  rw [softAmount, max_eq_left]
  linarith

/-- Coordinatewise complementarity identity.  It includes both the active and
inactive cases and is the key to recovering the KKT multiplier from `(p,z)`. -/
lemma abs_mul_softAmount {p w lam : ℝ} (hlam : 0 < lam) :
    |p| * softAmount p w lam =
      lam * (softAmount p w lam ^ 2 + w * softAmount p w lam) := by
  by_cases hactive : w < |p| / lam
  · rw [softAmount_eq_of_active hactive]
    field_simp [hlam.ne']
    ring
  · have hinactive : |p| / lam ≤ w := le_of_not_gt hactive
    rw [softAmount_eq_zero_of_inactive hinactive]
    ring

/-- A nonzero answer coordinate reveals its weight exactly. -/
lemma recover_active_weight {p w lam : ℝ}
    (hq : 0 < softAmount p w lam) :
    w = |p| / lam - softAmount p w lam := by
  by_cases hactive : w < |p| / lam
  · rw [softAmount_eq_of_active hactive]
    ring
  · have hinactive : |p| / lam ≤ w := le_of_not_gt hactive
    rw [softAmount_eq_zero_of_inactive hinactive] at hq
    linarith

/-- If weights encode ranks by `w²=2C²r`, a nonzero answer coordinate reveals
that rank through the displayed formula. -/
lemma recover_active_rank {p w lam C r : ℝ}
    (hC : C ≠ 0) (hq : 0 < softAmount p w lam)
    (hw : w ^ 2 = 2 * C ^ 2 * r) :
    r = (|p| / lam - softAmount p w lam) ^ 2 / (2 * C ^ 2) := by
  rw [← recover_active_weight hq, hw]
  field_simp [hC]

/-- Substituting one active soft-threshold coordinate into the weighted
quadratic constraint. -/
lemma active_constraint_contribution {u w : ℝ} :
    (1 / 2 : ℝ) * (u - w) ^ 2 + w * (u - w) =
      (1 / 2 : ℝ) * (u ^ 2 - w ^ 2) := by
  ring

/-- The water-level normalization used by the paper. -/
noncomputable def waterTau (C lam : ℝ) : ℝ := 1 / (2 * C ^ 2 * lam ^ 2)

/-- Conversion of an active constraint contribution to `τ p²-rank` when
`w²=2C² rank`. -/
lemma active_contribution_eq_water_level
    {C lam p w r : ℝ} (hC : C ≠ 0) (hlam : lam ≠ 0)
    (hw : w ^ 2 = 2 * C ^ 2 * r) :
    ((1 / 2 : ℝ) * ((|p| / lam) ^ 2 - w ^ 2)) / C ^ 2 =
      waterTau C lam * p ^ 2 - r := by
  rw [waterTau, hw]
  have habs : |p| ^ 2 = p ^ 2 := sq_abs p
  rw [div_pow, habs]
  field_simp [hC, hlam]

/-- If an inactive coordinate satisfies `|p|/lam ≤ w`, then its rank satisfies
the paper's water-level lower bound. -/
lemma inactive_water_level_le_rank
    {C lam p w r : ℝ} (hC : 0 < C) (hlam : 0 < lam)
    (hw : w ^ 2 = 2 * C ^ 2 * r) (hinactive : |p| / lam ≤ w)
    (hw0 : 0 ≤ w) :
    waterTau C lam * p ^ 2 ≤ r := by
  have hleft0 : 0 ≤ |p| / lam := by positivity
  have hsq : (|p| / lam) ^ 2 ≤ w ^ 2 := by nlinarith
  rw [div_pow, sq_abs, hw] at hsq
  rw [waterTau]
  have hden : 0 < 2 * C ^ 2 * lam ^ 2 := by positivity
  have hlam2 : 0 < lam ^ 2 := sq_pos_of_pos hlam
  have hsq' := (div_le_iff₀ hlam2).mp hsq
  rw [show 1 / (2 * C ^ 2 * lam ^ 2) * p ^ 2 =
      p ^ 2 / (2 * C ^ 2 * lam ^ 2) by field_simp]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Integer form of the inactive-rank lower bound used in the manuscript. -/
lemma inactive_rank_ceiling
    {C lam p w : ℝ} {rank : ℕ}
    (hC : 0 < C) (hlam : 0 < lam) (hw0 : 0 ≤ w)
    (hw : w ^ 2 = 2 * C ^ 2 * (rank : ℝ))
    (hinactive : |p| / lam ≤ w) :
    Nat.ceil (waterTau C lam * p ^ 2) ≤ rank := by
  apply Nat.ceil_le.mpr
  exact inactive_water_level_le_rank hC hlam hw hinactive hw0

/-- Summed complementarity identity for all LMO coordinate magnitudes. -/
lemma sum_abs_mul_softAmount {d : ℕ}
    (p w : Fin d → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (∑ i, |p i| * softAmount (p i) (w i) lam) =
      lam * ((∑ i, softAmount (p i) (w i) lam ^ 2) +
        ∑ i, w i * softAmount (p i) (w i) lam) := by
  calc
    (∑ i, |p i| * softAmount (p i) (w i) lam) =
        ∑ i, lam * (softAmount (p i) (w i) lam ^ 2 +
          w i * softAmount (p i) (w i) lam) := by
            apply Finset.sum_congr rfl
            intro i _
            exact abs_mul_softAmount hlam
    _ = lam * ((∑ i, softAmount (p i) (w i) lam ^ 2) +
        ∑ i, w i * softAmount (p i) (w i) lam) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- Piecewise-linear water-level profile. -/
noncomputable def waterProfile {d : ℕ} (p rank : Fin d → ℝ) (tau : ℝ) : ℝ :=
  ∑ i, max 0 (tau * p i ^ 2 - rank i)

lemma waterProfile_continuous {d : ℕ} (p rank : Fin d → ℝ) :
    Continuous (waterProfile p rank) := by
  unfold waterProfile
  fun_prop

lemma waterProfile_zero {d : ℕ} (p rank : Fin d → ℝ)
    (hrank : ∀ i, 0 ≤ rank i) : waterProfile p rank 0 = 0 := by
  simp [waterProfile, hrank]

lemma waterProfile_mono {d : ℕ} (p rank : Fin d → ℝ) :
    Monotone (waterProfile p rank) := by
  intro a b hab
  unfold waterProfile
  apply Finset.sum_le_sum
  intro i _
  apply max_le_max_left
  nlinarith [sq_nonneg (p i)]

lemma waterProfile_strict_of_pos {d : ℕ} (p rank : Fin d → ℝ)
    (hrank : ∀ i, 0 ≤ rank i)
    {a b : ℝ} (hab : a < b) (hpos : 0 < waterProfile p rank a) :
    waterProfile p rank a < waterProfile p rank b := by
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      0 ≤ max 0 (a * p i ^ 2 - rank i) := by intros; exact le_max_left _ _
  have hex : ∃ i ∈ (Finset.univ : Finset (Fin d)),
      0 < max 0 (a * p i ^ 2 - rank i) := by
    rw [waterProfile] at hpos
    exact (Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos
  unfold waterProfile
  apply Finset.sum_lt_sum
  · intro i _
    apply max_le_max_left
    nlinarith [sq_nonneg (p i)]
  · rcases hex with ⟨i, hi, hiactive⟩
    refine ⟨i, hi, ?_⟩
    have hpi : 0 < p i ^ 2 := by
      by_contra hp
      have hp0 : p i ^ 2 = 0 := le_antisymm (le_of_not_gt hp) (sq_nonneg _)
      rw [hp0] at hiactive
      simp at hiactive
      exact (not_lt_of_ge (hrank i)) hiactive
    have harg : a * p i ^ 2 - rank i < b * p i ^ 2 - rank i := by
      nlinarith
    have ha0 : 0 < a * p i ^ 2 - rank i := by
      simpa [max_eq_right (le_of_lt hiactive)] using hiactive
    rw [max_eq_right ha0.le, max_eq_right (le_trans ha0.le harg.le)]
    exact harg

/-- Every nonzero query has a unique positive water level with unit total
slack. -/
theorem existsUnique_waterLevel {d : ℕ} (p rank : Fin d → ℝ)
    (hrank : ∀ i, 0 ≤ rank i) (hp : ∃ i, p i ≠ 0) :
    ∃! tau : ℝ, 0 < tau ∧ waterProfile p rank tau = 1 := by
  rcases hp with ⟨j, hpj⟩
  let hi : ℝ := (1 + rank j) / p j ^ 2
  have hpj2 : 0 < p j ^ 2 := sq_pos_of_ne_zero hpj
  have hhi : 0 < hi := by
    dsimp [hi]
    exact div_pos (by nlinarith [hrank j]) hpj2
  have hterm : hi * p j ^ 2 - rank j = 1 := by
    dsimp [hi]
    field_simp [hpj]
    ring
  have hprofile_hi : 1 ≤ waterProfile p rank hi := by
    unfold waterProfile
    have hjle : max 0 (hi * p j ^ 2 - rank j) ≤
        ∑ i, max 0 (hi * p i ^ 2 - rank i) := by
      change max 0 (hi * p j ^ 2 - rank j) ≤
        (Finset.univ : Finset (Fin d)).sum
          (fun i => max 0 (hi * p i ^ 2 - rank i))
      exact Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
          le_max_left (0 : ℝ) (hi * p i ^ 2 - rank i))
        (Finset.mem_univ j)
    rw [hterm] at hjle
    norm_num at hjle
    exact hjle
  have htarget : (1 : ℝ) ∈ Set.Icc (waterProfile p rank 0) (waterProfile p rank hi) := by
    rw [waterProfile_zero p rank hrank]
    exact ⟨by norm_num, hprofile_hi⟩
  rcases intermediate_value_Icc hhi.le (waterProfile_continuous p rank).continuousOn htarget with
    ⟨tau, htauIcc, htauEq⟩
  have htau0 : 0 < tau := by
    by_contra h
    have htau : tau = 0 := le_antisymm (le_of_not_gt h) htauIcc.1
    subst tau
    rw [waterProfile_zero p rank hrank] at htauEq
    norm_num at htauEq
  refine ⟨tau, ⟨htau0, htauEq⟩, ?_⟩
  intro other hother
  rcases lt_trichotomy other tau with hlt | heq | hgt
  · have hs := waterProfile_strict_of_pos p rank hrank hlt
      (by rw [hother.2]; norm_num)
    linarith
  · exact heq
  · have hs := waterProfile_strict_of_pos p rank hrank hgt
      (by rw [htauEq]; norm_num)
    linarith

/-- Positive multiplier associated with a positive water level. -/
noncomputable def multiplierOfTau (C tau : ℝ) : ℝ :=
  (Real.sqrt (2 * C ^ 2 * tau))⁻¹

lemma multiplierOfTau_pos {C tau : ℝ} (hC : 0 < C) (htau : 0 < tau) :
    0 < multiplierOfTau C tau := by
  dsimp [multiplierOfTau]
  positivity

lemma waterTau_multiplierOfTau {C tau : ℝ} (hC : 0 < C) (htau : 0 < tau) :
    waterTau C (multiplierOfTau C tau) = tau := by
  have harg : 0 < 2 * C ^ 2 * tau := by positivity
  have hsqrt : Real.sqrt (2 * C ^ 2 * tau) ^ 2 = 2 * C ^ 2 * tau :=
    Real.sq_sqrt harg.le
  unfold waterTau multiplierOfTau
  rw [inv_pow, hsqrt]
  field_simp [hC.ne', htau.ne']

/-- The numerical query and LMO answer determine the positive KKT multiplier.
This is equation immediately before `eq:tau-from-active` in the paper. -/
theorem recover_multiplier_from_soft_answer {d : ℕ}
    (p w : Fin d → ℝ) {C lam : ℝ}
    (hC : 0 < C) (hlam : 0 < lam)
    (hboundary :
      (1 / 2 : ℝ) * (∑ i, softAmount (p i) (w i) lam ^ 2) +
        ∑ i, w i * softAmount (p i) (w i) lam = C ^ 2) :
    lam =
      (∑ i, |p i| * softAmount (p i) (w i) lam) /
        (C ^ 2 + (1 / 2 : ℝ) * ∑ i, softAmount (p i) (w i) lam ^ 2) := by
  have hsum := sum_abs_mul_softAmount p w hlam
  have hden :
      C ^ 2 + (1 / 2 : ℝ) * ∑ i, softAmount (p i) (w i) lam ^ 2 =
        (∑ i, softAmount (p i) (w i) lam ^ 2) +
          ∑ i, w i * softAmount (p i) (w i) lam := by
    linarith
  rw [hden, hsum]
  have hpos : 0 <
      (∑ i, softAmount (p i) (w i) lam ^ 2) +
        ∑ i, w i * softAmount (p i) (w i) lam := by
    rw [← hden]
    have hsum_nonneg : 0 ≤ (∑ i, softAmount (p i) (w i) lam ^ 2) := by positivity
    nlinarith [sq_pos_of_pos hC]
  field_simp [hpos.ne']

end Lemmata.DistributionalLowerBounds.Core.Distributional
