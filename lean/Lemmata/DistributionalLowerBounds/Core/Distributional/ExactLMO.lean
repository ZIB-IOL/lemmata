module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.WaterLevel
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact soft-threshold LMO

This module closes the analytic interface left in `WaterLevel.lean`: it proves
directly, without invoking a KKT library, that the soft-threshold vector
minimizes the queried linear functional over the weighted hard set whenever its
constraint is active.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Signed coordinate of the LMO answer. -/
noncomputable def softCoordinate (p w lam : ℝ) : ℝ :=
  if 0 ≤ p then -softAmount p w lam else softAmount p w lam

@[simp] lemma abs_softCoordinate (p w lam : ℝ) :
    |softCoordinate p w lam| = softAmount p w lam := by
  rw [softCoordinate]
  split_ifs <;> simp [abs_of_nonneg (softAmount_nonneg p w lam)]

/-- Scalar subgradient inequality at the soft-threshold point. -/
lemma softCoordinate_strong_subgradient
    {p w lam : ℝ} (hw : 0 ≤ w) (hlam : 0 < lam) (x : ℝ) :
    (1 / 2 : ℝ) * softCoordinate p w lam ^ 2 +
        w * |softCoordinate p w lam| +
        (-p / lam) * (x - softCoordinate p w lam) +
        (1 / 2 : ℝ) * (x - softCoordinate p w lam) ^ 2 ≤
      (1 / 2 : ℝ) * x ^ 2 + w * |x| := by
  by_cases hp : 0 ≤ p
  · have habs : |p| = p := abs_of_nonneg hp
    by_cases ha : w < p / lam
    · have hq : softAmount p w lam = p / lam - w := by
        simpa [habs] using
          (softAmount_eq_of_active (p := p) (w := w) (lam := lam)
            (by simpa [habs] using ha))
      have hz : softCoordinate p w lam = -(p / lam - w) := by
        simp [softCoordinate, hp, hq]
      rw [hz]
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx,
          abs_of_nonpos (by nlinarith [ha] : -(p / lam - w) ≤ 0)]
        have hwx : 0 ≤ w * x := mul_nonneg hw hx
        have hs := sq_nonneg (x + (p / lam - w))
        ring_nf at hs ⊢
        nlinarith
      · have hx' : x < 0 := lt_of_not_ge hx
        rw [abs_of_neg hx',
          abs_of_nonpos (by nlinarith [ha] : -(p / lam - w) ≤ 0)]
        have hs := sq_nonneg (x + (p / lam - w))
        ring_nf at hs ⊢
        nlinarith
    · have hi : p / lam ≤ w := le_of_not_gt ha
      have hq : softAmount p w lam = 0 := by
        apply softAmount_eq_zero_of_inactive
        simpa [habs] using hi
      have hz : softCoordinate p w lam = 0 := by simp [softCoordinate, hp, hq]
      rw [hz]
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]
        have hpdiv : 0 ≤ p / lam := by positivity
        have hprod := mul_nonneg hx (add_nonneg hw hpdiv)
        ring_nf at hprod ⊢
        nlinarith
      · have hx' : x < 0 := lt_of_not_ge hx
        rw [abs_of_neg hx']
        have hcoef : 0 ≤ w - p / lam := sub_nonneg.mpr hi
        have hprod := mul_nonneg (le_of_lt (neg_pos.mpr hx')) hcoef
        ring_nf at hprod ⊢
        nlinarith
  · have hp' : p < 0 := lt_of_not_ge hp
    have habs : |p| = -p := abs_of_neg hp'
    by_cases ha : w < (-p) / lam
    · have hq : softAmount p w lam = (-p) / lam - w := by
        simpa [habs] using
          (softAmount_eq_of_active (p := p) (w := w) (lam := lam)
            (by simpa [habs] using ha))
      have hz : softCoordinate p w lam = (-p) / lam - w := by
        simp [softCoordinate, hp, hq]
      rw [hz]
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx,
          abs_of_nonneg (by nlinarith [ha] : 0 ≤ (-p) / lam - w)]
        have hs := sq_nonneg (x - ((-p) / lam - w))
        ring_nf at hs ⊢
        nlinarith
      · have hx' : x < 0 := lt_of_not_ge hx
        rw [abs_of_neg hx',
          abs_of_nonneg (by nlinarith [ha] : 0 ≤ (-p) / lam - w)]
        have hwnegx : 0 ≤ w * (-x) := mul_nonneg hw (by linarith)
        have hs := sq_nonneg (x - ((-p) / lam - w))
        ring_nf at hs ⊢
        nlinarith
    · have hi : (-p) / lam ≤ w := le_of_not_gt ha
      have hq : softAmount p w lam = 0 := by
        apply softAmount_eq_zero_of_inactive
        simpa [habs] using hi
      have hz : softCoordinate p w lam = 0 := by simp [softCoordinate, hp, hq]
      rw [hz]
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]
        have hcoef : 0 ≤ w + p / lam := by
          ring_nf at hi ⊢
          linarith
        have hprod := mul_nonneg hx hcoef
        ring_nf at hprod ⊢
        nlinarith
      · have hx' : x < 0 := lt_of_not_ge hx
        rw [abs_of_neg hx']
        have hcoef : 0 ≤ w - p / lam := by
          have hpdiv : p / lam < 0 := div_neg_of_neg_of_pos hp' hlam
          linarith
        have hprod := mul_nonneg (le_of_lt (neg_pos.mpr hx')) hcoef
        ring_nf at hprod ⊢
        nlinarith

/-- The ordinary subgradient inequality follows by dropping the nonnegative
quadratic remainder. -/
lemma softCoordinate_subgradient
    {p w lam : ℝ} (hw : 0 ≤ w) (hlam : 0 < lam) (x : ℝ) :
    (1 / 2 : ℝ) * softCoordinate p w lam ^ 2 +
        w * |softCoordinate p w lam| +
        (-p / lam) * (x - softCoordinate p w lam) ≤
      (1 / 2 : ℝ) * x ^ 2 + w * |x| := by
  have h := softCoordinate_strong_subgradient (p := p) hw hlam x
  nlinarith [sq_nonneg (x - softCoordinate p w lam)]

/-- Coordinate-sum version of the weighted constraint. -/
noncomputable def coordinateEnergy {d : ℕ} (w x : Fin d → ℝ) : ℝ :=
  ∑ i, ((1 / 2 : ℝ) * x i ^ 2 + w i * |x i|)

/-- Coordinate energy is exactly the norm/weighted-ℓ₁ expression defining
`weightedHardSet`. -/
lemma coordinateEnergy_eq_weightedEnergy {d : ℕ}
    (w : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    coordinateEnergy w (fun i => x i) =
      (1 / 2 : ℝ) * ‖x‖ ^ 2 + ∑ i, w i * |x i| := by
  rw [coordinateEnergy, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

lemma mem_weightedHardSet_iff_coordinateEnergy {d : ℕ}
    (C : ℝ) (w : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ weightedHardSet C w ↔ coordinateEnergy w (fun i => x i) ≤ C ^ 2 := by
  change (1 / 2 : ℝ) * ‖x‖ ^ 2 + ∑ i, w i * |x i| ≤ C ^ 2 ↔ _
  rw [coordinateEnergy_eq_weightedEnergy]

/-- One coordinate's normalized energy equals its positive water-level slack. -/
lemma softCoordinate_energy_div_eq_waterTerm
    {p w lam C rank : ℝ}
    (hC : 0 < C) (hlam : 0 < lam) (hw0 : 0 ≤ w)
    (hw : w ^ 2 = 2 * C ^ 2 * rank) :
    (((1 / 2 : ℝ) * softCoordinate p w lam ^ 2 +
        w * |softCoordinate p w lam|) / C ^ 2) =
      max 0 (waterTau C lam * p ^ 2 - rank) := by
  have hsqcoord : softCoordinate p w lam ^ 2 = softAmount p w lam ^ 2 := by
    rw [← sq_abs (softCoordinate p w lam), abs_softCoordinate]
  rw [hsqcoord, abs_softCoordinate]
  by_cases hactive : w < |p| / lam
  · rw [softAmount_eq_of_active hactive]
    have hleft := active_constraint_contribution
      (u := |p| / lam) (w := w)
    have heq := active_contribution_eq_water_level
      (p := p) hC.ne' hlam.ne' hw
    have harg : 0 < waterTau C lam * p ^ 2 - rank := by
      rw [← heq]
      have hu0 : 0 ≤ |p| / lam := by positivity
      have hsq : w ^ 2 < (|p| / lam) ^ 2 := by nlinarith
      apply div_pos
      · nlinarith
      · positivity
    rw [max_eq_right harg.le]
    rw [hleft]
    exact heq
  · have hinactive : |p| / lam ≤ w := le_of_not_gt hactive
    rw [softAmount_eq_zero_of_inactive hinactive]
    have hwater := inactive_water_level_le_rank hC hlam hw hinactive hw0
    rw [max_eq_left]
    · ring
    · linarith

/-- A unit water-level profile is exactly the active-boundary equation required
by `softCoordinate_is_LMO`. -/
theorem softCoordinate_boundary_of_waterProfile {d : ℕ}
    (p w rank : Fin d → ℝ) {C lam : ℝ}
    (hC : 0 < C) (hlam : 0 < lam)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w i ^ 2 = 2 * C ^ 2 * rank i)
    (hprofile : waterProfile p rank (waterTau C lam) = 1) :
    coordinateEnergy w (fun i => softCoordinate (p i) (w i) lam) = C ^ 2 := by
  have hnormalized :
      coordinateEnergy w (fun i => softCoordinate (p i) (w i) lam) / C ^ 2 = 1 := by
    rw [coordinateEnergy, Finset.sum_div]
    calc
      (∑ i, ((1 / 2 : ℝ) * softCoordinate (p i) (w i) lam ^ 2 +
          w i * |softCoordinate (p i) (w i) lam|) / C ^ 2) =
          ∑ i, max 0 (waterTau C lam * p i ^ 2 - rank i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact softCoordinate_energy_div_eq_waterTerm hC hlam (hw0 i) (hw i)
      _ = 1 := hprofile
  apply (div_eq_one_iff_eq (pow_ne_zero 2 hC.ne')).mp hnormalized

/-- Paper-facing exact-LMO endpoint. -/
theorem softCoordinate_is_LMO {d : ℕ}
    (p w : Fin d → ℝ) {C lam : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hlam : 0 < lam)
    (hboundary : coordinateEnergy w (fun i => softCoordinate (p i) (w i) lam) = C ^ 2) :
    ∀ x : Fin d → ℝ, coordinateEnergy w x ≤ C ^ 2 →
      (∑ i, p i * softCoordinate (p i) (w i) lam) ≤ ∑ i, p i * x i := by
  intro x hx
  let z : Fin d → ℝ := fun i => softCoordinate (p i) (w i) lam
  have hsubgrad : coordinateEnergy w z +
      ∑ i, (-p i / lam) * (x i - z i) ≤ coordinateEnergy w x := by
    unfold coordinateEnergy
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => softCoordinate_subgradient (hw i) hlam (x i))
  have hnormal : ∑ i, (-p i / lam) * (x i - z i) ≤ 0 := by
    rw [hboundary] at hsubgrad
    linarith
  have hscale :
      (∑ i, p i * (x i - z i)) =
        -lam * ∑ i, (-p i / lam) * (x i - z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hlam.ne']
  have hgap : 0 ≤ ∑ i, p i * (x i - z i) := by
    rw [hscale]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hlam.le) hnormal
  dsimp [z] at hgap ⊢
  have hsumdiff :
      (∑ i, p i * (x i - softCoordinate (p i) (w i) lam)) =
        (∑ i, p i * x i) - ∑ i, p i * softCoordinate (p i) (w i) lam := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsumdiff] at hgap
  linarith

/-- The soft-threshold minimizer is unique. -/
theorem softCoordinate_unique_LMO {d : ℕ}
    (p w : Fin d → ℝ) {C lam : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hlam : 0 < lam)
    (hboundary : coordinateEnergy w (fun i => softCoordinate (p i) (w i) lam) = C ^ 2)
    {x : Fin d → ℝ} (hx : coordinateEnergy w x ≤ C ^ 2)
    (hvalue : (∑ i, p i * x i) =
      ∑ i, p i * softCoordinate (p i) (w i) lam) :
    x = fun i => softCoordinate (p i) (w i) lam := by
  let z : Fin d → ℝ := fun i => softCoordinate (p i) (w i) lam
  have hstrong : coordinateEnergy w z +
      ∑ i, (-p i / lam) * (x i - z i) +
      (1 / 2 : ℝ) * ∑ i, (x i - z i) ^ 2 ≤ coordinateEnergy w x := by
    unfold coordinateEnergy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum
      (fun i _ => softCoordinate_strong_subgradient (p := p i) (hw i) hlam (x i))
  have hlinear : ∑ i, p i * (x i - z i) = 0 := by
    rw [show (∑ i, p i * (x i - z i)) =
        (∑ i, p i * x i) - ∑ i, p i * z i by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    dsimp [z]
    linarith
  have hnormal : ∑ i, (-p i / lam) * (x i - z i) = 0 := by
    have hscale : (∑ i, p i * (x i - z i)) =
        -lam * ∑ i, (-p i / lam) * (x i - z i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hlam.ne']
    rw [hlinear] at hscale
    exact (mul_eq_zero.mp hscale.symm).resolve_left (neg_ne_zero.mpr hlam.ne')
  have hsumsq_le : (∑ i, (x i - z i) ^ 2) ≤ 0 := by
    rw [hboundary, hnormal] at hstrong
    nlinarith
  have hsumsq0 : (∑ i, (x i - z i) ^ 2) = 0 :=
    le_antisymm hsumsq_le (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hall : ∀ i, (x i - z i) ^ 2 = 0 := by
    have hiff := Finset.sum_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset (Fin d))) (f := fun i => (x i - z i) ^ 2)
      (fun i _ => sq_nonneg _)
    exact fun i => (hiff.mp hsumsq0) i (Finset.mem_univ i)
  funext i
  have : x i - z i = 0 := by nlinarith [hall i]
  dsimp [z] at this ⊢
  linarith

/-- One-based rank attached to a coordinate by a hidden permutation. -/
def permutedRank {d : ℕ} (π : Equiv.Perm (Fin d)) (i : Fin d) : ℝ :=
  ((π i).val + 1 : ℕ)

lemma permutedHardWeight_sq_rank {d : ℕ} (π : Equiv.Perm (Fin d)) (i : Fin d) :
    permutedHardWeight d π i ^ 2 =
      2 * hardC d ^ 2 * permutedRank π i := by
  rw [permutedHardWeight, hardWeight_sq]
  dsimp [permutedRank]
  push_cast
  ring

/-- Fully existential exact-LMO theorem: every nonzero query has a positive,
uniquely determined water level and an associated soft-threshold minimizer. -/
theorem exists_softCoordinate_LMO {d : ℕ}
    (p w rank : Fin d → ℝ) {C : ℝ}
    (hC : 0 < C) (hw0 : ∀ i, 0 ≤ w i)
    (hrank : ∀ i, 0 ≤ rank i)
    (hw : ∀ i, w i ^ 2 = 2 * C ^ 2 * rank i)
    (hp : ∃ i, p i ≠ 0) :
    ∃ tau lam : ℝ,
      0 < tau ∧ 0 < lam ∧
      waterProfile p rank tau = 1 ∧ waterTau C lam = tau ∧
      ∀ x : Fin d → ℝ, coordinateEnergy w x ≤ C ^ 2 →
        (∑ i, p i * softCoordinate (p i) (w i) lam) ≤ ∑ i, p i * x i := by
  rcases existsUnique_waterLevel p rank hrank hp with ⟨tau, htau, _⟩
  let lam := multiplierOfTau C tau
  have hlam : 0 < lam := multiplierOfTau_pos hC htau.1
  have hwater : waterTau C lam = tau := waterTau_multiplierOfTau hC htau.1
  have hprofileLam : waterProfile p rank (waterTau C lam) = 1 := by
    rw [hwater]
    exact htau.2
  have hboundary := softCoordinate_boundary_of_waterProfile
    p w rank hC hlam hw0 hw hprofileLam
  refine ⟨tau, lam, htau.1, hlam, htau.2, hwater, ?_⟩
  exact softCoordinate_is_LMO p w hw0 hlam hboundary

/-- Concrete paper-facing LMO theorem for every hidden permutation. -/
theorem concrete_exists_softCoordinate_LMO {d : ℕ}
    (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ)
    (hp : ∃ i, p i ≠ 0) :
    ∃ tau lam : ℝ,
      0 < tau ∧ 0 < lam ∧
      waterProfile p (permutedRank π) tau = 1 ∧
      waterTau (hardC d) lam = tau ∧
      ∀ x : Fin d → ℝ,
        coordinateEnergy (permutedHardWeight d π) x ≤ hardC d ^ 2 →
        (∑ i, p i * softCoordinate (p i) (permutedHardWeight d π i) lam) ≤
          ∑ i, p i * x i := by
  apply exists_softCoordinate_LMO p (permutedHardWeight d π) (permutedRank π)
    (hardC_pos d) (fun i => hardWeight_nonneg d (π i))
    (fun i => by dsimp [permutedRank]; positivity)
    (permutedHardWeight_sq_rank π) hp

end Lemmata.DistributionalLowerBounds.Core.Distributional
