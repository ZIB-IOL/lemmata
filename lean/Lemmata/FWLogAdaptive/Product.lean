module

public import Lemmata.FWLogAdaptive.Statement
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# The step sizes and the cumulative-product bound (Lemma 3.1)

For `δ = g(S) - ε ≥ 1`, Bernoulli's inequality `1 - δ s ≤ (1 - s)^δ` bounds every factor
`(i + ε)/(i + g(i)) ≤ 1 - δ/(i + g(S))` by `((i - 1 + g(S))/(i + g(S)))^δ`, the product telescopes
to `((S - 1 + g(S))/(t + g(S)))^δ`, and monotonicity of `g` gives
`(S - 1 + g(S))/(t + g(S)) ≤ η_t/η_{S-1}`.
-/

namespace Lemmata.FWLogAdaptive

open Lemmata.FrankWolfe Lemmata.FWAffineOpenLoop

theorem etaG_pos {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (t : ℕ) : 0 < etaG g t := by
  unfold etaG; have := hg2 t; positivity

theorem etaG_le_one {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (t : ℕ) : etaG g t ≤ 1 := by
  unfold etaG
  have := hg2 t
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  rw [div_le_one (by positivity)]; linarith

theorem etaG_mem {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (t : ℕ) : etaG g t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(etaG_pos hg2 t).le, etaG_le_one hg2 t⟩

/-- Assumption A2 says that the step sizes are nonincreasing. -/
theorem etaG_succ_le {g : ℕ → ℝ} (hg : IsAdmissible g) (t : ℕ) : etaG g (t + 1) ≤ etaG g t := by
  have h2 := hg.2.2 t
  have hg0 := hg.1 t
  have hg1 := hg.1 (t + 1)
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  unfold etaG
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h2
  nlinarith

theorem etaG_anti {g : ℕ → ℝ} (hg : IsAdmissible g) : Antitone (etaG g) :=
  antitone_nat_of_succ_le (etaG_succ_le hg)

/-- The factors of Lemma 3.1 are `(i + ε)/(i + g(i))`. -/
theorem factor_eq {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (i : ℕ) (ε : ℝ) :
    1 - (1 - ε / g i) * etaG g i = ((i : ℝ) + ε) / (i + g i) := by
  have := hg2 i
  have ht : (0 : ℝ) ≤ i := i.cast_nonneg
  have h1 : (i : ℝ) + g i ≠ 0 := by positivity
  have h2 : g i ≠ 0 := by positivity
  unfold etaG; field_simp; ring

theorem factor_nonneg {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (i : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ 1 - (1 - ε / g i) * etaG g i := by
  rw [factor_eq hg2]; have := hg2 i; positivity

/-- Bernoulli's inequality for one factor. -/
theorem factor_le {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (hmono : Monotone g) {S i : ℕ} (hSi : S ≤ i)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ g S - 1) :
    1 - (1 - ε / g i) * etaG g i ≤ (((i : ℝ) - 1 + g S) / (i + g S)) ^ (g S - ε) := by
  rw [factor_eq hg2]
  have hgS := hg2 S
  have hk : g S ≤ g i := hmono hSi
  have ht : (0 : ℝ) ≤ i := i.cast_nonneg
  have h2 : ((i : ℝ) + ε) / (i + g i) ≤ ((i : ℝ) + ε) / (i + g S) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hpos : 0 < (i : ℝ) + g S := by positivity
  have hs : (-1 : ℝ) ≤ -1 / ((i : ℝ) + g S) := by
    rw [le_div_iff₀ hpos]; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs (show 1 ≤ g S - ε by linarith)
  have e2 : 1 + (g S - ε) * (-1 / ((i : ℝ) + g S)) = ((i : ℝ) + ε) / (i + g S) := by
    field_simp; ring
  have e3 : 1 + -1 / ((i : ℝ) + g S) = ((i : ℝ) - 1 + g S) / (i + g S) := by
    field_simp; ring
  rw [e2, e3] at hb
  linarith

/-- The telescoped product. -/
theorem prod_le_closed {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (hmono : Monotone g) {S : ℕ}
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ g S - 1) :
    ∀ t, S ≤ t → ∏ i ∈ Finset.Icc S t, (1 - (1 - ε / g i) * etaG g i) ≤
      (((S : ℝ) - 1 + g S) / (t + g S)) ^ (g S - ε) := by
  have hgS := hg2 S
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.prod_singleton]; exact factor_le hg2 hmono le_rfl hε0 hε
  | succ t ht ih =>
    rw [Finset.prod_Icc_succ_top (by omega : S ≤ t + 1)]
    have hf := factor_le hg2 hmono (by omega : S ≤ t + 1) hε0 hε
    have hf0 := factor_nonneg hg2 (t + 1) hε0
    have hS1 : (0 : ℝ) ≤ (S : ℝ) - 1 + g S := by
      have : (0 : ℝ) ≤ S := S.cast_nonneg
      linarith
    have htr : (0 : ℝ) ≤ t := t.cast_nonneg
    calc (∏ i ∈ Finset.Icc S t, (1 - (1 - ε / g i) * etaG g i)) *
          (1 - (1 - ε / g (t + 1)) * etaG g (t + 1))
        ≤ (((S : ℝ) - 1 + g S) / (t + g S)) ^ (g S - ε) *
            ((((t + 1 : ℕ) : ℝ) - 1 + g S) / ((t + 1 : ℕ) + g S)) ^ (g S - ε) :=
          mul_le_mul ih hf hf0 (Real.rpow_nonneg (by positivity) _)
      _ = (((S : ℝ) - 1 + g S) / ((t + 1 : ℕ) + g S)) ^ (g S - ε) := by
          rw [← Real.mul_rpow (by positivity) (by push_cast; apply div_nonneg <;> linarith)]
          congr 1
          push_cast
          have h1 : (t : ℝ) + g S ≠ 0 := by positivity
          have h2 : (t : ℝ) + 1 + g S ≠ 0 := by positivity
          field_simp
          ring

/-- Monotonicity of `g` gives `(S - 1 + g(S))/(t + g(S)) ≤ η_t/η_{S-1}`. -/
theorem ratio_le_eta {g : ℕ → ℝ} (hg2 : ∀ t, 2 ≤ g t) (hmono : Monotone g) {S t : ℕ}
    (hS : 1 ≤ S) (hSt : S ≤ t) :
    ((S : ℝ) - 1 + g S) / (t + g S) ≤ etaG g t / etaG g (S - 1) := by
  have hgS := hg2 S
  have hgt : g S ≤ g t := hmono hSt
  have hgS1 : g (S - 1) ≤ g S := hmono (Nat.sub_le S 1)
  have hg1 := hg2 (S - 1)
  have hgt2 := hg2 t
  have htr : (0 : ℝ) ≤ t := t.cast_nonneg
  have hSr : ((S - 1 : ℕ) : ℝ) = (S : ℝ) - 1 := by rw [Nat.cast_sub hS]; simp
  have hS0 : (0 : ℝ) ≤ (S : ℝ) - 1 := by
    have : (1 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  -- `η_t ≥ g(S)/(t + g(S))` and `η_{S-1} ≤ g(S)/(S - 1 + g(S))`
  have h1 : g S / (t + g S) ≤ etaG g t := by
    unfold etaG
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : etaG g (S - 1) ≤ g S / ((S : ℝ) - 1 + g S) := by
    unfold etaG
    rw [hSr, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hpos1 : 0 < etaG g (S - 1) := etaG_pos hg2 _
  calc ((S : ℝ) - 1 + g S) / (t + g S) = (g S / (t + g S)) / (g S / ((S : ℝ) - 1 + g S)) := by
        have : (S : ℝ) - 1 + g S ≠ 0 := by positivity
        have : (t : ℝ) + g S ≠ 0 := by positivity
        have : g S ≠ 0 := by positivity
        field_simp
    _ ≤ etaG g t / etaG g (S - 1) :=
        div_le_div₀ (etaG_pos hg2 t).le h1 hpos1 h2

theorem product_bound_bound (g : ℕ → ℝ) (S t : ℕ) (ε : ℝ) (hg2 : ∀ t, 2 ≤ g t)
    (hmono : Monotone g) (hS : 1 ≤ S) (hSt : S ≤ t) (hε0 : 0 < ε) (hε : ε ≤ g S - 1) :
    ∏ i ∈ Finset.Icc S t, (1 - (1 - ε / g i) * etaG g i) ≤
      (etaG g t / etaG g (S - 1)) ^ (g S - ε) := by
  have hgS := hg2 S
  have hS0 : (0 : ℝ) ≤ (S : ℝ) - 1 + g S := by
    have : (0 : ℝ) ≤ S := S.cast_nonneg
    linarith
  have htr : (0 : ℝ) ≤ t := t.cast_nonneg
  exact le_trans (prod_le_closed hg2 hmono hε0 hε t hSt)
    (Real.rpow_le_rpow (by positivity) (ratio_le_eta hg2 hmono hS hSt) (by linarith))

/-- The log-adaptive choice satisfies Assumptions A1 and A2. -/
theorem logStep_isAdmissible : IsAdmissible logStep := by
  refine ⟨fun t => ?_, fun s t hst => ?_, fun t => ?_⟩
  · unfold logStep
    have ht : (0 : ℝ) ≤ t := t.cast_nonneg
    have : 0 ≤ Real.log ((t : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
  · unfold logStep
    have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hle : ((s : ℝ) + 1) ≤ (t : ℝ) + 1 := by linarith
    linarith [Real.log_le_log hs hle]
  · unfold logStep
    push_cast
    have ht : (0 : ℝ) ≤ t := t.cast_nonneg
    have hl1 : 0 ≤ Real.log ((t : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hl2 : 0 ≤ Real.log ((t : ℝ) + 1 + 1) := Real.log_nonneg (by linarith)
    -- `log(t + 2) - log(t + 1) ≤ 1/(t + 1)`
    have hdiff : Real.log ((t : ℝ) + 1 + 1) - Real.log ((t : ℝ) + 1) ≤ 1 / ((t : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((t : ℝ) + 1 + 1) / ((t : ℝ) + 1) by
        positivity)
      have e : ((t : ℝ) + 1 + 1) / ((t : ℝ) + 1) - 1 = 1 / ((t : ℝ) + 1) := by field_simp; ring
      linarith
    have hfrac : (t : ℝ) * (1 / ((t : ℝ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hdiff ht
    nlinarith

namespace Proof

theorem product_bound : ProductBound := product_bound_bound

theorem logStep_admissible : LogStepAdmissible := logStep_isAdmissible

end Proof

end Lemmata.FWLogAdaptive
