module

public import Lemmata.FWAffineOpenLoop.Weak

@[expose] public section

/-!
# Gaps growth: Theorems 5.1 and 5.2

From the threshold `S` on, `(η_i M)^r ≤ m/2`, and Theorem 3.1 gives `h_i ≤ η_i M`. A step whose
primal gap exceeds `δ_i = (η_i M/m)^{1/(1-r)}` then contracts the primal gap by `1 - η_i`, and a
step below `δ_i` leaves at most `δ_i + η_i² M/2`. The argument of Theorem 3.4 with Lemma 3.3 gives
the rate.
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FrankWolfe Lemmata.FWOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 5.2.** -/
theorem relaxed_gaps_bound {C : Set E} {f : E → ℝ} {M m r : ℝ} {ℓ S : ℕ} {x v : ℕ → E}
    {xStar : E} (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hm : 0 < m) (hℓ : 2 ≤ ℓ)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hg0 : IsStrongGrowth C f M 0)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t))
    (hS : max 1 ⌈(2 : ℝ) ^ (1 / r) * ℓ * M / m ^ (1 / r) - ℓ⌉₊ ≤ S)
    (hrel : IsRelaxedGapsGrowth C f x v (fun t => (eta ℓ t * M / m) ^ (1 / (1 - r))) m r S) :
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max ((f (x S) - f xStar) * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ)
        (eta ℓ ((t : ℤ) - 1) ^ (min (ℓ : ℝ) (min (1 / (1 - r)) 2)) *
          ((M / m) ^ (1 / (1 - r)) + M / 2)) := by
  obtain ⟨hr0, hr1⟩ := hr
  have hℓ1 : 1 ≤ ℓ := by omega
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have hS1 : 1 ≤ S := le_trans (le_max_left _ _) hS
  have h1r : 0 < 1 - r := by linarith
  set a : ℝ := 1 / (1 - r) with ha
  have ha0 : 0 < a := by positivity
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  -- from `S` on, `(η_i M)^r ≤ m/2`
  have hηM : ∀ i, S ≤ i → (eta ℓ i * M) ^ r ≤ m / 2 := by
    intro i hi
    have h1 : ⌈(2 : ℝ) ^ (1 / r) * ℓ * M / m ^ (1 / r) - ℓ⌉₊ ≤ i :=
      le_trans (le_trans (le_max_right _ _) hS) hi
    have h2 := Nat.le_ceil ((2 : ℝ) ^ (1 / r) * ℓ * M / m ^ (1 / r) - ℓ)
    have h3 : ((⌈(2 : ℝ) ^ (1 / r) * ℓ * M / m ^ (1 / r) - ℓ⌉₊ : ℕ) : ℝ) ≤ i := by exact_mod_cast h1
    have h2r : (0 : ℝ) < 2 ^ (1 / r) := by positivity
    have hmr : (0 : ℝ) < m ^ (1 / r) := Real.rpow_pos_of_pos hm _
    have hle : eta ℓ i * M ≤ (m / 2) ^ (1 / r) := by
      rw [eta_nat, Real.div_rpow hm.le (by norm_num), div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) h2r]
      have : (2 : ℝ) ^ (1 / r) * ℓ * M / m ^ (1 / r) ≤ i + ℓ := by linarith
      rw [div_le_iff₀ hmr] at this
      nlinarith
    calc (eta ℓ i * M) ^ r ≤ ((m / 2) ^ (1 / r)) ^ r :=
          Real.rpow_le_rpow (by have := (eta_mem ℓ hℓ1 i).1; positivity) hle hr0.le
      _ = m / 2 := by rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr0.ne',
          Real.rpow_one]
  -- `h_i ≤ η_i M` (Theorem 3.1)
  have hrate : ∀ i, 1 ≤ i → f (x i) - f xStar ≤ eta ℓ i * M := fun i hi =>
    le_trans (pd_ge_subopt hconv hdiff hxs hrun i)
      (pd_rate_zero_bound hconv.1 hM.le hℓ hg0 hrun i hi)
  -- the two kinds of steps
  have hsmall : ∀ i, S ≤ i → f (x i) - f xStar ≤ (eta ℓ i * M / m) ^ a →
      f (x (i + 1)) - f xStar ≤ eta ℓ i ^ min a 2 * ((M / m) ^ a + M / 2) := by
    intro i hi hle
    have h1 := weak_small_step (xStar := xStar) hconv hg0 hrun i
    have hη0 := (eta_mem ℓ hℓ1 i).1
    have hη1 := (eta_mem ℓ hℓ1 i).2
    have e1 : (eta ℓ i * M / m) ^ a = eta ℓ i ^ a * (M / m) ^ a := by
      rw [← Real.mul_rpow hη0 (by positivity)]; ring_nf
    have h2 : eta ℓ i ^ a ≤ eta ℓ i ^ min a 2 := by
      rcases hη0.eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow ha0.ne', Real.zero_rpow (lt_min ha0 (by norm_num)).ne']
      · exact Real.rpow_le_rpow_of_exponent_ge hpos hη1 (min_le_left _ _)
    have h3 : eta ℓ i ^ 2 ≤ eta ℓ i ^ min a 2 := by
      rcases hη0.eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow (lt_min ha0 (by norm_num)).ne']; norm_num
      · rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_ge hpos hη1 (min_le_right _ _)
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (M / m) ^ a)
    have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ M / 2)
    rw [e1] at hle
    nlinarith
  have hbig : ∀ i, S ≤ i → (eta ℓ i * M / m) ^ a < f (x i) - f xStar →
      f (x (i + 1)) - f xStar ≤ (1 - eta ℓ i) * (f (x i) - f xStar) := by
    intro i hi hgt
    have hi1 : 1 ≤ i := le_trans hS1 hi
    have hη0 := (eta_mem ℓ hℓ1 i).1
    set h := f (x i) - f xStar with hh
    have hpos : 0 < h := lt_of_le_of_lt (Real.rpow_nonneg (by positivity) _) hgt
    have hgap : m * h ^ (1 - r) ≤ fderiv ℝ f (x i) (x i - v i) := by
      rcases hrel i hi xStar hxs with hlt | hge
      · exact absurd hlt (not_lt.mpr hgt.le)
      · exact hge
    have h1 := f_step hrun i
    obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
    have h3 := hg0 (x i) (hmem i) (v i) hvC hvmin (eta ℓ i) hγ
    rw [Real.rpow_zero, mul_one, ← hx] at h3
    -- `η M ≤ m h^{1-r}`
    have hA : eta ℓ i * M / m ≤ h ^ (1 - r) := by
      have hb : 0 ≤ eta ℓ i * M / m := by positivity
      have := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hgt.le h1r.le
      rwa [← Real.rpow_mul hb, ha, one_div_mul_cancel h1r.ne', Real.rpow_one] at this
    have hB : eta ℓ i * M ≤ m * h ^ (1 - r) := by
      rw [div_le_iff₀ hm] at hA; linarith
    -- `h^{1-r} ≥ (2/m) h`
    have hC : 2 / m * h ≤ h ^ (1 - r) := by
      have hηMpos : 0 < eta ℓ i * M := by
        have : 0 < eta ℓ i := by rw [eta_nat]; positivity
        positivity
      have h4 : (eta ℓ i * M) ^ (-r) ≤ h ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos hpos (hrate i hi1) (by linarith)
      have h5 : 2 / m ≤ (eta ℓ i * M) ^ (-r) := by
        rw [Real.rpow_neg hηMpos.le, le_inv_comm₀ (by positivity) (by positivity), inv_div]
        exact hηM i hi
      have e : h ^ (1 - r) = h * h ^ (-r) := by
        rw [← Real.rpow_one_add' hpos.le (by linarith)]; ring_nf
      rw [e]
      nlinarith
    have hη0' : 0 ≤ eta ℓ i := hη0
    have h6 := mul_le_mul_of_nonneg_left hgap hη0'
    have h7 := mul_le_mul_of_nonneg_left hB hη0'
    have h8 := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ eta ℓ i * m / 2)
    have e2 : eta ℓ i * m / 2 * (2 / m * h) = eta ℓ i * h := by field_simp
    nlinarith
  have hc0 : ∀ i : ℕ, 0 ≤ 1 - eta ℓ i := fun i => by linarith [(eta_mem ℓ hℓ1 i).2]
  set term : ℕ → ℝ := fun R => if R = S then f (x S) - f xStar else
    eta ℓ ((R - 1 : ℕ) : ℤ) ^ min a 2 * ((M / m) ^ a + M / 2) with hterm
  have hinv : ∀ t, S ≤ t → ∃ R, S ≤ R ∧ R ≤ t ∧
      f (x t) - f xStar ≤ term R * ∏ i ∈ Finset.Ico R t, (1 - eta ℓ i) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨S, le_rfl, le_rfl, by simp [hterm]⟩
    | succ t ht ih =>
      obtain ⟨R, hSR, hRt, hR⟩ := ih
      by_cases hle : f (x t) - f xStar ≤ (eta ℓ t * M / m) ^ a
      · refine ⟨t + 1, by omega, le_rfl, ?_⟩
        rw [Finset.Ico_self, Finset.prod_empty, mul_one]
        simp only [hterm, show t + 1 ≠ S by omega, ↓reduceIte, Nat.add_sub_cancel]
        exact hsmall t ht hle
      · refine ⟨R, hSR, by omega, ?_⟩
        rw [Finset.prod_Ico_succ_top hRt]
        calc f (x (t + 1)) - f xStar ≤ (1 - eta ℓ t) * (f (x t) - f xStar) :=
              hbig t ht (lt_of_not_ge hle)
          _ ≤ (1 - eta ℓ t) * (term R * ∏ i ∈ Finset.Ico R t, (1 - eta ℓ i)) :=
              mul_le_mul_of_nonneg_left hR (hc0 t)
          _ = term R * ((∏ i ∈ Finset.Ico R t, (1 - eta ℓ i)) * (1 - eta ℓ t)) := by ring
  intro t ht
  obtain ⟨R, hSR, hRt, hR⟩ := hinv t ht
  have hR1 : 1 ≤ R := le_trans hS1 hSR
  set q := eta ℓ ((t : ℤ) - 1) with hq
  have hq0 : 0 < q := eta_pos_nat ℓ hℓ1 t (le_trans hR1 hRt)
  set p := eta ℓ ((R : ℤ) - 1) with hp
  have hp0 : 0 < p := eta_pos_nat ℓ hℓ1 R hR1
  have hp1 : p ≤ 1 := eta_pred_le_one ℓ hℓ1 R hR1
  have hqp : q ≤ p := eta_pred_anti ℓ hℓ1 hR1 hRt
  -- the product over `[R, t)` with Lemma 3.3
  have hprod : ∏ i ∈ Finset.Ico R t, (1 - eta ℓ i) ≤ (q / p) ^ ℓ := by
    rcases eq_or_lt_of_le hRt with heq | hlt
    · subst heq; rw [Finset.Ico_self, Finset.prod_empty, div_self hp0.ne', one_pow]
    · have hIco : Finset.Ico R t = Finset.Icc R (t - 1) := by
        ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [hIco]
      have h := product_bound_closed ℓ R hℓ1 hR1 (t - 1) (by omega)
      rwa [← eta_pred_ratio ℓ R t hℓ1 hR1 (by omega)] at h
  have hprod0 : 0 ≤ ∏ i ∈ Finset.Ico R t, (1 - eta ℓ i) := Finset.prod_nonneg fun i _ => hc0 i
  by_cases hRS : R = S
  · subst hRS
    simp only [hterm, ↓reduceIte] at hR
    have hS0 : 0 ≤ f (x R) - f xStar := sub_nonneg.mpr (hxs.2 _ (hmem R))
    refine le_max_of_le_left (le_trans hR (mul_le_mul_of_nonneg_left hprod hS0))
  · simp only [hterm, hRS, ↓reduceIte] at hR
    have hcast : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by omega
    rw [hcast] at hR
    refine le_max_of_le_right ?_
    set b : ℝ := min a 2 with hb
    have hmix := rpow_mix_le (a := b) (b := (ℓ : ℝ)) hq0 hqp hp1
    rw [Real.rpow_natCast] at hmix
    calc f (x t) - f xStar ≤ p ^ b * ((M / m) ^ a + M / 2) * ∏ i ∈ Finset.Ico R t, (1 - eta ℓ i) :=
          hR
      _ ≤ p ^ b * ((M / m) ^ a + M / 2) * (q / p) ^ ℓ :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (p ^ b * (q / p) ^ ℓ) * ((M / m) ^ a + M / 2) := by ring
      _ ≤ q ^ (min (ℓ : ℝ) b) * ((M / m) ^ a + M / 2) :=
          mul_le_mul_of_nonneg_right hmix (by positivity)

/-- Gaps growth gives relaxed gaps growth along every run, for every `δ` and threshold. -/
theorem gaps_relaxed {C : Set E} {f : E → ℝ} {m r : ℝ} {x v : ℕ → E} {γ : ℕ → ℝ}
    (hC : Convex ℝ C) (hgg : IsGapsGrowth C f m r) (hrun : IsFWRun C (fderiv ℝ f) x v γ)
    (δ : ℕ → ℝ) (S : ℕ) : IsRelaxedGapsGrowth C f x v δ m r S := by
  intro t _ xStar hxs
  obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 t
  exact Or.inr (hgg (x t) (Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v γ hC hrun t) (v t) hvC
    hvmin xStar hxs)

namespace Proof

theorem weak_rate : WeakRate.{u} := by
  intro E _ _ C f M r ε ℓ x v xStar hconv hdiff hxs hM hℓ hr hε hg0 hw hrun
  exact ⟨weak_rate_bound hconv hdiff hxs hM hℓ hr hε hg0 hw hrun,
    weak_dichotomy hconv hdiff hxs hM hℓ hr hε hw hrun⟩

theorem weak_restart : WeakRestart.{u} := by
  intro E _ _ C f M r ε ℓ x v xStar hconv hdiff hxs hM hℓ hr hℓa hε hw hrun R hR
  exact weak_restart_bound hconv hdiff hxs hM hℓ hr hℓa hε hw hrun R hR

theorem relaxed_gaps_rate : RelaxedGapsRate.{u} := by
  intro E _ _ C f M m r ℓ S x v xStar hconv hdiff hxs hM hm hℓ hr hg0 hrun hS hrel t ht
  exact relaxed_gaps_bound hconv hdiff hxs hM hm hℓ hr hg0 hrun hS hrel t ht

theorem gaps_rate : GapsRate.{u} := by
  intro E _ _ C f M m r ℓ x v xStar hconv hdiff hxs hM hm hℓ hr hg0 hgg hrun S t ht
  exact relaxed_gaps_bound hconv hdiff hxs hM hm hℓ hr hg0 hrun le_rfl
    (gaps_relaxed hconv.1 hgg hrun _ _) t ht

end Proof

end Lemmata.FWAffineOpenLoop
