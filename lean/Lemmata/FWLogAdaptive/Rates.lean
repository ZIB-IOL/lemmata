module

public import Lemmata.FWLogAdaptive.Steps

@[expose] public section

/-!
# Theorems 3.2 and 4.1

The argument of Theorems 3.4 and 4.1 of the affine-invariant entry, with `g(i)` in place of `ℓ`:
for every `t ≥ S` there is `R ∈ [S, t]` such that the gap at `t` is at most the gap at `R`
(a small value when `R > S`) times the product of the contractions over `[R, t)`, and Lemma 3.1
bounds the product. The log-adaptive cases take `ε = 1` and `S = ⌈exp(1/(1-r))⌉`, so that
`g(S) - 1 ≥ 1/(1-r)`.
-/

namespace Lemmata.FWLogAdaptive

open Lemmata.FrankWolfe Lemmata.FWAffineOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product over `[R, t)`, for `S ≤ R ≤ t`. -/
theorem stretch_bound {g : ℕ → ℝ} (hg : IsAdmissible g) {S R t : ℕ} (hS : 1 ≤ S) (hSR : S ≤ R)
    (hRt : R ≤ t) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ g S - 1) :
    ∏ i ∈ Finset.Ico R t, (1 - (1 - ε / g i) * etaG g i) ≤
      (etaG g (t - 1) / etaG g (R - 1)) ^ (g S - ε) := by
  have hanti := etaG_anti hg
  obtain ⟨hg2, hmono, -⟩ := hg
  have hpos : 0 < etaG g (R - 1) := etaG_pos hg2 _
  rcases eq_or_lt_of_le hRt with heq | hlt
  · subst heq
    rw [Finset.Ico_self, Finset.prod_empty, div_self hpos.ne', Real.one_rpow]
  · have hIco : Finset.Ico R t = Finset.Icc R (t - 1) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco]
    have hgSR : g S ≤ g R := hmono hSR
    have h1 := product_bound_bound g R (t - 1) ε hg2 hmono (le_trans hS hSR) (by omega) hε0
      (by linarith)
    have hq0 : 0 < etaG g (t - 1) / etaG g (R - 1) := div_pos (etaG_pos hg2 _) hpos
    have hq1 : etaG g (t - 1) / etaG g (R - 1) ≤ 1 := by
      rw [div_le_one hpos]
      exact hanti (by omega)
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by linarith))

/-- **Theorem 3.2.** -/
theorem strong_rate_bound {C : Set E} {f : E → ℝ} {g : ℕ → ℝ} {M r ε : ℝ} {S : ℕ}
    {x v : ℕ → E} {xStar : E} (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hg : IsAdmissible g) (hM : 0 < M)
    (hr : r ∈ Set.Ico (0 : ℝ) 1) (hgr : IsStrongGrowth C f M r) (hS : 1 ≤ S) (hε0 : 0 < ε)
    (hε : ε ≤ g S - 1) (hrun : IsFWRun C (fderiv ℝ f) x v (etaG g)) :
    ∀ t : ℕ, S ≤ t → pdGap f x v t ≤
      max (pdGap f x v S * (etaG g (t - 1) / etaG g (S - 1)) ^ (g S - ε))
        ((M * g (t - 1) / (2 * ε)) ^ (1 / (1 - r)) *
          etaG g (t - 1) ^ (min (g S - ε) (1 / (1 - r)))) := by
  have hg' := hg
  obtain ⟨hg2, hmono, -⟩ := hg
  obtain ⟨hr0, hr1⟩ := hr
  have h1r : 0 < 1 - r := by linarith
  set a : ℝ := 1 / (1 - r) with ha
  have ha0 : 0 < a := by positivity
  have hεi : ∀ i, S ≤ i → ε ≤ g i := fun i hi => by have := hmono hi; linarith
  set c : ℕ → ℝ := fun i => 1 - (1 - ε / g i) * etaG g i with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => factor_nonneg hg2 i hε0
  set X : ℕ → ℝ := fun i => (M * g i * etaG g i / (2 * ε)) ^ a with hX
  set term : ℕ → ℝ := fun R => if R = S then pdGap f x v S else X (R - 1) with hterm
  have hinv : ∀ t, S ≤ t → ∃ R, S ≤ R ∧ R ≤ t ∧
      pdGap f x v t ≤ term R * ∏ i ∈ Finset.Ico R t, c i := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨S, le_rfl, le_rfl, by simp [hterm]⟩
    | succ t ht ih =>
      obtain ⟨R, hSR, hRt, hR⟩ := ih
      have hst := strong_step hconv.1 hM hg2 ⟨hr0, hr1⟩ hε0 hgr hrun t (hεi t ht)
      by_cases hsmall : fderiv ℝ f (x t) (x t - v t) ≤ X t
      · refine ⟨t + 1, by omega, le_rfl, ?_⟩
        rw [Finset.Ico_self, Finset.prod_empty, mul_one]
        simp only [hterm, show t + 1 ≠ S by omega, ↓reduceIte, Nat.add_sub_cancel]
        exact hst.1 hsmall
      · refine ⟨R, hSR, by omega, ?_⟩
        rw [Finset.prod_Ico_succ_top hRt]
        have h2 := hst.2 (lt_of_not_ge hsmall)
        have hpg := pd_le_gap f x v t
        have hgi := hg2 t
        have hcoef : 0 ≤ (1 - ε / g t) * etaG g t := by
          apply mul_nonneg _ (etaG_pos hg2 t).le
          rw [sub_nonneg, div_le_one (by linarith)]; exact hεi t ht
        have h3 : pdGap f x v (t + 1) ≤ c t * pdGap f x v t := by
          have := mul_le_mul_of_nonneg_left hpg hcoef
          simp only [hc]; nlinarith
        calc pdGap f x v (t + 1) ≤ c t * pdGap f x v t := h3
          _ ≤ c t * (term R * ∏ i ∈ Finset.Ico R t, c i) := mul_le_mul_of_nonneg_left hR (hc0 t)
          _ = term R * ((∏ i ∈ Finset.Ico R t, c i) * c t) := by ring
  intro t ht
  obtain ⟨R, hSR, hRt, hR⟩ := hinv t ht
  have hprod := stretch_bound hg' hS hSR hRt hε0 hε
  have hprod0 : 0 ≤ ∏ i ∈ Finset.Ico R t, c i := Finset.prod_nonneg fun i _ => hc0 i
  set q := etaG g (t - 1) with hq
  set p := etaG g (R - 1) with hp
  have hq0 : 0 < q := etaG_pos hg2 _
  have hp0 : 0 < p := etaG_pos hg2 _
  have hp1 : p ≤ 1 := etaG_le_one hg2 _
  have hqp : q ≤ p := etaG_anti hg' (by omega)
  have hgt0 : 0 < g (t - 1) := by linarith [hg2 (t - 1)]
  have hKt : 0 ≤ (M * g (t - 1) / (2 * ε)) ^ a := Real.rpow_nonneg (by positivity) _
  by_cases hRS : R = S
  · subst hRS
    simp only [hterm, ↓reduceIte] at hR
    have hS0 : 0 ≤ pdGap f x v R := pd_nonneg hconv hdiff hxs hrun R
    exact le_max_of_le_left (le_trans hR (mul_le_mul_of_nonneg_left hprod hS0))
  · simp only [hterm, hRS, ↓reduceIte] at hR
    refine le_max_of_le_right ?_
    have hgR : g (R - 1) ≤ g (t - 1) := hmono (by omega)
    have hgR0 : 0 < g (R - 1) := by linarith [hg2 (R - 1)]
    have hXR : X (R - 1) ≤ (M * g (t - 1) / (2 * ε)) ^ a * p ^ a := by
      show (M * g (R - 1) * p / (2 * ε)) ^ a ≤ _
      have hbase : M * g (R - 1) * p / (2 * ε) ≤ M * g (t - 1) / (2 * ε) * p := by
        have h1 : M * g (R - 1) / (2 * ε) ≤ M * g (t - 1) / (2 * ε) := by gcongr
        calc M * g (R - 1) * p / (2 * ε) = M * g (R - 1) / (2 * ε) * p := by ring
          _ ≤ M * g (t - 1) / (2 * ε) * p := mul_le_mul_of_nonneg_right h1 hp0.le
      have e : (M * g (t - 1) / (2 * ε) * p) ^ a = (M * g (t - 1) / (2 * ε)) ^ a * p ^ a :=
        Real.mul_rpow (by positivity) hp0.le
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hbase ha0.le
    have hmix := rpow_mix_le (a := a) (b := g S - ε) hq0 hqp hp1
    have hX0 : 0 ≤ X (R - 1) := by
      show 0 ≤ (M * g (R - 1) * p / (2 * ε)) ^ a
      exact Real.rpow_nonneg (by positivity) _
    have hqp0 : 0 ≤ (q / p) ^ (g S - ε) := Real.rpow_nonneg (div_pos hq0 hp0).le _
    calc pdGap f x v t ≤ X (R - 1) * ∏ i ∈ Finset.Ico R t, c i := hR
      _ ≤ X (R - 1) * (q / p) ^ (g S - ε) := mul_le_mul_of_nonneg_left hprod hX0
      _ ≤ (M * g (t - 1) / (2 * ε)) ^ a * p ^ a * (q / p) ^ (g S - ε) :=
          mul_le_mul_of_nonneg_right hXR hqp0
      _ = (M * g (t - 1) / (2 * ε)) ^ a * (p ^ a * (q / p) ^ (g S - ε)) := by ring
      _ ≤ (M * g (t - 1) / (2 * ε)) ^ a * q ^ min (g S - ε) a :=
          mul_le_mul_of_nonneg_left hmix hKt

/-- **Theorem 4.1.** -/
theorem weak_rate_bound {C : Set E} {f : E → ℝ} {g : ℕ → ℝ} {M r ε : ℝ} {S : ℕ}
    {x v : ℕ → E} {xStar : E} (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hg : IsAdmissible g) (hM : 0 < M)
    (hr : r ∈ Set.Ico (0 : ℝ) 1) (hgr0 : IsStrongGrowth C f M 0) (hw : IsWeakGrowth C f M r)
    (hS : 1 ≤ S) (hε0 : 0 < ε) (hε : ε ≤ g S - 1) (hrun : IsFWRun C (fderiv ℝ f) x v (etaG g)) :
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max ((f (x S) - f xStar) * (etaG g (t - 1) / etaG g (S - 1)) ^ (g S - ε))
        (((M * g (t - 1) / (2 * ε)) ^ (1 / (1 - r)) + M / 2) *
          etaG g (t - 1) ^ (min (g S - ε) (min (1 / (1 - r)) 2))) := by
  have hg' := hg
  obtain ⟨hg2, hmono, -⟩ := hg
  obtain ⟨hr0, hr1⟩ := hr
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1r : 0 < 1 - r := by linarith
  set a : ℝ := 1 / (1 - r) with ha
  have ha0 : 0 < a := by positivity
  set b : ℝ := min a 2 with hb
  have hb0 : 0 < b := lt_min ha0 (by norm_num)
  have hεi : ∀ i, S ≤ i → ε ≤ g i := fun i hi => by have := hmono hi; linarith
  set c : ℕ → ℝ := fun i => 1 - (1 - ε / g i) * etaG g i with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => factor_nonneg hg2 i hε0
  set K : ℕ → ℝ := fun i => (M * g i / (2 * ε)) ^ a + M / 2 with hK
  have hK0 : ∀ i, 0 ≤ K i := fun i => by simp only [hK]; have := hg2 i; positivity
  set term : ℕ → ℝ := fun R => if R = S then f (x S) - f xStar else
    K (R - 1) * etaG g (R - 1) ^ b with hterm
  -- the small step
  have hsmall : ∀ i, f (x i) - f xStar ≤ (M * g i * etaG g i / (2 * ε)) ^ a →
      f (x (i + 1)) - f xStar ≤ K i * etaG g i ^ b := by
    intro i hle
    have h1 := weak_small_step (xStar := xStar) hconv hgr0 hrun i
    have hη0 := etaG_pos hg2 i
    have hη1 := etaG_le_one hg2 i
    have hgi := hg2 i
    have e1 : (M * g i * etaG g i / (2 * ε)) ^ a = (M * g i / (2 * ε)) ^ a * etaG g i ^ a := by
      rw [← Real.mul_rpow (by positivity) hη0.le]; ring_nf
    have h2 : etaG g i ^ a ≤ etaG g i ^ b :=
      Real.rpow_le_rpow_of_exponent_ge hη0 hη1 (min_le_left _ _)
    have h3 : etaG g i ^ 2 ≤ etaG g i ^ b := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_ge hη0 hη1 (min_le_right _ _)
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (M * g i / (2 * ε)) ^ a)
    have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ M / 2)
    rw [e1] at hle
    simp only [hK]
    nlinarith
  have hinv : ∀ t, S ≤ t → ∃ R, S ≤ R ∧ R ≤ t ∧
      f (x t) - f xStar ≤ term R * ∏ i ∈ Finset.Ico R t, c i := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨S, le_rfl, le_rfl, by simp [hterm]⟩
    | succ t ht ih =>
      obtain ⟨R, hSR, hRt, hR⟩ := ih
      by_cases hle : f (x t) - f xStar ≤ (M * g t * etaG g t / (2 * ε)) ^ a
      · refine ⟨t + 1, by omega, le_rfl, ?_⟩
        rw [Finset.Ico_self, Finset.prod_empty, mul_one]
        simp only [hterm, show t + 1 ≠ S by omega, ↓reduceIte, Nat.add_sub_cancel]
        exact hsmall t hle
      · refine ⟨R, hSR, by omega, ?_⟩
        rw [Finset.prod_Ico_succ_top hRt]
        have h2 := weak_big_step hconv hdiff hxs hM hg2 ⟨hr0, hr1⟩ hε0 hw hrun t (hεi t ht)
          (lt_of_not_ge hle)
        calc f (x (t + 1)) - f xStar ≤ c t * (f (x t) - f xStar) := h2
          _ ≤ c t * (term R * ∏ i ∈ Finset.Ico R t, c i) := mul_le_mul_of_nonneg_left hR (hc0 t)
          _ = term R * ((∏ i ∈ Finset.Ico R t, c i) * c t) := by ring
  intro t ht
  obtain ⟨R, hSR, hRt, hR⟩ := hinv t ht
  have hprod := stretch_bound hg' hS hSR hRt hε0 hε
  set q := etaG g (t - 1) with hq
  set p := etaG g (R - 1) with hp
  have hq0 : 0 < q := etaG_pos hg2 _
  have hp0 : 0 < p := etaG_pos hg2 _
  have hp1 : p ≤ 1 := etaG_le_one hg2 _
  have hqp : q ≤ p := etaG_anti hg' (by omega)
  have hqp0 : 0 ≤ (q / p) ^ (g S - ε) := Real.rpow_nonneg (div_pos hq0 hp0).le _
  have hpb : 0 ≤ p ^ b := Real.rpow_nonneg hp0.le _
  by_cases hRS : R = S
  · subst hRS
    simp only [hterm, ↓reduceIte] at hR
    have hS0 : 0 ≤ f (x R) - f xStar := sub_nonneg.mpr (hxs.2 _ (hmem R))
    exact le_max_of_le_left (le_trans hR (mul_le_mul_of_nonneg_left hprod hS0))
  · simp only [hterm, hRS, ↓reduceIte] at hR
    refine le_max_of_le_right ?_
    have hKR : K (R - 1) ≤ K (t - 1) := by
      show (M * g (R - 1) / (2 * ε)) ^ a + M / 2 ≤ (M * g (t - 1) / (2 * ε)) ^ a + M / 2
      have hgR : g (R - 1) ≤ g (t - 1) := hmono (by omega)
      have hgR0 : 0 < g (R - 1) := by linarith [hg2 (R - 1)]
      have h1 : M * g (R - 1) / (2 * ε) ≤ M * g (t - 1) / (2 * ε) := by gcongr
      have := Real.rpow_le_rpow (by positivity) h1 ha0.le
      linarith
    have hmix := rpow_mix_le (a := b) (b := g S - ε) hq0 hqp hp1
    calc f (x t) - f xStar ≤ K (R - 1) * p ^ b * ∏ i ∈ Finset.Ico R t, c i := hR
      _ ≤ K (R - 1) * p ^ b * (q / p) ^ (g S - ε) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg (hK0 (R - 1)) hpb)
      _ ≤ K (t - 1) * p ^ b * (q / p) ^ (g S - ε) := by
          apply mul_le_mul_of_nonneg_right _ hqp0
          exact mul_le_mul_of_nonneg_right hKR hpb
      _ = K (t - 1) * (p ^ b * (q / p) ^ (g S - ε)) := by ring
      _ ≤ K (t - 1) * q ^ min (g S - ε) b := mul_le_mul_of_nonneg_left hmix (hK0 _)

/-- Facts about the threshold `S = ⌈exp(1/(1-r))⌉` of the log-adaptive cases. -/
theorem log_threshold (r : ℝ) :
    1 ≤ ⌈Real.exp (1 / (1 - r))⌉₊ ∧ (1 : ℝ) ≤ logStep ⌈Real.exp (1 / (1 - r))⌉₊ - 1 ∧
      1 / (1 - r) ≤ logStep ⌈Real.exp (1 / (1 - r))⌉₊ - 1 := by
  set S := ⌈Real.exp (1 / (1 - r))⌉₊ with hS
  have hS1 : 1 ≤ S := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hSr : Real.exp (1 / (1 - r)) ≤ S := Nat.le_ceil _
  have hlog : 1 / (1 - r) ≤ Real.log ((S : ℝ) + 1) := by
    rw [← Real.log_exp (1 / (1 - r))]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hS0 : (0 : ℝ) ≤ S := S.cast_nonneg
  have hl0 : 0 ≤ Real.log ((S : ℝ) + 1) := Real.log_nonneg (by linarith)
  refine ⟨hS1, ?_, ?_⟩ <;> unfold logStep <;> linarith

/-- `g(t - 1) = 2 + log t` and `η_{t-1} ≤ (2 + log t)/t` for the log-adaptive choice. -/
theorem logStep_pred {t : ℕ} (ht : 1 ≤ t) :
    logStep (t - 1) = 2 + Real.log t ∧ etaG logStep (t - 1) ≤ (2 + Real.log t) / t := by
  have hc : ((t - 1 : ℕ) : ℝ) + 1 = t := by rw [Nat.cast_sub ht]; simp
  have hg : logStep (t - 1) = 2 + Real.log t := by unfold logStep; rw [hc]
  refine ⟨hg, ?_⟩
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hl : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htr
  unfold etaG
  rw [hg]
  apply div_le_div_of_nonneg_left (by positivity) (by linarith)
  have : ((t - 1 : ℕ) : ℝ) = t - 1 := by rw [Nat.cast_sub ht]; simp
  rw [this]; linarith

namespace Proof

theorem strong_rate : StrongRate.{u} := by
  intro E _ _ C f g M r ε S x v xStar hconv hdiff hxs hg hM hr hgr hS hε0 hε hrun t ht
  exact strong_rate_bound hconv hdiff hxs hg hM hr hgr hS hε0 hε hrun t ht

theorem weak_rate : WeakRate.{u} := by
  intro E _ _ C f g M r ε S x v xStar hconv hdiff hxs hg hM hr hgr0 hw hS hε0 hε hrun t ht
  exact weak_rate_bound hconv hdiff hxs hg hM hr hgr0 hw hS hε0 hε hrun t ht

theorem log_strong_rate : LogStrongRate.{u} := by
  intro E _ _ C f M r x v xStar hconv hdiff hxs hM hr hgr hrun S t ht
  obtain ⟨hS1, hε, ha⟩ := log_threshold r
  have hr1 : 0 < 1 - r := by linarith [hr.2]
  set a : ℝ := 1 / (1 - r) with hadef
  have ha0 : 0 < a := by positivity
  have h := strong_rate_bound hconv hdiff hxs logStep_isAdmissible hM hr hgr hS1 one_pos hε hrun
    t ht
  rw [min_eq_right ha] at h
  have ht1 : 1 ≤ t := le_trans hS1 ht
  obtain ⟨hg, hηt⟩ := logStep_pred ht1
  rw [hg, mul_one] at h
  set q := etaG logStep (t - 1) with hq
  set p := etaG logStep (S - 1) with hp
  have hg2 := logStep_isAdmissible.1
  have hq0 : 0 < q := etaG_pos hg2 _
  have hp0 : 0 < p := etaG_pos hg2 _
  have hqp : q ≤ p := etaG_anti logStep_isAdmissible (by omega)
  have hS0 : 0 ≤ pdGap f x v S := pd_nonneg hconv hdiff hxs hrun S
  have hratio1 : q / p ≤ 1 := by rw [div_le_one hp0]; exact hqp
  have hfirst : pdGap f x v S * (q / p) ^ (logStep S - 1) ≤ pdGap f x v S / p ^ a * q ^ a := by
    have := Real.rpow_le_rpow_of_exponent_ge (div_pos hq0 hp0) hratio1 ha
    calc pdGap f x v S * (q / p) ^ (logStep S - 1) ≤ pdGap f x v S * (q / p) ^ a :=
          mul_le_mul_of_nonneg_left this hS0
      _ = pdGap f x v S / p ^ a * q ^ a := by rw [Real.div_rpow hq0.le hp0.le]; ring
  set A := pdGap f x v S / p ^ a with hA
  set B := (M * (2 + Real.log t) / 2) ^ a with hB
  have hlt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht1)
  have hB0 : 0 ≤ B := by positivity
  have hmax0 : 0 ≤ max A B := le_max_of_le_right hB0
  have hqQ : q ^ a ≤ ((2 + Real.log t) / t) ^ a := Real.rpow_le_rpow hq0.le hηt ha0.le
  have hqa0 : 0 ≤ q ^ a := by positivity
  calc pdGap f x v t ≤ max (pdGap f x v S * (q / p) ^ (logStep S - 1)) (B * q ^ a) := h
    _ ≤ max (A * q ^ a) (B * q ^ a) := max_le_max hfirst le_rfl
    _ ≤ max A B * q ^ a := max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hqa0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hqa0)
    _ ≤ max A B * ((2 + Real.log t) / t) ^ a := mul_le_mul_of_nonneg_left hqQ hmax0

theorem log_weak_rate : LogWeakRate.{u} := by
  intro E _ _ C f M r x v xStar hconv hdiff hxs hM hr hgr0 hw hrun S t ht
  obtain ⟨hS1, hε, ha⟩ := log_threshold r
  have hr1 : 0 < 1 - r := by linarith [hr.2]
  set a : ℝ := 1 / (1 - r) with hadef
  have ha0 : 0 < a := by positivity
  set b : ℝ := min a 2 with hbdef
  have hb0 : 0 < b := lt_min ha0 (by norm_num)
  have hba : b ≤ logStep S - 1 := le_trans (min_le_left _ _) ha
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h := weak_rate_bound hconv hdiff hxs logStep_isAdmissible hM hr hgr0 hw hS1 one_pos hε
    hrun t ht
  rw [min_eq_right hba] at h
  have ht1 : 1 ≤ t := le_trans hS1 ht
  obtain ⟨hg, hηt⟩ := logStep_pred ht1
  rw [hg, mul_one] at h
  set q := etaG logStep (t - 1) with hq
  set p := etaG logStep (S - 1) with hp
  have hg2 := logStep_isAdmissible.1
  have hq0 : 0 < q := etaG_pos hg2 _
  have hp0 : 0 < p := etaG_pos hg2 _
  have hqp : q ≤ p := etaG_anti logStep_isAdmissible (by omega)
  have hS0 : 0 ≤ f (x S) - f xStar := sub_nonneg.mpr (hxs.2 _ (hmem S))
  have hratio1 : q / p ≤ 1 := by rw [div_le_one hp0]; exact hqp
  have hfirst : (f (x S) - f xStar) * (q / p) ^ (logStep S - 1) ≤
      (f (x S) - f xStar) / p ^ b * q ^ b := by
    have := Real.rpow_le_rpow_of_exponent_ge (div_pos hq0 hp0) hratio1 hba
    calc (f (x S) - f xStar) * (q / p) ^ (logStep S - 1) ≤ (f (x S) - f xStar) * (q / p) ^ b :=
          mul_le_mul_of_nonneg_left this hS0
      _ = (f (x S) - f xStar) / p ^ b * q ^ b := by rw [Real.div_rpow hq0.le hp0.le]; ring
  set A := (f (x S) - f xStar) / p ^ b with hA
  set B := (M * (2 + Real.log t) / 2) ^ a + M / 2 with hB
  have hlt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht1)
  have hB0 : 0 ≤ B := by positivity
  have hmax0 : 0 ≤ max A B := le_max_of_le_right hB0
  have hqQ : q ^ b ≤ ((2 + Real.log t) / t) ^ b := Real.rpow_le_rpow hq0.le hηt hb0.le
  have hqb0 : 0 ≤ q ^ b := by positivity
  calc f (x t) - f xStar ≤ max ((f (x S) - f xStar) * (q / p) ^ (logStep S - 1)) (B * q ^ b) := h
    _ ≤ max (A * q ^ b) (B * q ^ b) := max_le_max hfirst le_rfl
    _ ≤ max A B * q ^ b := max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hqb0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hqb0)
    _ ≤ max A B * ((2 + Real.log t) / t) ^ b := mul_le_mul_of_nonneg_left hqQ hmax0

end Proof

end Lemmata.FWLogAdaptive
