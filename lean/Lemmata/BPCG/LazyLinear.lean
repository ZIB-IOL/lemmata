module

public import Lemmata.BPCG.Lazy

@[expose] public section

/-!
# Lazified BPCG for strongly convex objectives (Theorem 3.6, case (A))

At a gap step `f'(x)(a - w) < 2 Φ`, so geometric strong convexity gives `μ δ² h ≤ 2 Φ²`, and
`μ δ² h ≤ 8 Φ²` after the halving. Steps that do not drop a vertex gain at least
`Φ²/(2 J² L D²)`: a constant before the first gap step, and at least `μ δ² h/(16 J² L D²)` after it.
-/

namespace Lemmata.BPCG

open Lemmata.FrankWolfe Lemmata.AwayStepFW

namespace Proof

universe u

theorem lazy_linear_rate : LazyLinearRate.{u} := by
  intro E _ _ V f L μ δ J x S lam Φ hμ hδ hsc hconv hsm hstrong hJ hrun xStar hxs hΦ0 hΦ0' ε hε t
    ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set P := convexHull ℝ (↑V : Set E) with hP
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hJ0 : 0 < J := by linarith
  have inv := lazy_bpcg_run_inv hrun
  have hxP : ∀ t, x t ∈ P := fun t =>
    convexHull_mono (by exact_mod_cast (inv t).sub) (inv t).mem_convexHull
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hxP t)]
  have hdist : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D := fun y hy z hz => by
    rw [← dist_eq_norm, hD, ← convexHull_diam]
    exact Metric.dist_le_diam_of_mem hPc.isBounded hy hz
  have hgapw : ∀ t (w : E), (∀ u ∈ V, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) u) →
      h t ≤ fderiv ℝ f (x t) (x t - w) := fun t w hwV => by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
    have h2 := Lemmata.CGBasics.Proof.le_on_hull (fderiv ℝ f (x t)) hwV hxs.1
    simp only [hh]
    rw [map_sub] at h1 ⊢
    linarith
  -- each step: monotone, and `Φ` stays or halves
  have hbasic : ∀ t, h (t + 1) ≤ h t ∧ (Φ (t + 1) = Φ t ∨ Φ (t + 1) = Φ t / 2) := by
    intro t
    obtain ⟨a, ha, -, s, hs, -, hstep⟩ := hrun.2.2.2 t
    unfold IsLazyBPCGStep at hstep
    split_ifs at hstep with hsel
    · obtain ⟨⟨γ, hγ, hls, hx', -, -⟩, hΦ'⟩ := hstep
      refine ⟨?_, Or.inl hΦ'⟩
      have := hls 0 ⟨le_rfl, (inv t).nonneg a⟩
      simp only [hh, hx']; simp at this; linarith
    · obtain ⟨w, hw, -, hrest⟩ := hstep
      split_ifs at hrest with hfw
      · obtain ⟨⟨γ, hγ, hls, hx', -, -⟩, hΦ'⟩ := hrest
        refine ⟨?_, Or.inl hΦ'⟩
        have := hls 0 ⟨le_rfl, zero_le_one⟩
        simp only [hh, hx']; simp at this; linarith
      · obtain ⟨hx', -, -, hΦ'⟩ := hrest
        exact ⟨by simp only [hh, hx', le_refl], Or.inr hΦ'⟩
  have hmono : ∀ t, h (t + 1) ≤ h t := fun t => (hbasic t).1
  have hanti : Antitone h := antitone_nat_of_succ_le hmono
  have hΦb : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ Φ 0 := by
    intro t
    induction t with
    | zero => exact ⟨by linarith [hh0 0], le_rfl⟩
    | succ t ih =>
      rcases (hbasic t).2 with hΦ' | hΦ'
      · rw [hΦ']; exact ih
      · rw [hΦ']; exact ⟨by linarith [ih.1], by linarith [ih.1, ih.2]⟩
  -- the degenerate case `L D² = 0`
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK0 | hKpos
  · have h1 : h 0 ≤ 0 := by simp only [hh]; rw [← hK0] at hΦ0'; linarith
    have h2 := hanti (Nat.zero_le t)
    have h3 : h t ≤ ε := by linarith
    simpa [hh] using h3
  have hLpos : 0 < (L : ℝ) := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with h0 | h0
    · rw [← h0, zero_mul] at hKpos; exact absurd hKpos (lt_irrefl 0)
    · exact h0
  have hΦK : ∀ t, Φ t ≤ J * (L * D ^ 2) := fun t => by
    have h1 := (hΦb t).2
    have h2 : L * D ^ 2 ≤ J * (L * D ^ 2) := le_mul_of_one_le_left hKpos.le hJ
    linarith
  have hout : ∀ t, (h t ≤ Φ t ∧ μ * δ ^ 2 * h t ≤ 2 * Φ t ^ 2 ∧ h (t + 1) = h t ∧
        S (t + 1) = S t ∧ Φ (t + 1) = Φ t / 2) ∨
      (h (t + 1) ≤ h t ∧ (S (t + 1)).card + 1 = (S t).card ∧ Φ (t + 1) = Φ t) ∨
      (h (t + 1) ≤ h t - Φ t ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) ∧
        (S (t + 1)).card ≤ (S t).card + 1 ∧ Φ (t + 1) = Φ t) := by
    intro t
    obtain ⟨a, ha, haS, s, hs, hsS, hstep⟩ := hrun.2.2.2 t
    have haP : a ∈ P := subset_convexHull ℝ _ (by exact_mod_cast (inv t).sub ha)
    have hsP : s ∈ P := subset_convexHull ℝ _ (by exact_mod_cast (inv t).sub hs)
    have hJ2 : (1 : ℝ) ≤ J ^ 2 := by nlinarith
    have hmono' : Φ t ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) ≤ Φ t ^ 2 / (2 * (L * D ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    unfold IsLazyBPCGStep at hstep
    split_ifs at hstep with hsel
    · obtain ⟨⟨γ, hγ, hls, hx', -, hS'⟩, hΦ'⟩ := hstep
      by_cases hdrop : γ = lam t a ∧ a ≠ s
      · right; left
        exact ⟨hmono t, by rw [hS', ite_eq_left hdrop]; exact Finset.card_erase_add_one ha, hΦ'⟩
      · right; right
        refine ⟨?_, by rw [hS', ite_eq_right hdrop]; omega, hΦ'⟩
        by_cases has : a = s
        · subst has
          have hΦ0t : Φ t = 0 := le_antisymm (by simpa using hsel) (hΦb t).1
          have e : h (t + 1) = h t := by simp only [hh, hx', sub_self, smul_zero, sub_zero]
          rw [hΦ0t, e]; simp
        · have hγlt : γ < lam t a := lt_of_le_of_ne hγ.2 (fun e => hdrop ⟨e, has⟩)
          have hray := ray_opt hconv hγlt hls hγ.1
          set G := fderiv ℝ f (x t) (a - s) with hG
          have hd : 0 < ‖a - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr has)
          have hdD : ‖a - s‖ ≤ D := hdist a haP s hsP
          have hc : 0 < (L : ℝ) * ‖a - s‖ ^ 2 := by positivity
          set σ := G / (L * ‖a - s‖ ^ 2) with hσ
          have hσ0 : 0 ≤ σ := div_nonneg ((hΦb t).1.trans hsel) hc.le
          have h1 := hray σ hσ0
          have h2 := quad_along hsm (x t) (a - s) σ
          rw [← hG] at h2
          have e : σ * G - σ ^ 2 * L / 2 * ‖a - s‖ ^ 2 = G ^ 2 / (2 * (L * ‖a - s‖ ^ 2)) := by
            rw [hσ]; field_simp; ring
          have hdD2 : (L : ℝ) * ‖a - s‖ ^ 2 ≤ L * D ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdD 2) hLpos.le
          have h3 : Φ t ^ 2 / (2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * ‖a - s‖ ^ 2)) :=
            calc Φ t ^ 2 / (2 * (L * D ^ 2)) ≤ G ^ 2 / (2 * (L * D ^ 2)) :=
                  div_le_div_of_nonneg_right (pow_le_pow_left₀ (hΦb t).1 hsel 2) (by positivity)
              _ ≤ G ^ 2 / (2 * (L * ‖a - s‖ ^ 2)) :=
                  div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
          simp only [hh, hx']
          linarith
    · obtain ⟨w, hw, hwV, hrest⟩ := hstep
      have hwP : w ∈ P := subset_convexHull ℝ _ (by exact_mod_cast hw)
      split_ifs at hrest with hfw
      · obtain ⟨⟨γ, hγ, hls, hx', -, hS'⟩, hΦ'⟩ := hrest
        right; right
        refine ⟨?_, by rw [hS']; split_ifs <;> simp [Finset.card_insert_le], hΦ'⟩
        set G := fderiv ℝ f (x t) (x t - w) with hG
        have hdD : ‖x t - w‖ ≤ D := hdist (x t) (hxP t) w hwP
        set σ := Φ t / (J * (L * D ^ 2)) with hσ
        have hσ0 : 0 ≤ σ := div_nonneg (hΦb t).1 (by positivity)
        have hσ1 : σ ≤ 1 := by rw [hσ, div_le_one (by positivity)]; exact hΦK t
        have h1 := hls σ ⟨hσ0, hσ1⟩
        have h2 := quad_along hsm (x t) (x t - w) σ
        rw [← hG] at h2
        have hd2 : σ ^ 2 * L / 2 * ‖x t - w‖ ^ 2 ≤ σ ^ 2 * (L * D ^ 2) / 2 := by
          have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdD 2)
            (by positivity : (0 : ℝ) ≤ σ ^ 2 * L)
          nlinarith
        have hg : σ * (Φ t / J) ≤ σ * G := mul_le_mul_of_nonneg_left hfw hσ0
        have he : σ * (Φ t / J) - σ ^ 2 * (L * D ^ 2) / 2 =
            Φ t ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) := by
          rw [hσ]; field_simp; ring
        simp only [hh, hx']
        linarith
      · obtain ⟨hx', hS', -, hΦ'⟩ := hrest
        left
        push Not at hfw
        have h1 := hgapw t w hwV
        have h2 : Φ t / J ≤ Φ t := div_le_self (hΦb t).1 hJ
        have hsx := Lemmata.CGBasics.Proof.le_on_hull (V := S t) (fderiv ℝ f (x t)) hsS
          (inv t).mem_convexHull
        have hax := (inv t).apply_le (fderiv ℝ f (x t)) haS
        have hwx := Lemmata.CGBasics.Proof.le_on_hull (fderiv ℝ f (x t)) hwV (hxP t)
        have hsel' : fderiv ℝ f (x t) (a - s) < Φ t := not_le.mp hsel
        have hgaw : fderiv ℝ f (x t) (a - w) ≤ 2 * Φ t := by
          rw [map_sub] at hsel' hfw ⊢; linarith
        have hgaw0 : 0 ≤ fderiv ℝ f (x t) (a - w) := by rw [map_sub]; linarith
        have hgeo := Lemmata.AwayStepFW.Proof.geometric_strong_convexity V f μ δ hμ hδ hsc hstrong
          xStar hxs (S t) (inv t).sub (x t) (inv t).mem_convexHull a ha haS w hw hwV
        have h5 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
        have h6 := pow_le_pow_left₀ hgaw0 hgaw 2
        have h7 : (2 * Φ t) ^ 2 = 4 * Φ t ^ 2 := by ring
        refine ⟨by linarith, ?_, by simp only [hh, hx'], hS', hΦ'⟩
        simp only [hh] at h5 ⊢
        linarith
  set c := μ * δ ^ 2 / (16 * J ^ 2 * (L * D ^ 2)) with hc
  set q₀ := Φ 0 ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) with hq₀
  set n₀ := ⌈Real.logb 2 (Φ 0 / ε)⌉₊ with hn₀
  have hc0 : 0 ≤ c := by positivity
  have hφε : Φ 0 / 2 ^ n₀ ≤ ε := by
    rcases le_or_gt (Φ 0) 0 with hΦ | hΦ
    · have : Φ 0 / 2 ^ n₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hΦ (by positivity)
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have h1 : Real.logb 2 (Φ 0 / ε) ≤ n₀ := Nat.le_ceil _
      have h2 : Φ 0 / ε ≤ (2 : ℝ) ^ (n₀ : ℝ) := by
        rw [← Real.logb_le_logb (b := 2) (by norm_num) (div_pos hΦ hε) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num)]
        exact h1
      rw [Real.rpow_natCast, div_le_iff₀ hε] at h2
      linarith
  have hstate : ∀ t, ∃ n dr gpre gpost : ℕ, n + dr + gpre + gpost = t ∧
      (S t).card + dr ≤ 1 + gpre + gpost ∧ Φ t = Φ 0 / 2 ^ n ∧ (n₀ + 1 ≤ n → h t ≤ ε) ∧
      (n = 0 → gpost = 0 ∧ (gpre : ℝ) * q₀ ≤ h 0 - h t) ∧ (gpre : ℝ) * q₀ ≤ h 0 ∧
      (1 ≤ n → μ * δ ^ 2 * h t ≤ 8 * Φ t ^ 2) ∧ h t ≤ Real.exp (-(c * gpost)) * h 0 := by
    intro t
    induction t with
    | zero =>
      refine ⟨0, 0, 0, 0, rfl, by rw [hrun.2.1]; simp, by simp, fun h => absurd h (by omega),
        fun _ => ⟨rfl, by simp⟩, by simp [hh0 0], fun h => absurd h (by omega), by simp⟩
    | succ t ih =>
      obtain ⟨n, dr, gpre, gpost, hsum, hcard, hφn, hε', hpre, hpre', hlin, hexp⟩ := ih
      rcases hout t with ⟨hcert, hgeo2, he, hS', hΦ'⟩ | ⟨hle, hc', hΦ'⟩ | ⟨hle, hc', hΦ'⟩
      · refine ⟨n + 1, dr, gpre, gpost, by omega, by rw [hS']; omega,
          by rw [hΦ', hφn, pow_succ]; field_simp, fun hN => ?_, fun h => absurd h (by omega),
          hpre', fun _ => ?_, by rw [he]; exact hexp⟩
        · rw [he]
          rcases Nat.lt_or_ge n (n₀ + 1) with hlt | hge
          · have hN0 : n = n₀ := by omega
            calc h t ≤ Φ t := hcert
              _ = Φ 0 / 2 ^ n := hφn
              _ = Φ 0 / 2 ^ n₀ := by rw [hN0]
              _ ≤ ε := hφε
          · exact hε' hge
        · rw [he, hΦ']
          have := hgeo2
          nlinarith
      · refine ⟨n, dr + 1, gpre, gpost, by omega, by omega, by rw [hΦ', hφn],
          fun hN => hle.trans (hε' hN), fun h0 => ⟨(hpre h0).1, by linarith [(hpre h0).2]⟩,
          hpre', fun h1 => ?_, hle.trans hexp⟩
        rw [hΦ']
        have := hlin h1
        have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ μ * δ ^ 2)
        linarith
      · rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · -- before the first negative answer: `φ_t = Φ₀`
          have hφt : Φ t = Φ 0 := by rw [hφn, hn0, pow_zero, div_one]
          have hq : h (t + 1) ≤ h t - q₀ := by rw [hq₀, ← hφt]; exact hle
          obtain ⟨hgp, hpre0⟩ := hpre hn0
          refine ⟨n, dr, gpre + 1, gpost, by omega, by omega, by rw [hΦ', hφn],
            fun hN => absurd hN (by omega), fun _ => ⟨hgp, ?_⟩, ?_, fun h => absurd h (by omega),
            ?_⟩
          · push_cast; linarith
          · push_cast; linarith [hh0 (t + 1)]
          · rw [hgp]; simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
            linarith [hanti (Nat.zero_le (t + 1))]
        · have hl := hlin hn1
          have hprog : c * h t ≤ Φ t ^ 2 / (2 * J ^ 2 * (L * D ^ 2)) := by
            rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            have := mul_le_mul_of_nonneg_right hl
              (by positivity : (0 : ℝ) ≤ 2 * J ^ 2 * (L * D ^ 2))
            linarith
          have hstep : h (t + 1) ≤ Real.exp (-c) * h t := by
            have := Real.add_one_le_exp (-c)
            have := mul_le_mul_of_nonneg_right this (hh0 t)
            linarith
          refine ⟨n, dr, gpre, gpost + 1, by omega, by omega, by rw [hΦ', hφn],
            fun hN => (hmono t).trans (hε' hN), fun h => absurd h (by omega),
            hpre', fun _ => ?_, ?_⟩
          · rw [hΦ']
            have := mul_le_mul_of_nonneg_left (hmono t) (by positivity : (0 : ℝ) ≤ μ * δ ^ 2)
            linarith
          · calc h (t + 1) ≤ Real.exp (-c) * h t := hstep
              _ ≤ Real.exp (-c) * (Real.exp (-(c * gpost)) * h 0) :=
                mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
              _ = Real.exp (-(c * ((gpost + 1 : ℕ) : ℝ))) * h 0 := by
                rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
  obtain ⟨n, dr, gpre, gpost, hsum, hcard, -, hε', -, hpre', -, hexp⟩ := hstate t
  by_cases hsmall : h 0 ≤ ε
  · have := hanti (Nat.zero_le t)
    have : h t ≤ ε := by linarith
    simpa [hh] using this
  push Not at hsmall
  have hh0pos : 0 < h 0 := lt_trans hε hsmall
  have hφ0pos : 0 < Φ 0 := by
    have : 0 < f (x 0) - f xStar := hh0pos
    linarith
  set A := ⌈4 * J ^ 2 * L * D ^ 2 / Φ 0⌉₊ with hA
  set B := ⌈16 * J ^ 2 * L * D ^ 2 / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε)⌉₊ with hB
  rcases Nat.lt_or_ge n (n₀ + 1) with hn | hn
  swap
  · simpa [hh] using hε' hn
  rcases Nat.lt_or_ge gpost B with hgp | hgp
  swap
  · have hcinv : c * (16 * J ^ 2 * L * D ^ 2 / (μ * δ ^ 2)) = 1 := by
      have hpos' : 0 < 16 * J ^ 2 * (L * D ^ 2) * (μ * δ ^ 2) :=
        mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hJ0 2)) hKpos) (mul_pos hμ (pow_pos hδ 2))
      rw [hc, div_mul_div_comm,
        show μ * δ ^ 2 * (16 * J ^ 2 * L * D ^ 2) = 16 * J ^ 2 * (L * D ^ 2) * (μ * δ ^ 2) by ring]
      exact div_self hpos'.ne'
    have h1 : 16 * J ^ 2 * L * D ^ 2 / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε) ≤ B :=
      Nat.le_ceil _
    have h2 : (B : ℝ) ≤ gpost := by exact_mod_cast hgp
    have hcB : Real.log ((f (x 0) - f xStar) / ε) ≤ c * gpost := by
      calc Real.log ((f (x 0) - f xStar) / ε) =
            c * (16 * J ^ 2 * L * D ^ 2 / (μ * δ ^ 2) * Real.log ((f (x 0) - f xStar) / ε)) := by
            rw [← mul_assoc, hcinv, one_mul]
        _ ≤ c * B := mul_le_mul_of_nonneg_left h1 hc0
        _ ≤ c * gpost := mul_le_mul_of_nonneg_left h2 hc0
    have h3 : Real.exp (-(c * gpost)) ≤ Real.exp (-Real.log ((f (x 0) - f xStar) / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpos : 0 < (f (x 0) - f xStar) / ε := div_pos hh0pos hε
    rw [show Real.exp (-Real.log ((f (x 0) - f xStar) / ε)) = ((f (x 0) - f xStar) / ε)⁻¹ by
      rw [Real.exp_neg, Real.exp_log hpos]] at h3
    have h4 : Real.exp (-(c * gpost)) * h 0 ≤ ε := by
      calc Real.exp (-(c * gpost)) * h 0 ≤ ((f (x 0) - f xStar) / ε)⁻¹ * h 0 :=
            mul_le_mul_of_nonneg_right h3 hh0pos.le
        _ = ε := by
            have : h 0 = f (x 0) - f xStar := rfl
            rw [this, inv_div]
            exact div_mul_cancel₀ ε hh0pos.ne'
    simpa [hh] using hexp.trans h4
  exfalso
  have hgpre : gpre ≤ A := by
    have h1 : (gpre : ℝ) * q₀ ≤ 2 * Φ 0 := by
      have : h 0 ≤ 2 * Φ 0 := by simp only [hh]; linarith
      linarith
    have hq : (gpre : ℝ) * Φ 0 ^ 2 ≤ 2 * Φ 0 * (2 * J ^ 2 * (L * D ^ 2)) := by
      rw [hq₀, mul_div_assoc', div_le_iff₀ (by positivity)] at h1
      exact h1
    have h2 : (gpre : ℝ) * Φ 0 ≤ 4 * J ^ 2 * L * D ^ 2 := by
      have h3 : (gpre : ℝ) * Φ 0 * Φ 0 ≤ (4 * J ^ 2 * L * D ^ 2) * Φ 0 := by
        have e1 : (gpre : ℝ) * Φ 0 * Φ 0 = (gpre : ℝ) * Φ 0 ^ 2 := by ring
        have e2 : (4 * J ^ 2 * L * D ^ 2) * Φ 0 = 2 * Φ 0 * (2 * J ^ 2 * (L * D ^ 2)) := by ring
        rw [e1, e2]; exact hq
      exact le_of_mul_le_mul_right h3 hφ0pos
    have h4 : (gpre : ℝ) ≤ A := by
      have : (gpre : ℝ) ≤ 4 * J ^ 2 * L * D ^ 2 / Φ 0 := by rw [le_div_iff₀ hφ0pos]; exact h2
      exact this.trans (Nat.le_ceil _)
    exact_mod_cast h4
  have hS1 : 1 ≤ (S t).card := by
    rcases Nat.eq_zero_or_pos (S t).card with h0 | h0
    · have := (inv t).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
  omega

end Proof

end Lemmata.BPCG
