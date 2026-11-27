module

public import Lemmata.CGImprovements.Sharp
public import Lemmata.AwayStepFW.Convergence

@[expose] public section

/-!
# Away-step Frank–Wolfe under sharpness (Corollary 3.33)

A step of away-step Frank–Wolfe that does not drop a vertex gains at least
`min {h/2, f'(x)(a - v)²/(8 L D²)}`: the chosen gap is at least the primal gap and at least half
of `f'(x)(a - v)`. Geometric sharpness bounds `f'(x)(a - v)` from below.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem afw_step_progress {V : Finset E} {f : E → ℝ} {L : NNReal} (hL : 0 < (L : ℝ))
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L) {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) {x : E} {S : Finset E}
    {lam : E → ℝ} (h : Lemmata.AwayStepFW.Proof.Inv V x S lam) {v a : E} (hvV : v ∈ V)
    (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : Lemmata.AwayStepFW.IsAFWStep L (fderiv ℝ f x) x S lam v a x' S' lam') :
    (f x' - f xStar ≤ (f x - f xStar) - min ((f x - f xStar) / 2)
        (fderiv ℝ f x (a - v) ^ 2 / (8 * (L * Metric.diam (↑V : Set E) ^ 2))) ∧
      S'.card ≤ S.card + 1) ∨ (f x' ≤ f x ∧ S'.card + 1 = S.card) := by
  set g := fderiv ℝ f x with hg
  set D := Metric.diam (↑V : Set E) with hD
  set K : ℝ := L * D ^ 2 with hK
  have hP : IsCompact (convexHull ℝ (↑V : Set E)) := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxV : x ∈ convexHull ℝ (↑V : Set E) :=
    convexHull_mono (by exact_mod_cast h.sub) h.mem_convexHull
  have hdist : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D :=
    fun y hy z hz => by
      rw [← dist_eq_norm, hD, ← convexHull_diam]
      exact Metric.dist_le_diam_of_mem hP.isBounded hy hz
  have hvP : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hvV)
  have haP : a ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast h.sub ha)
  have hgap : f x - f xStar ≤ g (x - v) := by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 x xStar
    have h2 := Lemmata.CGBasics.Proof.le_on_hull g hv hxs.1
    rw [map_sub] at h1 ⊢
    linarith
  have hh0 : 0 ≤ f x - f xStar := by linarith [hxs.2 x hxV]
  have hfw0 : 0 ≤ g (x - v) := hh0.trans hgap
  have hax : g x ≤ g a := h.apply_le g haS
  have hK0 : 0 ≤ K := by positivity
  -- the generic estimate `min {G/2, G²/(2K)} ≥ min {h/2, g(a - v)²/(8K)}`
  have hmin : ∀ G : ℝ, f x - f xStar ≤ G → g (a - v) ≤ 2 * G →
      min ((f x - f xStar) / 2) (g (a - v) ^ 2 / (8 * K)) ≤ min (G / 2) (G ^ 2 / (2 * K)) := by
    intro G hG1 hG2
    have hgav0 : 0 ≤ g (a - v) := by
      rw [map_sub]; linarith [Lemmata.CGBasics.Proof.le_on_hull g hv hxV]
    apply le_min
    · exact (min_le_left _ _).trans (by linarith)
    · refine (min_le_right _ _).trans ?_
      rcases eq_or_lt_of_le hK0 with hK00 | hKpos
      · rw [← hK00]; simp
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := pow_le_pow_left₀ hgav0 hG2 2
        nlinarith
  unfold Lemmata.AwayStepFW.IsAFWStep at hstep
  split_ifs at hstep with hfw
  · -- Frank–Wolfe step
    dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    left
    refine ⟨?_, ?_⟩
    swap
    · rw [hS']
      split_ifs
      · simp
      · exact Finset.card_insert_le v S
    set G := g (x - v) with hG
    have hm := hmin G hgap (by
      have e : g (a - v) = g (a - x) + G := by rw [hG]; simp only [map_sub]; ring
      rw [e]; linarith)
    rcases eq_or_lt_of_le (norm_nonneg (x - v)) with hd0 | hd
    · have hxv : x - v = 0 := norm_eq_zero.mp hd0.symm
      have hG0 : G = 0 := by rw [hG, hxv, map_zero]
      rw [hx', hxv, smul_zero, sub_zero]
      have : min (G / 2) (G ^ 2 / (2 * K)) = 0 := by rw [hG0]; simp
      linarith
    have hq := Lemmata.BPCG.Proof.quad_along hsm x (x - v)
      (min (G / (L * ‖x - v‖ ^ 2)) 1)
    rw [← hG, ← hx'] at hq
    have hc : 0 < (L : ℝ) * ‖x - v‖ ^ 2 := by positivity
    have hdD : ‖x - v‖ ≤ D := hdist x hxV v hvP
    have hdD2 : (L : ℝ) * ‖x - v‖ ^ 2 ≤ K :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdD 2) (NNReal.coe_nonneg L)
    have hKpos : 0 < K := lt_of_lt_of_le hc hdD2
    have hprog : f x' ≤ f x - min (G / 2) (G ^ 2 / (2 * K)) := by
      rcases le_total (G / (L * ‖x - v‖ ^ 2)) 1 with hle | hle
      · rw [min_eq_left hle] at hq
        have e : G / (L * ‖x - v‖ ^ 2) * G - (G / (L * ‖x - v‖ ^ 2)) ^ 2 * L / 2 * ‖x - v‖ ^ 2 =
            G ^ 2 / (2 * (L * ‖x - v‖ ^ 2)) := by field_simp; ring
        have h1 : G ^ 2 / (2 * K) ≤ G ^ 2 / (2 * (L * ‖x - v‖ ^ 2)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
        have := min_le_right (G / 2) (G ^ 2 / (2 * K))
        linarith
      · rw [min_eq_right hle] at hq
        have hcG : (L : ℝ) * ‖x - v‖ ^ 2 ≤ G := by rwa [le_div_iff₀ hc, one_mul] at hle
        have := min_le_left (G / 2) (G ^ 2 / (2 * K))
        simp only [one_pow, one_mul] at hq
        linarith
    linarith
  · -- away step
    dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    have hfw' : g (x - v) < g (a - x) := not_le.mp hfw
    set G := g (a - x) with hG
    set γmax := lam a / (1 - lam a) with hγmax
    have hle1 : lam a ≤ 1 := h.sum ▸ Finset.single_le_sum (fun u _ => h.nonneg u) ha
    have hγmax0 : 0 ≤ γmax := div_nonneg (h.nonneg a) (by linarith)
    have hG0 : 0 < G := lt_of_le_of_lt hfw0 hfw'
    have hd : 0 < ‖a - x‖ := norm_pos_iff.mpr (fun e => by rw [hG, e, map_zero] at hG0; linarith)
    have hc : 0 < (L : ℝ) * ‖a - x‖ ^ 2 := by positivity
    have hdD : ‖a - x‖ ≤ D := hdist a haP x hxV
    have hdD2 : (L : ℝ) * ‖a - x‖ ^ 2 ≤ K :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdD 2) (NNReal.coe_nonneg L)
    set γ := min (G / (L * ‖a - x‖ ^ 2)) γmax with hγ
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hG0.le hc.le) hγmax0
    have hγc : γ * (L * ‖a - x‖ ^ 2) ≤ G := by
      have : γ ≤ G / (L * ‖a - x‖ ^ 2) := min_le_left _ _
      rwa [le_div_iff₀ hc] at this
    have hq := Lemmata.BPCG.Proof.quad_along hsm x (a - x) γ
    rw [← hG, ← hx'] at hq
    by_cases hdrop : γ = γmax
    · right
      refine ⟨?_, by rw [hS', ite_eq_left hdrop]; exact Finset.card_erase_add_one ha⟩
      have h5 := mul_le_mul_of_nonneg_left hγc (by positivity : (0 : ℝ) ≤ γ / 2)
      have h6 := mul_nonneg hγ0 hG0.le
      linarith
    · left
      refine ⟨?_, by rw [hS', ite_eq_right hdrop]; omega⟩
      have hγv : γ = G / (L * ‖a - x‖ ^ 2) := by
        rcases min_choice (G / (L * ‖a - x‖ ^ 2)) γmax with h1 | h1
        · rw [hγ, h1]
        · exact absurd (by rw [hγ, h1]) hdrop
      have hKpos : 0 < K := lt_of_lt_of_le hc hdD2
      have e : γ * G - γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 = G ^ 2 / (2 * (L * ‖a - x‖ ^ 2)) := by
        rw [hγv]; field_simp; ring
      have h1 : G ^ 2 / (2 * K) ≤ G ^ 2 / (2 * (L * ‖a - x‖ ^ 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      have hm := hmin G (hgap.trans hfw'.le) (by
        have e : g (a - v) = G + g (x - v) := by rw [hG]; simp only [map_sub]; ring
        rw [e]; linarith)
      have := min_le_right (G / 2) (G ^ 2 / (2 * K))
      linarith

universe u

theorem sharp_away_linear : SharpAwayLinear.{u} := by
  intro E _ _ V f L c δ x S lam hL hc hδ hsc hconv hsm hsharp hrun xStar hxs t ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set ρ := min (1 / 2 : ℝ) (δ ^ 2 / (8 * c ^ 2 * L * D ^ 2)) with hρ
  have hρ0 : 0 ≤ ρ := le_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have inv := Lemmata.AwayStepFW.Proof.run_inv (NNReal.coe_nonneg L) hrun
  have hxP : ∀ t, x t ∈ convexHull ℝ (↑V : Set E) := fun t =>
    convexHull_mono (by exact_mod_cast (inv t).sub) (inv t).mem_convexHull
  have hh0 : ∀ t, 0 ≤ f (x t) - f xStar := fun t => by linarith [hxs.2 _ (hxP t)]
  have hout : ∀ t, (f (x (t + 1)) - f xStar ≤ (1 - ρ) * (f (x t) - f xStar) ∧
      (S (t + 1)).card ≤ (S t).card + 1) ∨
      (f (x (t + 1)) ≤ f (x t) ∧ (S (t + 1)).card + 1 = (S t).card) := by
    intro t
    obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hrun.2.2.2 t
    rcases afw_step_progress hL hconv hsm hxs (inv t) hvV hv ha haS hstep with ⟨h1, hc'⟩ | h
    · left
      refine ⟨?_, hc'⟩
      set h0 := f (x t) - f xStar with hh0def
      set gav := fderiv ℝ f (x t) (a - v) with hgav
      have hm : ρ * h0 ≤ min (h0 / 2) (gav ^ 2 / (8 * (L * D ^ 2))) := by
        rcases eq_or_lt_of_le (hh0 t) with hz | hpos
        · have hz' : h0 = 0 := by rw [hh0def]; exact hz.symm
          rw [hz']
          simp only [mul_zero, zero_div]
          exact le_min le_rfl (by positivity)
        apply le_min
        · nlinarith
        · rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ L * D ^ 2) with hK0 | hKpos
          · have : ρ ≤ 0 := by
              rw [hρ]; refine (min_le_right _ _).trans ?_
              rw [show (8 : ℝ) * c ^ 2 * L * D ^ 2 = 8 * c ^ 2 * (L * D ^ 2) by ring, ← hK0]
              simp
            rw [← hK0]; simp only [mul_zero, div_zero]; nlinarith
          · have hgeo := Proof.geometric_sharpness V f c (1 / 2) δ hconv hsm.1 hc hδ hsc hsharp
              xStar hxs (S t) (inv t).sub (x t) (inv t).mem_convexHull (by linarith) a ha haS v hvV
              hv
            set r := h0 ^ (1 - 1 / 2 : ℝ) with hr
            have hr0 : 0 ≤ r := Real.rpow_nonneg hpos.le _
            have hr2 : r ^ 2 = h0 := by
              rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
                show ((1 : ℝ) - 1 / 2) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
            have h3 : r * δ ≤ gav * c := by
              rw [div_le_div_iff₀ hc hδ] at hgeo; exact hgeo
            have h4 : 0 ≤ gav := by
              have := mul_nonneg hr0 hδ.le
              by_contra hneg; push Not at hneg
              nlinarith
            have h5 : (r * δ) ^ 2 ≤ (gav * c) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
            rw [mul_pow, mul_pow, hr2] at h5
            have hqle : ρ ≤ δ ^ 2 / (8 * c ^ 2 * L * D ^ 2) := min_le_right _ _
            calc ρ * h0 ≤ δ ^ 2 / (8 * c ^ 2 * L * D ^ 2) * h0 :=
                  mul_le_mul_of_nonneg_right hqle hpos.le
              _ ≤ gav ^ 2 / (8 * (L * D ^ 2)) := by
                have hp1 : (0 : ℝ) < 8 * c ^ 2 * L * D ^ 2 := by
                  have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) (pow_pos hc 2)) hKpos
                  linarith
                rw [div_mul_eq_mul_div, div_le_div_iff₀ hp1 (by linarith)]
                have := mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ 8 * (L * D ^ 2))
                nlinarith
      linarith
    · right; exact h
  have hstate : ∀ n, ∃ G Dr : ℕ, G + Dr = n ∧ (S (n + 1)).card + Dr ≤ (S 1).card + G ∧
      f (x (n + 1)) - f xStar ≤ (1 - ρ) ^ G * (L * D ^ 2 / 2) := by
    intro n
    induction n with
    | zero =>
      exact ⟨0, 0, rfl, le_rfl, by
        simpa using Lemmata.AwayStepFW.Proof.first_step_bound hL hconv hsm hxs hrun⟩
    | succ n ih =>
      obtain ⟨G, Dr, hsum, hcard, hbd⟩ := ih
      rcases hout (n + 1) with ⟨h1, hc'⟩ | ⟨h1, hc'⟩
      · refine ⟨G + 1, Dr, by omega, by omega, ?_⟩
        calc f (x (n + 1 + 1)) - f xStar ≤ (1 - ρ) * (f (x (n + 1)) - f xStar) := h1
          _ ≤ (1 - ρ) * ((1 - ρ) ^ G * (L * D ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left hbd (by linarith)
          _ = (1 - ρ) ^ (G + 1) * (L * D ^ 2 / 2) := by ring
      · exact ⟨G, Dr + 1, by omega, by omega, by linarith⟩
  have hS1 : (S 1).card ≤ 2 := by
    rcases hout 0 with ⟨-, hc'⟩ | ⟨-, hc'⟩ <;>
      simp only [zero_add, hrun.2.1, Finset.card_singleton] at hc' <;> omega
  obtain ⟨G, Dr, hsum, hcard, hbd⟩ := hstate (t - 1)
  rw [show t - 1 + 1 = t by omega] at hcard hbd
  have hSt : 1 ≤ (S t).card := by
    rcases Nat.eq_zero_or_pos (S t).card with h0 | h0
    · have := (inv t).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
  have hG : (t - 1) / 2 ≤ G := by omega
  calc f (x t) - f xStar ≤ (1 - ρ) ^ G * (L * D ^ 2 / 2) := hbd
    _ ≤ (1 - ρ) ^ ((t - 1) / 2) * (L * D ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by linarith) (by linarith) hG)
        (by positivity)

end Proof

end Lemmata.CGImprovements
