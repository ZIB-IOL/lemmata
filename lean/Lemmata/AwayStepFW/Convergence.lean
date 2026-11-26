module

public import Lemmata.AwayStepFW.Progress

@[expose] public section

/-!
# Linear convergence of away-step Frank–Wolfe (Theorem 2.29)

The first step is a Frank–Wolfe step and gives `h₁ ≤ L D²/2`. Every later step is good (the gap
contracts and the active set grows by at most one vertex) or a drop step (the gap does not grow and
the active set loses a vertex). Since active sets are nonempty and `|S₁| ≤ 2`, at most one more
drop step than good steps occurs, so at least `⌊(t-1)/2⌋` of the first `t - 1` steps are good.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem first_step_bound {V : Finset E} {f : E → ℝ} {L : NNReal} (hL : 0 < (L : ℝ))
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L) {xStar : E}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f) {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} (h : IsAFWRun V f L x S lam) :
    f (x 1) - f xStar ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 := by
  classical
  have inv := run_inv (NNReal.coe_nonneg L) h
  obtain ⟨hx0, hS0, -, hsteps⟩ := h
  obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hsteps 0
  rw [hS0, Finset.mem_singleton] at ha
  set g := fderiv ℝ f (x 0) with hg
  have hxV : x 0 ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hx0)
  have hvC : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hvV)
  have hgFW : 0 ≤ g (x 0 - v) := by rw [map_sub]; linarith [(inv 0).le_apply g hv]
  have hbdd : Bornology.IsBounded (convexHull ℝ (↑V : Set E)) :=
    isBounded_convexHull.mpr V.finite_toSet.isBounded
  have hdD : ‖x 0 - v‖ ≤ Metric.diam (↑V : Set E) := by
    rw [← dist_eq_norm, ← convexHull_diam]; exact Metric.dist_le_diam_of_mem hbdd hxV hvC
  have hG : f (x 0) - f xStar ≤ g (x 0 - v) := by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x 0) xStar
    have h2 := le_of_min_vertex g hv hxs.1
    rw [map_sub] at h1 ⊢
    linarith
  unfold IsAFWStep at hstep
  split_ifs at hstep with hfw
  · dsimp only at hstep
    obtain ⟨hx', -, -⟩ := hstep
    set G := g (x 0 - v) with hGdef
    rcases eq_or_lt_of_le (norm_nonneg (x 0 - v)) with hd0 | hdpos
    · have hxv : x 0 - v = 0 := norm_eq_zero.mp hd0.symm
      have hG0 : G = 0 := by rw [hGdef, hxv, map_zero]
      rw [hx', hxv, smul_zero, sub_zero]
      have : 0 ≤ (L : ℝ) * Metric.diam (↑V : Set E) ^ 2 / 2 := by positivity
      linarith
    · have hc : 0 < (L : ℝ) * ‖x 0 - v‖ ^ 2 := by positivity
      set γ := min (G / (L * ‖x 0 - v‖ ^ 2)) 1 with hγ
      have hprog : f (x 1) ≤ f (x 0) - γ * G + γ ^ 2 * L / 2 * ‖v - x 0‖ ^ 2 := by
        have := hsm.progress (x 0) v γ
        rw [show x 0 + γ • (v - x 0) = x 1 by rw [hx']; module] at this
        exact this
      rw [norm_sub_rev v (x 0)] at hprog
      have hcD : (L : ℝ) * ‖x 0 - v‖ ^ 2 ≤ L * Metric.diam (↑V : Set E) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdD 2) (NNReal.coe_nonneg L)
      rcases le_total (G / (L * ‖x 0 - v‖ ^ 2)) 1 with hle | hle
      · rw [min_eq_left hle] at hγ
        have hval : γ * G - γ ^ 2 * L / 2 * ‖x 0 - v‖ ^ 2 = G ^ 2 / (2 * (L * ‖x 0 - v‖ ^ 2)) := by
          rw [hγ]; field_simp; ring
        have hsq : G - G ^ 2 / (2 * (L * ‖x 0 - v‖ ^ 2)) ≤ L * ‖x 0 - v‖ ^ 2 / 2 := by
          rw [sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity),
            le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (G - L * ‖x 0 - v‖ ^ 2)]
        linarith
      · rw [min_eq_right hle] at hγ
        rw [hγ] at hprog
        have hcG : (L : ℝ) * ‖x 0 - v‖ ^ 2 ≤ G := by rwa [le_div_iff₀ hc, one_mul] at hle
        nlinarith
  · exfalso
    apply hfw
    rw [ha, sub_self, map_zero]
    exact hgFW

theorem away_step_convergence : AwayStepConvergence.{u} := by
  intro E _ _ V f L μ δ x S lam hL hμ hδ hsc hconv hsm hstrong h xStar hxs t ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  set ρ := min (1 / 2) (μ * δ ^ 2 / (4 * L * D ^ 2)) with hρ
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ0 : 0 ≤ ρ := le_min (by norm_num) (by positivity)
  have hq0 : 0 ≤ 1 - ρ := by linarith
  have hq1 : 1 - ρ ≤ 1 := by linarith
  have inv := run_inv (NNReal.coe_nonneg L) h
  have hout : ∀ s, (f (x (s + 1)) - f xStar ≤ (1 - ρ) * (f (x s) - f xStar) ∧
      (S (s + 1)).card ≤ (S s).card + 1) ∨
      (f (x (s + 1)) ≤ f (x s) ∧ (S (s + 1)).card + 1 = (S s).card) := by
    intro s
    obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := h.2.2.2 s
    exact step_outcome hL hμ hδ hsc hconv hsm hstrong hxs (inv s) hvV hv ha haS hstep
  have hbase := first_step_bound hL hconv hsm hxs h
  have hne : ∀ s, 1 ≤ (S s).card := fun s =>
    Finset.card_pos.mpr (Finset.nonempty_of_sum_ne_zero (by rw [(inv s).sum]; norm_num))
  have hS0 : (S 0).card = 1 := by rw [h.2.1]; simp
  have hS1 : (S 1).card ≤ 2 := by
    rcases hout 0 with ⟨-, h0⟩ | ⟨-, h0⟩
    · simp only [zero_add] at h0; omega
    · simp only [zero_add] at h0; have := hne 1; omega
  have key : ∀ t, 1 ≤ t → ∃ k b : ℕ, k + b = t - 1 ∧
      f (x t) - f xStar ≤ (1 - ρ) ^ k * (L * D ^ 2 / 2) ∧ (S t).card + b ≤ (S 1).card + k := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨0, 0, rfl, by simpa using hbase, le_refl _⟩
    | succ t ht ih =>
      obtain ⟨k, b, hkb, hh, hcard⟩ := ih
      rcases hout t with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨k + 1, b, by omega, ?_, by omega⟩
        calc f (x (t + 1)) - f xStar ≤ (1 - ρ) * (f (x t) - f xStar) := h1
          _ ≤ (1 - ρ) * ((1 - ρ) ^ k * (L * D ^ 2 / 2)) := mul_le_mul_of_nonneg_left hh hq0
          _ = (1 - ρ) ^ (k + 1) * (L * D ^ 2 / 2) := by ring
      · exact ⟨k, b + 1, by omega, by linarith, by omega⟩
  obtain ⟨k, b, hkb, hh, hcard⟩ := key t ht
  have hk : (t - 1) / 2 ≤ k := by have := hne t; omega
  calc f (x t) - f xStar ≤ (1 - ρ) ^ k * (L * D ^ 2 / 2) := hh
    _ ≤ (1 - ρ) ^ ((t - 1) / 2) * (L * D ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 hk) (by positivity)

end Proof

end Lemmata.AwayStepFW
