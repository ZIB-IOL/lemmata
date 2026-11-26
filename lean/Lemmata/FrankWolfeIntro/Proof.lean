module

public import Lemmata.FrankWolfeIntro.Statement
public import Lemmata.FrankWolfe.Main
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Proofs of the statements

Lemma 4.2 from the tangent-cone characterization of minima and first-order convexity;
Proposition 4.6 by induction on `f'(x⋆)(x_t - x⋆)`; Theorem 4.7 by summing the progress
inequality over the run.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Frank–Wolfe gap is attained at the oracle's answer. -/
theorem fwGap_eq_lmo {C : Set E} {lmo : StrongDual ℝ E → E} (hlmo : IsLMO C lmo)
    (f' : E → StrongDual ℝ E) (x : E) : fwGap C f' x = f' x (x - lmo (f' x)) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨lmo (f' x), (hlmo _).1, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have := (hlmo (f' x)).2 v hv
  simp only [map_sub]
  linarith

/-- At a minimizer over a convex set, `0 ≤ f'(x⋆)(v - x⋆)` for every feasible `v`. -/
theorem fderiv_nonneg_of_mem_minimizers {C : Set E} (hC : Convex ℝ C) {f : E → ℝ}
    (hf : Differentiable ℝ f) {xStar : E} (hxs : xStar ∈ minimizers C f) {v : E} (hv : v ∈ C) :
    0 ≤ fderiv ℝ f xStar (v - xStar) := by
  have hloc : IsLocalMinOn f C xStar := (isMinOn_iff.mpr hxs.2).isLocalMinOn
  exact hloc.hasFDerivWithinAt_nonneg (hf xStar).hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hxs.1 hv))

theorem first_order_optimality : FirstOrderOptimality.{u} := by
  intro E _ _ C f _ hCc hconv hdiff xStar hxC
  have hiff : xStar ∈ minimizers C f ↔ ∀ v ∈ C, fderiv ℝ f xStar (xStar - v) ≤ 0 := by
    constructor
    · intro hxs v hv
      have := fderiv_nonneg_of_mem_minimizers hCc hdiff hxs hv
      rw [show xStar - v = -(v - xStar) by abel, map_neg]
      linarith
    · intro h
      refine ⟨hxC, fun y hy => ?_⟩
      have h1 := add_fderiv_le_of_convexOn hconv hdiff xStar y
      have h2 := h y hy
      rw [show xStar - y = -(y - xStar) by abel, map_neg] at h2
      linarith
  refine ⟨hiff, fun hxs => ?_⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨xStar, hxC, by simp⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hiff.mp hxs v hv

theorem fixed_lower_bound : FixedLowerBound.{u} := by
  intro E _ _ C lmo f L h step hstep xStar hxs x₀ hx₀ t ht
  set x := fwIterates lmo (fderiv ℝ f) step x₀ with hxdef
  have hmem := fwIterates_mem h.convex h.lmo_mem (fderiv ℝ f) hstep hx₀
  have key : ∀ n, 1 ≤ n → (∏ τ ∈ Finset.Ico 1 n, (1 - step τ (x τ))) *
      fderiv ℝ f xStar (x 1 - xStar) ≤ fderiv ℝ f xStar (x n - xStar) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.prod_Ico_succ_top hn]
      have hγ := hstep n (x n) (hmem n)
      have hv := fderiv_nonneg_of_mem_minimizers h.convex h.isSmooth.1 hxs
        (h.lmo_mem (fderiv ℝ f (x n)))
      have hsucc : x (n + 1) - xStar = (1 - step n (x n)) • (x n - xStar) +
          step n (x n) • (lmo (fderiv ℝ f (x n)) - xStar) := by
        show fwStep lmo (fderiv ℝ f) (x n) (step n (x n)) - xStar = _
        simp only [fwStep]
        module
      rw [hsucc, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have h1 : 0 ≤ 1 - step n (x n) := by linarith [hγ.2]
      have h2 := mul_le_mul_of_nonneg_left ih h1
      have h3 := mul_nonneg hγ.1 hv
      have h4 : (∏ τ ∈ Finset.Ico 1 n, (1 - step τ (x τ))) * (1 - step n (x n)) *
          fderiv ℝ f xStar (x 1 - xStar) = (1 - step n (x n)) *
          ((∏ τ ∈ Finset.Ico 1 n, (1 - step τ (x τ))) * fderiv ℝ f xStar (x 1 - xStar)) := by ring
      linarith
  have hconvx := add_fderiv_le_of_convexOn h.convexOn h.isSmooth.1 xStar (x t)
  have := key t ht
  linarith

theorem fixed_lower_bound_open_loop : FixedLowerBoundOpenLoop.{u} := by
  intro E _ _ C lmo f L h xStar hxs x₀ hx₀ t ht
  have hstep : ∀ t, ∀ x ∈ C, (openLoopStep 2 : ℕ → E → ℝ) t x ∈ Set.Icc (0 : ℝ) 1 :=
    fun t _ _ => by
      show (2 : ℝ) / ((t : ℝ) + 2) ∈ Set.Icc (0 : ℝ) 1
      exact ⟨by positivity, by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]⟩
  have hb := fixed_lower_bound C lmo f L h (openLoopStep 2) hstep xStar hxs x₀ hx₀ t ht
  have hprod : ∀ n, 1 ≤ n → (∏ τ ∈ Finset.Ico 1 n, (1 - (openLoopStep 2 : ℕ → E → ℝ) τ
      (fwIterates lmo (fderiv ℝ f) (openLoopStep 2) x₀ τ))) = 2 / ((n : ℝ) * (n + 1)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.prod_Ico_succ_top hn, ih]
      show 2 / ((n : ℝ) * (n + 1)) * (1 - 2 / ((n : ℝ) + 2)) =
        2 / (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1))
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      field_simp
      ring
  rw [hprod t ht] at hb
  exact hb

theorem nonconvex_rate : NonconvexRate.{u} := by
  intro E _ _ C lmo f L hC hCc hlmo hsm xStar hxs x₀ hx₀ T
  set s := Real.sqrt ((T : ℝ) + 1) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = (T : ℝ) + 1 := Real.sq_sqrt (by positivity)
  set γ : ℝ := 1 / s with hγ
  have hγ01 : γ ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [hγ, div_le_one hspos]
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  set x := fwIterates lmo (fderiv ℝ f) (fun _ _ => γ) x₀ with hx
  have hmem : ∀ t, x t ∈ C :=
    fwIterates_mem hCc (fun g => (hlmo g).1) (fderiv ℝ f) (fun _ _ _ => hγ01) hx₀
  set D := Metric.diam C with hD
  set g : ℕ → ℝ := fun t => fderiv ℝ f (x t) (x t - lmo (fderiv ℝ f (x t))) with hg
  have hstep : ∀ t, f (x (t + 1)) ≤ f (x t) - γ * g t + γ ^ 2 * L / 2 * D ^ 2 := by
    intro t
    have hprog := hsm.progress (x t) (lmo (fderiv ℝ f (x t))) γ
    have hd : ‖lmo (fderiv ℝ f (x t)) - x t‖ ≤ D := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hC.isBounded (hlmo _).1 (hmem t)
    have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hL : (0 : ℝ) ≤ γ ^ 2 * L / 2 := by positivity
    have hsucc : x (t + 1) = x t + γ • (lmo (fderiv ℝ f (x t)) - x t) := rfl
    rw [hsucc]
    nlinarith [mul_le_mul_of_nonneg_left hd2 hL]
  have hsum : ∀ n : ℕ, f (x n) ≤
      f x₀ - γ * ∑ t ∈ Finset.range n, g t + n * (γ ^ 2 * L / 2 * D ^ 2) := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, Nat.cast_zero,
        zero_mul, add_zero]; exact le_rfl
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hstep n
      push_cast
      nlinarith
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image (Finset.range (T + 1)) g ⟨0, by simp⟩
  refine ⟨t, Nat.lt_succ_iff.mp (Finset.mem_range.mp ht), ?_⟩
  rw [fwGap_eq_lmo hlmo]
  have hge : ((T : ℝ) + 1) * g t ≤ ∑ τ ∈ Finset.range (T + 1), g τ := by
    have := Finset.card_nsmul_le_sum (Finset.range (T + 1)) g (g t) (fun τ hτ => hmin τ hτ)
    rw [Finset.card_range, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have hlast := hsum (T + 1)
  have hfx : f xStar ≤ f (x (T + 1)) := hxs.2 _ (hmem (T + 1))
  have hh0 : 0 ≤ f x₀ - f xStar := by linarith [hxs.2 x₀ hx₀]
  have hγ2 : ((T : ℝ) + 1) * γ ^ 2 = 1 := by rw [hγ, ← hs2]; field_simp
  have hterm : (((T + 1 : ℕ) : ℝ)) * (γ ^ 2 * L / 2 * D ^ 2) = L * D ^ 2 / 2 := by
    push_cast
    rw [show ((T : ℝ) + 1) * (γ ^ 2 * L / 2 * D ^ 2) = ((T : ℝ) + 1) * γ ^ 2 * (L * D ^ 2 / 2) by
      ring, hγ2, one_mul]
  have hγs : γ * ((T : ℝ) + 1) = s := by rw [hγ, ← hs2]; field_simp
  have hmain : s * g t ≤ (f x₀ - f xStar) + L * D ^ 2 / 2 := by
    have hsumγ : γ * ∑ τ ∈ Finset.range (T + 1), g τ ≤ f x₀ - f xStar + L * D ^ 2 / 2 := by
      linarith
    calc s * g t = γ * (((T : ℝ) + 1) * g t) := by rw [← hγs]; ring
      _ ≤ γ * ∑ τ ∈ Finset.range (T + 1), g τ := mul_le_mul_of_nonneg_left hge hγ01.1
      _ ≤ _ := hsumγ
  rw [le_div_iff₀ hspos]
  have hmax : (f x₀ - f xStar) + L * D ^ 2 / 2 ≤ max (2 * (f x₀ - f xStar)) (L * D ^ 2) := by
    rcases le_total (2 * (f x₀ - f xStar)) (L * D ^ 2) with hle | hle
    · rw [max_eq_right hle]; linarith
    · rw [max_eq_left hle]; linarith
  nlinarith [hmain, hmax]

end Proof

end Lemmata.FrankWolfeIntro
