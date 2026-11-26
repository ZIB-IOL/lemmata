module

public import Lemmata.AwayStepFW.Invariants
public import Lemmata.AwayStepFW.Geometry
public import Lemmata.FrankWolfe.Proof.Calculus
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-!
# One step of away-step Frank–Wolfe

The chosen direction has gap `G ≥ ½ f'(x)(a - v)`, and geometric strong convexity gives
`f'(x)(a - v)² ≥ 2 μ δ² h`. A step that is not a drop step uses the short step `G / (L ‖d‖²)` or the
full Frank–Wolfe step, and contracts the primal gap by `1 - min {1/2, μ δ²/(4 L D²)}`; a drop step
does not increase it.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem le_of_min_vertex {V : Finset E} (g : StrongDual ℝ E) {v : E} (hv : ∀ w ∈ V, g v ≤ g w)
    {y : E} (hy : y ∈ convexHull ℝ (↑V : Set E)) : g v ≤ g y := by
  have hsub : (↑V : Set E) ⊆ {z | g v ≤ g z} := fun w hw => hv w hw
  exact convexHull_min hsub (convex_halfSpace_ge g.toLinearMap.isLinear _) hy

theorem step_outcome {V : Finset E} {f : E → ℝ} {L : NNReal} {μ δ : ℝ} (hL : 0 < (L : ℝ))
    (hμ : 0 < μ) (hδ : 0 < δ) (hsc : IsScaling V δ) (hconv : ConvexOn ℝ Set.univ f)
    (hsm : IsSmooth f L)
    (hstrong : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    {xStar : E} (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f)
    {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam) {v a : E} (hvV : v ∈ V)
    (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : IsAFWStep L (fderiv ℝ f x) x S lam v a x' S' lam') :
    (f x' - f xStar ≤ (1 - min (1 / 2) (μ * δ ^ 2 / (4 * L * Metric.diam (↑V : Set E) ^ 2))) *
        (f x - f xStar) ∧ S'.card ≤ S.card + 1) ∨
      (f x' ≤ f x ∧ S'.card + 1 = S.card) := by
  classical
  set ρ := min (1 / 2) (μ * δ ^ 2 / (4 * L * Metric.diam (↑V : Set E) ^ 2)) with hρ
  set D := Metric.diam (↑V : Set E) with hD
  set g := fderiv ℝ f x with hg
  have hxV : x ∈ convexHull ℝ (↑V : Set E) :=
    convexHull_mono (by exact_mod_cast h.sub) h.mem_convexHull
  have hbdd : Bornology.IsBounded (convexHull ℝ (↑V : Set E)) :=
    isBounded_convexHull.mpr V.finite_toSet.isBounded
  have hdist : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D :=
    fun y hy z hz => by
      rw [← dist_eq_norm, hD, ← convexHull_diam]; exact Metric.dist_le_diam_of_mem hbdd hy hz
  have hvC : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast hvV)
  have haC : a ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (by exact_mod_cast h.sub ha)
  have hh0 : 0 ≤ f x - f xStar := sub_nonneg.mpr (hxs.2 x hxV)
  have hgFW : 0 ≤ g (x - v) := by rw [map_sub]; linarith [h.le_apply g hv]
  have hgA : 0 ≤ g (a - x) := by rw [map_sub]; linarith [h.apply_le g haS]
  have hgeo := geometric_strong_convexity V f μ δ hμ hδ hsc hstrong xStar hxs S h.sub x
    h.mem_convexHull a ha haS v hvV hv
  have hsplit : g (a - v) = g (a - x) + g (x - v) := by rw [map_sub, map_sub, map_sub]; ring
  have hFWgap : f x - f xStar ≤ g (x - v) := by
    have h1 := add_fderiv_le_of_convexOn hconv hsm.1 x xStar
    have h2 := le_of_min_vertex g hv hxs.1
    rw [map_sub] at h1 ⊢
    linarith
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ2 : ρ ≤ μ * δ ^ 2 / (4 * L * D ^ 2) := min_le_right _ _
  -- the progress `G² / (2 L D²)` of a full short step with gap `G ≥ ½ g(a - v)` beats `ρ h`
  have hgood : ∀ G : ℝ, 0 ≤ G → g (a - v) ≤ 2 * G → 0 < D →
      f x - f xStar - G ^ 2 / (2 * L * D ^ 2) ≤ (1 - ρ) * (f x - f xStar) := by
    intro G hG hGa hDpos
    have h1 : 2 * μ * δ ^ 2 * (f x - f xStar) ≤ g (a - v) ^ 2 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ * δ ^ 2)).mp hgeo
      linarith
    have hga0 : 0 ≤ g (a - v) := by nlinarith [sq_nonneg (g (a - v))]
    have h2 : g (a - v) ^ 2 ≤ 4 * G ^ 2 := by
      have := pow_le_pow_left₀ (by linarith [hsplit, hgA, hgFW]) hGa 2
      nlinarith [this]
    have h3 : μ * δ ^ 2 / (4 * L * D ^ 2) * (f x - f xStar) ≤ G ^ 2 / (2 * L * D ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity : (0 : ℝ) ≤ L * D ^ 2)
      nlinarith [this]
    have h4 := mul_le_mul_of_nonneg_right hρ2 hh0
    linarith
  unfold IsAFWStep at hstep
  split_ifs at hstep with hfw
  · dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    left
    refine ⟨?_, ?_⟩
    · set G := g (x - v) with hG
      have hGa : g (a - v) ≤ 2 * G := by linarith
      rcases eq_or_lt_of_le (norm_nonneg (x - v)) with hd0 | hdpos
      · have hxv : x - v = 0 := norm_eq_zero.mp hd0.symm
        have hG0 : G = 0 := by rw [hG, hxv, map_zero]
        have hx'x : x' = x := by rw [hx', hxv, smul_zero, sub_zero]
        have hzero : f x - f xStar ≤ 0 := by
          have : g (a - v) ≤ 0 := by linarith
          have hga0 : g (a - v) = 0 := by linarith
          rw [hga0] at hgeo; simpa using hgeo
        rw [hx'x]; nlinarith
      · have hc : 0 < (L : ℝ) * ‖x - v‖ ^ 2 := by positivity
        have hdD : ‖x - v‖ ≤ D := hdist x hxV v hvC
        have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
        set γ := min (G / (L * ‖x - v‖ ^ 2)) 1 with hγ
        have hprog : f x' ≤ f x - γ * G + γ ^ 2 * L / 2 * ‖v - x‖ ^ 2 := by
          have := hsm.progress x v γ
          rw [show x + γ • (v - x) = x' by rw [hx']; module] at this
          exact this
        rw [norm_sub_rev v x] at hprog
        rcases le_total (G / (L * ‖x - v‖ ^ 2)) 1 with hle | hle
        · rw [min_eq_left hle] at hγ
          have hval : γ * G - γ ^ 2 * L / 2 * ‖x - v‖ ^ 2 = G ^ 2 / (2 * (L * ‖x - v‖ ^ 2)) := by
            rw [hγ]; field_simp; ring
          have hcmp : G ^ 2 / (2 * L * D ^ 2) ≤ G ^ 2 / (2 * (L * ‖x - v‖ ^ 2)) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
              (by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdD 2])
          have := hgood G hgFW hGa hDpos
          linarith
        · rw [min_eq_right hle] at hγ
          rw [hγ] at hprog
          have hcG : (L : ℝ) * ‖x - v‖ ^ 2 ≤ G := by
            rwa [le_div_iff₀ hc, one_mul] at hle
          have h5 : f x' ≤ f x - G / 2 := by nlinarith [hprog, hcG]
          have h6 := mul_le_mul_of_nonneg_right hρ1 hh0
          linarith
    · rw [hS']
      split_ifs
      · simp
      · exact Finset.card_insert_le v S
  · dsimp only at hstep
    obtain ⟨hx', -, hS'⟩ := hstep
    set G := g (a - x) with hG
    have hGFW : g (x - v) < G := lt_of_not_ge hfw
    have hGa : g (a - v) ≤ 2 * G := by linarith
    have hdpos : 0 < ‖a - x‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (a - x)) with hd0 | hd0
      · exfalso
        apply hfw
        rw [hG, show a - x = 0 from norm_eq_zero.mp hd0.symm, map_zero]
        exact hgFW
      · exact hd0
    have hc : 0 < (L : ℝ) * ‖a - x‖ ^ 2 := by positivity
    have hdD : ‖a - x‖ ≤ D := hdist a haC x hxV
    have hDpos : 0 < D := lt_of_lt_of_le hdpos hdD
    set γmax := lam a / (1 - lam a) with hγmax
    set γ := min (G / (L * ‖a - x‖ ^ 2)) γmax with hγ
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hgA hc.le)
      (div_nonneg (h.nonneg a) (by linarith [h.lam_lt_one g hv ha hfw]))
    have hγle : γ ≤ G / (L * ‖a - x‖ ^ 2) := min_le_left _ _
    have hprog : f x' ≤ f x - γ * G + γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 := by
      have := hsm.le_quadratic x x'
      rw [hx', show x - γ • (a - x) - x = -(γ • (a - x)) by abel, map_neg, map_smul, smul_eq_mul,
        norm_neg, norm_smul, Real.norm_of_nonneg hγ0, mul_pow] at this
      have e : fderiv ℝ f x (a - x) = G := rfl
      rw [e] at this
      rw [hx']
      linarith
    have hdec : γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 ≤ γ * G / 2 := by
      have : γ * (L * ‖a - x‖ ^ 2) ≤ G := by rwa [le_div_iff₀ hc] at hγle
      calc γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 = γ / 2 * (γ * (L * ‖a - x‖ ^ 2)) := by ring
        _ ≤ γ / 2 * G := mul_le_mul_of_nonneg_left this (by positivity)
        _ = γ * G / 2 := by ring
    rcases eq_or_ne γ γmax with hdrop | hdrop
    · right
      have : 0 ≤ γ * G := mul_nonneg hγ0 hgA
      refine ⟨by linarith, ?_⟩
      rw [hS', ite_eq_left hdrop]
      exact Finset.card_erase_add_one ha
    · left
      have hγv : γ = G / (L * ‖a - x‖ ^ 2) := by
        rcases min_choice (G / (L * ‖a - x‖ ^ 2)) γmax with h1 | h1
        · rw [hγ, h1]
        · exact absurd (by rw [hγ, h1]) hdrop
      refine ⟨?_, ?_⟩
      · have hval : γ * G - γ ^ 2 * L / 2 * ‖a - x‖ ^ 2 = G ^ 2 / (2 * (L * ‖a - x‖ ^ 2)) := by
          rw [hγv]; field_simp; ring
        have hcmp : G ^ 2 / (2 * L * D ^ 2) ≤ G ^ 2 / (2 * (L * ‖a - x‖ ^ 2)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
            (by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdD 2])
        have := hgood G hgA hGa hDpos
        linarith
      · rw [hS', ite_eq_right hdrop]; omega

end Proof

end Lemmata.AwayStepFW
