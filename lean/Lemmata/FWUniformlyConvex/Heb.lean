module

public import Lemmata.FWUniformlyConvex.Local

@[expose] public section

/-!
# Rates under a Hölderian error bound (Theorem 2.10)

With the error bound, `‖f'(x_t)‖ ≥ h_t^{1-θ}/μ`, so the progress estimate over uniformly convex sets
from the basics entry (`uc_progress`) applies with `β = α h_t^{1-θ}/μ`. The exponents combine to
`h_t · min {1/2, c h_t^{1 - 2θ/q}}`, and the contraction lemma of the basics entry turns this
recursion into the rate.
-/

namespace Lemmata.FWUniformlyConvex

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 2.10.** -/
theorem heb_rate_bound {C : Set E} {f : E → ℝ} {L : NNReal} {α q μ θ : ℝ} {x v : ℕ → E}
    {γ : ℕ → ℝ} (hCc : IsCompact C) (hC : Convex ℝ C) (hUC : IsUniformlyConvexSet C α q)
    (hq : 2 ≤ q) (hα : 0 < α) (hL : 0 < (L : ℝ)) (hD : 0 < Metric.diam C)
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L) (heb : IsHolderErrorBound C f μ θ)
    (hμ : 0 < μ) (hθ : θ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hrun : IsShortStepRun C f L x v γ)
    {xStar : E} (hxs : xStar ∈ minimizers C f) (t : ℕ) (ht : 1 ≤ t) :
    let a := 1 - 2 * θ / q
    let K := ((L : ℝ) * (μ / α) ^ (2 / q)) ^ (1 / a)
    let t₀ : ℤ := max (⌊Real.logb (1 / 2) (2 * K / (L * Metric.diam C ^ 2))⌋ + 2) 1
    ((t : ℤ) < t₀ → f (x t) - f xStar ≤ L * Metric.diam C ^ 2 / 2 * (1 / 2) ^ (t - 1)) ∧
      (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤ K / (1 + a / 2 * ((t : ℝ) - t₀)) ^ (1 / a)) := by
  intro a K t₀
  set D := Metric.diam C with hDdef
  have hq0 : 0 < q := by linarith
  have ha : 0 < a := by
    show 0 < 1 - 2 * θ / q
    have : 2 * θ / q ≤ 1 / 2 := by
      rw [div_le_iff₀ hq0]; nlinarith [hθ.2]
    linarith
  set h : ℕ → ℝ := fun τ => f (x τ) - f xStar with hh
  have hfacts := Lemmata.CGBasics.Proof.run_step hC hconv hsm hrun hxs
  have h0 : ∀ τ, 0 ≤ h τ := fun τ => by simp only [hh]; linarith [hxs.2 _ (hfacts τ).1]
  have hmono : ∀ τ, h (τ + 1) ≤ h τ := fun τ => by
    have := (hfacts τ).2.2.2 0 ⟨le_rfl, zero_le_one⟩
    simp only [hh]; simp at this; linarith
  have h1 : h 1 ≤ L * D ^ 2 / 2 := by
    have := (Lemmata.CGBasics.Proof.vanilla_rate C f L x v γ hCc hC hconv hsm hrun.1 hrun.2
      xStar hxs 1 le_rfl).1
    have e : 2 * (L : ℝ) * D ^ 2 / (((1 : ℕ) : ℝ) + 3) = L * D ^ 2 / 2 := by push_cast; ring
    simp only [hh]; linarith
  set c₂ := (α / μ) ^ (2 / q) / (2 * L) with hc₂
  have hc₂pos : 0 < c₂ := by positivity
  have hconvC : ConvexOn ℝ C f := hconv.subset (Set.subset_univ C) hC
  have hdiffC : ∀ y ∈ C, DifferentiableAt ℝ f y := fun y _ => hsm.1 y
  have hstep : ∀ τ, 1 ≤ τ → 0 < h τ → h τ * min (1 / 2) (c₂ * h τ ^ a) ≤ h τ - h (τ + 1) := by
    intro τ _ hpos
    obtain ⟨hxC, hhg, -, hs⟩ := hfacts τ
    have hg := heb_grad_lower hconvC hdiffC heb hμ (by linarith [hθ.2]) hxs hxC
    obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 τ
    have hsc := Lemmata.CGBasics.Proof.uniformly_convex_scaling C α q hUC (fderiv ℝ f (x τ))
      (v τ) hvC hvmin (x τ) hxC
    set β := α * h τ ^ (1 - θ) / μ with hβ
    have hβpos : 0 < β := by
      have : 0 < h τ ^ (1 - θ) := Real.rpow_pos_of_pos hpos _
      positivity
    have hβle : β ≤ α * ‖fderiv ℝ f (x τ)‖ := by
      rw [hβ, div_le_iff₀ hμ]
      nlinarith [mul_le_mul_of_nonneg_left hg hα.le]
    have hscal : β * ‖v τ - x τ‖ ^ q ≤ fderiv ℝ f (x τ) (x τ - v τ) := by
      rw [norm_sub_rev]
      calc β * ‖x τ - v τ‖ ^ q ≤ α * ‖fderiv ℝ f (x τ)‖ * ‖x τ - v τ‖ ^ q :=
            mul_le_mul_of_nonneg_right hβle (Real.rpow_nonneg (norm_nonneg _) _)
        _ ≤ _ := hsc
    have hp := Lemmata.CGBasics.Proof.uc_progress hL hq hβpos hhg (h0 τ) (norm_nonneg _) hscal hs
    have e : β ^ (2 / q) * h τ ^ (1 - 2 / q) / (2 * L) = c₂ * h τ ^ a := by
      have e1 : β ^ (2 / q) = (α / μ) ^ (2 / q) * h τ ^ ((1 - θ) * (2 / q)) := by
        rw [hβ, show α * h τ ^ (1 - θ) / μ = (α / μ) * h τ ^ (1 - θ) by ring,
          Real.mul_rpow (by positivity) (Real.rpow_nonneg (h0 τ) _), ← Real.rpow_mul (h0 τ)]
      have e2 : h τ ^ ((1 - θ) * (2 / q)) * h τ ^ (1 - 2 / q) = h τ ^ a := by
        rw [← Real.rpow_add hpos]
        congr 1
        show _ = 1 - 2 * θ / q
        ring
      rw [e1, hc₂, mul_assoc, e2]
      ring
    rw [e] at hp
    simp only [hh]
    linarith
  have hra := Lemmata.CGBasics.Proof.rate_assembly h (L * D ^ 2 / 2) c₂ a (by positivity) hc₂pos
    ha h0 hmono h1 hstep t ht
  have eK : (1 / 2 / c₂) ^ (1 / a) = K := by
    show _ = ((L : ℝ) * (μ / α) ^ (2 / q)) ^ (1 / a)
    congr 1
    have hinv : (μ / α) ^ (2 / q) = ((α / μ) ^ (2 / q))⁻¹ := by
      rw [← Real.inv_rpow (by positivity), inv_div]
    rw [hc₂, hinv]
    have : 0 < (α / μ) ^ (2 / q) := by positivity
    field_simp
  have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have eT : K / (L * D ^ 2 / 2) = 2 * K / (L * D ^ 2) := by field_simp
  have ea : 1 / 2 * a = a / 2 := by ring
  simp only [e1] at hra
  rw [eK, eT, ea] at hra
  exact hra

namespace Proof

theorem heb_rate : HEBRate.{u} := by
  intro E _ _ C f L α q μ θ x v γ hCc hC hUC hq hα hL hD hconv hsm heb hμ hθ hrun xStar hxs a K t₀ t
    ht
  exact heb_rate_bound hCc hC hUC hq hα hL hD hconv hsm heb hμ hθ hrun hxs t ht

end Proof

end Lemmata.FWUniformlyConvex
