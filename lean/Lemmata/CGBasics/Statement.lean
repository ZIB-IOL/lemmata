module

public import Lemmata.FrankWolfe.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

universe u

/-- **Lemma 1.7** (smoothness and Lipschitz gradients). For a convex differentiable `f` on a real
normed space, the quadratic upper bound `f y ≤ f x + f'(x)(y - x) + L/2 ‖y - x‖²` holds for all
`x, y` if and only if the derivative is `L`-Lipschitz. -/
def SmoothIffLipschitz : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal),
    ConvexOn ℝ Set.univ f → Differentiable ℝ f →
      ((∀ x y : E, f y ≤ f x + fderiv ℝ f x (y - x) + L / 2 * ‖y - x‖ ^ 2) ↔
        LipschitzWith L (fderiv ℝ f))

/-- **Proposition 1.12** (the Frank–Wolfe gap from the primal gap). Let `f` be `L`-smooth, not
necessarily convex, and `C` convex and bounded with diameter `D`, and let `x⋆` minimize `f` on `C`.
For `x ∈ C` with primal gap `h = f x - f x⋆`, every `v ∈ C` satisfies
`f'(x)(x - v) ≤ h + L D²/2` if `h ≥ L D²/2`, and `f'(x)(x - v) ≤ D √(2 L h)` if `h ≤ L D²/2`. -/
def GapByPrimalGap : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal),
    IsSmooth f L → Convex ℝ C → Bornology.IsBounded C →
    ∀ xStar ∈ minimizers C f, ∀ x ∈ C, ∀ v ∈ C,
      (L * Metric.diam C ^ 2 / 2 ≤ f x - f xStar →
        fderiv ℝ f x (x - v) ≤ f x - f xStar + L * Metric.diam C ^ 2 / 2) ∧
      (f x - f xStar ≤ L * Metric.diam C ^ 2 / 2 →
        fderiv ℝ f x (x - v) ≤ Metric.diam C * Real.sqrt (2 * L * (f x - f xStar)))

/-- **Lemma 2.13** (primal gap bound via strong convexity). Let `f` be `μ`-strongly convex on a
convex set `C`, with `μ > 0`, and let `x⋆` minimize `f` on `C`. Then for every `x ∈ C`,
`f x - f x⋆ ≤ f'(x)(x - x⋆)² / (2 μ ‖x - x⋆‖²) ≤ ‖f'(x)‖² / (2 μ)`. -/
def PrimalGapStrongConvexity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (μ : ℝ),
    0 < μ → (∀ x ∈ C, ∀ y ∈ C, f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    ∀ xStar ∈ minimizers C f, ∀ x ∈ C,
      f x - f xStar ≤ fderiv ℝ f x (x - xStar) ^ 2 / (2 * μ * ‖x - xStar‖ ^ 2) ∧
      fderiv ℝ f x (x - xStar) ^ 2 / (2 * μ * ‖x - xStar‖ ^ 2) ≤ ‖fderiv ℝ f x‖ ^ 2 / (2 * μ)

/-- **Proposition 2.16** (scaling condition for an interior minimizer). Let `f` be convex and
differentiable, let `x⋆` minimize `f` on `C`, and let the closed ball of radius `r > 0` around `x⋆`
lie in `C`. For every `x ∈ C` and every minimizer `v` of `f'(x)` on `C`,
`f'(x)(x - v) ≥ r ‖f'(x)‖ ≥ r f'(x)(x - x⋆) / ‖x - x⋆‖`. -/
def ScalingInterior : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (r : ℝ),
    ConvexOn ℝ Set.univ f → Differentiable ℝ f →
    ∀ xStar ∈ minimizers C f, 0 < r → Metric.closedBall xStar r ⊆ C →
    ∀ x ∈ C, ∀ v ∈ C, (∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
      r * ‖fderiv ℝ f x‖ ≤ fderiv ℝ f x (x - v) ∧
      r * fderiv ℝ f x (x - xStar) / ‖x - xStar‖ ≤ r * ‖fderiv ℝ f x‖

/-- **Theorem 2.17** (linear convergence for an interior minimizer). Under the standing
assumptions, let `x⋆` minimize `f` on `C` with the closed ball of radius `r > 0` around `x⋆` in `C`,
and let `f` be `c`-gradient dominated: `f x - f x⋆ ≤ c² ‖f'(x)‖²` on `C`. With short steps or exact
line search, `f(x_t) - f(x⋆) ≤ q^t L D²/2` for all `t`, where `q = max {1 - r²/(2 L c² D²), 0}`. -/
def LinearRateInterior : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (lmo : StrongDual ℝ E → E) (f : E → ℝ) (L : NNReal) (c r : ℝ),
    StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f (fderiv ℝ f) σ →
    ∀ xStar ∈ minimizers C f, 0 < r → Metric.closedBall xStar r ⊆ C →
    (∀ x ∈ C, f x - f xStar ≤ c ^ 2 * ‖fderiv ℝ f x‖ ^ 2) →
    ∀ x₀ ∈ C, ∀ t : ℕ,
      f (fwIterates lmo (fderiv ℝ f) (shortStep lmo (fderiv ℝ f) L) x₀ t) - f xStar ≤
        max (1 - r ^ 2 / (2 * L * c ^ 2 * Metric.diam C ^ 2)) 0 ^ t *
          (L * Metric.diam C ^ 2 / 2) ∧
      f (fwIterates lmo (fderiv ℝ f) (fun _ => σ) x₀ t) - f xStar ≤
        max (1 - r ^ 2 / (2 * L * c ^ 2 * Metric.diam C ^ 2)) 0 ^ t *
          (L * Metric.diam C ^ 2 / 2)

/-- **Lemma 2.22** (linear contraction). If `h_t ≥ 0`, `0 < c₁ < 1`, `h₁ ≤ c₀` and
`h_t - h_{t+1} ≥ c₁ h_t` for `t ≥ 1`, then `h_t ≤ c₀ (1 - c₁)^{t-1}` for `t ≥ 1`. -/
def ContractionLinear : Prop :=
  ∀ (h : ℕ → ℝ) (c₀ c₁ : ℝ), (∀ t, 0 ≤ h t) → 0 < c₁ → c₁ < 1 → h 1 ≤ c₀ →
    (∀ t, 1 ≤ t → h t * c₁ ≤ h t - h (t + 1)) →
    ∀ t, 1 ≤ t → h t ≤ c₀ * (1 - c₁) ^ (t - 1)

/-- **Lemma 2.23** (power contraction). If `h_t > 0`, `c₀, c₂, α > 0`, `h₁ ≤ c₀` and
`h_t - h_{t+1} ≥ c₂ h_t^{1+α}` for `t ≥ 1`, then
`h_t ≤ c₀ / (1 + c₂ c₀^α α (t - 1))^{1/α}` for `t ≥ 1`. -/
def ContractionPower : Prop :=
  ∀ (h : ℕ → ℝ) (c₀ c₂ α : ℝ), (∀ t, 0 < h t) → 0 < c₀ → 0 < c₂ → 0 < α → h 1 ≤ c₀ →
    (∀ t, 1 ≤ t → c₂ * h t ^ (1 + α) ≤ h t - h (t + 1)) →
    ∀ t : ℕ, 1 ≤ t → h t ≤ c₀ / (1 + c₂ * c₀ ^ α * α * ((t : ℝ) - 1)) ^ (1 / α)

end Lemmata.CGBasics
