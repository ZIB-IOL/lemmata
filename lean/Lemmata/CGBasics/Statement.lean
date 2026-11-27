module

public import Lemmata.FrankWolfe.Statement
public import Lemmata.FrankWolfeIntro.Statement
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Base

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

/-- **Lemma 2.21** (from contractions to convergence rates). Let `h_t > 0`, `c₀, c₂, α > 0`,
`0 < c₁ < 1`, `h₁ ≤ c₀` and `h_t - h_{t+1} ≥ h_t min {c₁, c₂ h_t^α}` for `t ≥ 1`. With
`τ = (c₁/c₂)^{1/α}` and `t₀ = max {⌊log_{1-c₁}(τ/c₀)⌋ + 2, 1}`, `h_t ≤ c₀ (1 - c₁)^{t-1}` for
`1 ≤ t < t₀`, and `h_t ≤ τ / (1 + c₁ α (t - t₀))^{1/α}` for `t ≥ t₀`. The book states the first
bound also at `t = t₀`, where it can fail. -/
def ContractionMixed : Prop :=
  ∀ (h : ℕ → ℝ) (c₀ c₁ c₂ α : ℝ), (∀ t, 0 < h t) → 0 < c₀ → 0 < c₁ → c₁ < 1 → 0 < c₂ → 0 < α →
    h 1 ≤ c₀ → (∀ t, 1 ≤ t → h t * min c₁ (c₂ * h t ^ α) ≤ h t - h (t + 1)) →
    (∀ t : ℕ, 1 ≤ t →
      (t : ℤ) < max (⌊Real.logb (1 - c₁) ((c₁ / c₂) ^ (1 / α) / c₀)⌋ + 2) 1 →
        h t ≤ c₀ * (1 - c₁) ^ (t - 1)) ∧
    (∀ t : ℕ, max (⌊Real.logb (1 - c₁) ((c₁ / c₂) ^ (1 / α) / c₀)⌋ + 2) 1 ≤ (t : ℤ) →
      h t ≤ (c₁ / c₂) ^ (1 / α) / (1 + c₁ * α * ((t : ℝ) -
        (max (⌊Real.logb (1 - c₁) ((c₁ / c₂) ^ (1 / α) / c₀)⌋ + 2) 1 : ℤ))) ^ (1 / α))

/-- **Theorem 2.6** (approximate linear minimization). Let `C` be compact and convex with diameter
`D`, `f` convex and `L`-smooth, and `δ ≥ 0`. Take a Frank–Wolfe run in which `v_t ∈ C` minimizes
`f'(x_t)` over `C` up to the additive error `L D² δ / (t + 3)`, and every step `γ_t ∈ [0, 1]` does
at least as well as every `s ∈ [0, 1]` in the smoothness bound (short steps clipped to `[0, 1]` and
exact line search qualify). Then `f(x_t) - f(x⋆) ≤ 2 L D² (1 + δ) / (t + 3)` for `t ≥ 1`. -/
def ApproximateOracleRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (δ : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → IsSmooth f L → 0 ≤ δ → x 0 ∈ C →
    (∀ t : ℕ, v t ∈ C ∧
      (∀ y ∈ C, fderiv ℝ f (x t) (v t) ≤
        fderiv ℝ f (x t) y + L * Metric.diam C ^ 2 * δ / ((t : ℝ) + 3)) ∧
      γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤
        f (x t) - s * fderiv ℝ f (x t) (x t - v t) + s ^ 2 * L / 2 * ‖v t - x t‖ ^ 2) →
    ∀ xStar ∈ minimizers C f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤ 2 * L * Metric.diam C ^ 2 * (1 + δ) / ((t : ℝ) + 3)

/-- **Theorem 2.2** (vanilla Frank–Wolfe). Let `C` be compact and convex with diameter `D` and `f`
convex and `L`-smooth. If every `v_t` is a Frank–Wolfe vertex and every step does at least as well
as each `s ∈ [0, 1]` in the smoothness bound, as the short step and line search do, then for `t ≥ 1`
the primal gap is at most `2 L D²/(t + 3)` and some Frank–Wolfe gap `g_τ = f'(x_τ)(x_τ - v_τ)` with
`τ ≤ t` is at most `4 L D²/(t + 3)`. -/
def VanillaRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → IsSmooth f L → x 0 ∈ C →
    (∀ t : ℕ, v t ∈ C ∧ (∀ y ∈ C, fderiv ℝ f (x t) (v t) ≤ fderiv ℝ f (x t) y) ∧
      γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤
        f (x t) - s * fderiv ℝ f (x t) (x t - v t) + s ^ 2 * L / 2 * ‖v t - x t‖ ^ 2) →
    ∀ xStar ∈ minimizers C f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤ 2 * L * Metric.diam C ^ 2 / ((t : ℝ) + 3) ∧
        ∃ τ ≤ t, fderiv ℝ f (x τ) (x τ - v τ) ≤ 4 * L * Metric.diam C ^ 2 / ((t : ℝ) + 3)

/-- **Theorem 2.11** (nonconvex objectives). For `L`-smooth, not necessarily convex `f` and steps as
in Theorem 2.2, some Frank–Wolfe gap `g_τ` with `τ ≤ t` is at most `max {2 h₀, L D²}/√(t + 1)`,
where `h₀ = f(x₀) - f(x⋆)`. -/
def NonconvexShortStepRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsSmooth f L → x 0 ∈ C →
    (∀ t : ℕ, v t ∈ C ∧ (∀ y ∈ C, fderiv ℝ f (x t) (v t) ≤ fderiv ℝ f (x t) y) ∧
      γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤
        f (x t) - s * fderiv ℝ f (x t) (x t - v t) + s ^ 2 * L / 2 * ‖v t - x t‖ ^ 2) →
    ∀ xStar ∈ minimizers C f, ∀ t : ℕ, ∃ τ ≤ t,
      fderiv ℝ f (x τ) (x τ - v τ) ≤
        max (2 * (f (x 0) - f xStar)) (L * Metric.diam C ^ 2) / Real.sqrt ((t : ℝ) + 1)

/-- **Proposition 2.9** (a lower bound for any step sizes), the value bound:
`f(x_t) - f(x⋆) ≥ ∏_{τ=1}^{t-1} (1 - γ_τ) · f'(x⋆)(x₁ - x⋆)` for `t ≥ 1`. This is Proposition 4.6 of
the introduction `Lemmata.FrankWolfeIntro`. -/
abbrev FixedStepLowerBound : Prop := Lemmata.FrankWolfeIntro.FixedLowerBound.{u}

/-- **Proposition 2.9** for the open-loop rule `γ_t = 2/(t+2)`:
`f(x_t) - f(x⋆) ≥ 2/(t(t+1)) · f'(x⋆)(x₁ - x⋆)` for `t ≥ 1`. -/
abbrev FixedStepLowerBoundOpenLoop : Prop := Lemmata.FrankWolfeIntro.FixedLowerBoundOpenLoop.{u}

/-- **Proposition 2.9**, the decomposition: for step sizes in `[0, 1]` and atoms in `C`, every
iterate `x_T` with `T ≥ 1` equals `P x₁ + (1 - P) y_T` for `P = ∏_{t=1}^{T-1} (1 - γ_t)` and some
`y_T ∈ C`. -/
def FixedStepDecomposition : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (x v : ℕ → E) (γ : ℕ → ℝ),
    Convex ℝ C → x 0 ∈ C →
    (∀ t : ℕ, v t ∈ C ∧ γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t)) →
    ∀ T : ℕ, 1 ≤ T → ∃ y ∈ C,
      x T = (∏ t ∈ Finset.Ico 1 T, (1 - γ t)) • x 1 + (1 - ∏ t ∈ Finset.Ico 1 T, (1 - γ t)) • y

/-- **Definition 2.12** (gradient domination). `f` is `c`-gradient dominated on `C` if
`(f(x) - f(y))/c² ≤ ‖f'(x)‖²` for all `x, y ∈ C`. -/
def IsGradientDominated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (f : E → ℝ) (c : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, (f x - f y) / c ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2

/-- A Frank–Wolfe run on `C` with exact linear minimization in which every step does at least as
well as each `s ∈ [0, 1]` in the smoothness bound, as short steps and line search do. -/
def IsShortStepRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (L : NNReal) (x v : ℕ → E) (γ : ℕ → ℝ) : Prop :=
  x 0 ∈ C ∧ ∀ t : ℕ, v t ∈ C ∧ (∀ y ∈ C, fderiv ℝ f (x t) (v t) ≤ fderiv ℝ f (x t) y) ∧
    γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t) ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤
      f (x t) - s * fderiv ℝ f (x t) (x t - v t) + s ^ 2 * L / 2 * ‖v t - x t‖ ^ 2

/-- **Proposition 2.19** (scaling condition for uniformly convex sets). If `C` is
`(α, q)`-uniformly convex and `v ∈ C` minimizes `ψ` over `C`, then `α ‖ψ‖ ‖x - v‖^q ≤ ψ(x - v)`
for every `x ∈ C`. -/
def UniformlyConvexScaling : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (α q : ℝ),
    IsUniformlyConvexSet C α q → ∀ (ψ : StrongDual ℝ E) (v : E), v ∈ C → (∀ y ∈ C, ψ v ≤ ψ y) →
    ∀ x ∈ C, α * ‖ψ‖ * ‖x - v‖ ^ q ≤ ψ (x - v)

/-- **Theorem 2.20** for `q = 2` (strongly convex sets). If `C` is compact, convex and
`(α, 2)`-uniformly convex, `f` is convex and `L`-smooth with `‖f'(y)‖ ≥ c > 0` on `C`, then every
short-step run satisfies `f(x_t) - f(x⋆) ≤ max {1/2, 1 - α c/(2 L)}^{t-1} L D²/2` for `t ≥ 1`. -/
def UniformlyConvexLinear : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (α c : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α 2 → 0 < α → 0 < c → 0 < (L : ℝ) →
    ConvexOn ℝ Set.univ f → IsSmooth f L → (∀ y ∈ C, c ≤ ‖fderiv ℝ f y‖) →
    IsShortStepRun C f L x v γ → ∀ xStar ∈ minimizers C f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        max (1 / 2) (1 - α * c / (2 * L)) ^ (t - 1) * (L * Metric.diam C ^ 2 / 2)

/-- **Theorem 2.20** for `q > 2`. Under the assumptions of `UniformlyConvexLinear` with an
`(α, q)`-uniformly convex set, let `K = (L/(α c))^{2/(q-2)}` and
`t₀ = max {⌊log₂ (D²/K)⌋ + 1, 1}`. Then `f(x_t) - f(x⋆) ≤ L D²/2^t` for `1 ≤ t < t₀` and
`f(x_t) - f(x⋆) ≤ L K/(1 + (1/2 - 1/q)(t - t₀))^{q/(q-2)}` for `t ≥ t₀`. -/
def UniformlyConvexPower : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (α c q : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α q → 2 < q → 0 < α → 0 < c → 0 < (L : ℝ) →
    ConvexOn ℝ Set.univ f → IsSmooth f L → (∀ y ∈ C, c ≤ ‖fderiv ℝ f y‖) →
    IsShortStepRun C f L x v γ → ∀ xStar ∈ minimizers C f,
      let K := ((L : ℝ) / (α * c)) ^ (2 / (q - 2))
      let t₀ : ℤ := max (⌊Real.logb 2 (Metric.diam C ^ 2 / K)⌋ + 1) 1
      (∀ t : ℕ, 1 ≤ t → (t : ℤ) < t₀ → f (x t) - f xStar ≤ L * Metric.diam C ^ 2 / 2 ^ t) ∧
      (∀ t : ℕ, t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
        L * K / (1 + (1 / 2 - 1 / q) * ((t : ℝ) - t₀)) ^ (q / (q - 2)))

/-- **Theorem 2.24** (gradient-dominated objectives), with scale-invariant constants. If `C` is
compact, convex and `(α, q)`-uniformly convex with `q ≥ 2`, and `f` is convex, `L`-smooth and
`c`-gradient dominated on `C`, let `K = (L c²/α²)^{1/(q-1)}` and `t₀ = max {⌊log₂ (D²/K)⌋ + 1, 1}`.
Then every short-step run satisfies `f(x_t) - f(x⋆) ≤ L D²/2^t` for `1 ≤ t < t₀` and
`f(x_t) - f(x⋆) ≤ L K/(1 + (1/2)(1 - 1/q)(t - t₀))^{q/(q-1)}` for `t ≥ t₀`. -/
def GradientDominatedRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (α c q : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α q → 2 ≤ q → 0 < α → 0 < c → 0 < (L : ℝ) →
    ConvexOn ℝ Set.univ f → IsSmooth f L → IsGradientDominated C f c →
    IsShortStepRun C f L x v γ → ∀ xStar ∈ minimizers C f,
      let K := ((L : ℝ) * c ^ 2 / α ^ 2) ^ (1 / (q - 1))
      let t₀ : ℤ := max (⌊Real.logb 2 (Metric.diam C ^ 2 / K)⌋ + 1) 1
      (∀ t : ℕ, 1 ≤ t → (t : ℤ) < t₀ → f (x t) - f xStar ≤ L * Metric.diam C ^ 2 / 2 ^ t) ∧
      (∀ t : ℕ, t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
        L * K / (1 + 1 / 2 * (1 - 1 / q) * ((t : ℝ) - t₀)) ^ (q / (q - 1)))

/-- **Example 2.7** (a primal gap lower bound). Minimize `‖x‖²` over the probability simplex in
`ℝⁿ` with the Euclidean norm. Every convex combination `x` of the coordinate vectors `e_i` with
`i ∈ S` has primal gap at least `1/|S| - 1/n`, so an algorithm that has seen at most `k` vertices
has primal gap at least `1/k - 1/n`. -/
def SimplexLowerBound : Prop :=
  ∀ (n : ℕ) (S : Finset (Fin n)), S.Nonempty →
    ∀ xStar ∈ minimizers
        (convexHull ℝ (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)))
        (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2),
    ∀ x ∈ convexHull ℝ ((fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) '' (S : Set (Fin n))),
      1 / (S.card : ℝ) - 1 / n ≤ ‖x‖ ^ 2 - ‖xStar‖ ^ 2

/-- **Lemma 2.10** (square sums with fast tails). Let `γ_i ≥ 0` with `∑ γ_i²` convergent, and let
`δ > 0` and `t₀` be such that `∑_{i ≥ t} γ_i² ≤ C/(t log^{2+δ} t)` for `t ≥ t₀`. Then `∑ γ_i`
converges. -/
def SquareTailSummable : Prop :=
  ∀ (γ : ℕ → ℝ) (C δ : ℝ) (t₀ : ℕ), (∀ i, 0 ≤ γ i) → 0 < δ → Summable (fun i => γ i ^ 2) →
    (∀ t : ℕ, t₀ ≤ t → ∑' i, γ (t + i) ^ 2 ≤ C / (t * Real.log t ^ (2 + δ))) →
    Summable γ

/-- **Theorem 2.8** (Frank–Wolfe is slow when the minimizers lie on a face). Let `P = conv V` for a
finite `V`, let `F` be an exposed face of `P` containing all minimizers of a convex `L`-smooth `f`
over `P`, and take a Frank–Wolfe run with vertices `v_t ∈ V` whose steps satisfy
`γ_t ≤ ν g_t/‖x_t - v_t‖²` and `f(x_t) - f(x_{t+1}) ≥ g_t²/(2 L ‖x_t - v_t‖²)`, where
`g_t = f'(x_t)(x_t - v_t)`. If some iterate `x_{t₀}` lies outside `F` with `f(x_{t₀}) < f(w)` for
every vertex `w` of `F`, then for every `δ > 0`, `f(x_t) - f(x⋆) ≥ L D²/(t log^{2+δ} t)` for
infinitely many `t`. -/
def WolfeLowerBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (ψ : StrongDual ℝ E)
    (f : E → ℝ) (L : NNReal) (ν : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ) (t₀ : ℕ),
    0 < (L : ℝ) → ConvexOn ℝ Set.univ f → IsSmooth f L →
    minimizers (convexHull ℝ (↑V : Set E)) f ⊆ convexHull ℝ (↑(exposedFace V ψ) : Set E) →
    x 0 ∈ convexHull ℝ (↑V : Set E) →
    (∀ t : ℕ, v t ∈ V ∧ (∀ w ∈ V, fderiv ℝ f (x t) (v t) ≤ fderiv ℝ f (x t) w) ∧
      γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t) ∧
      γ t ≤ ν * fderiv ℝ f (x t) (x t - v t) / ‖x t - v t‖ ^ 2 ∧
      fderiv ℝ f (x t) (x t - v t) ^ 2 / (2 * L * ‖x t - v t‖ ^ 2) ≤ f (x t) - f (x (t + 1))) →
    x t₀ ∉ convexHull ℝ (↑(exposedFace V ψ) : Set E) → (∀ w ∈ exposedFace V ψ, f (x t₀) < f w) →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ δ : ℝ, 0 < δ →
      ∃ᶠ t : ℕ in Filter.atTop,
        L * Metric.diam (↑V : Set E) ^ 2 / ((t : ℝ) * Real.log t ^ (2 + δ)) ≤ f (x t) - f xStar

end Lemmata.CGBasics
