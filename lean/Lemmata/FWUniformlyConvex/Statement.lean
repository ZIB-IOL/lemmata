module

public import Lemmata.CGBasics.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWUniformlyConvex

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

/-- **Local uniform convexity** at `x⋆` (the hypothesis of Lemma 2.4): for all `x ∈ C`,
`η ∈ [0, 1]` and unit vectors `z`, the point `η x⋆ + (1 - η) x + η (1 - η) α ‖x⋆ - x‖^q z` lies in
`C`. -/
def IsLocallyUniformlyConvexAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (α q : ℝ) (xStar : E) : Prop :=
  ∀ x ∈ C, ∀ η ∈ Set.Icc (0 : ℝ) 1, ∀ z : E, ‖z‖ = 1 →
    η • xStar + (1 - η) • x + (η * (1 - η) * α * ‖xStar - x‖ ^ q) • z ∈ C

/-- The **local scaling inequality** at `x⋆` (equation (8)):
`α/2 ‖f'(x⋆)‖ ‖x⋆ - x‖^q ≤ f'(x⋆)(x - x⋆)` for all `x ∈ C`. -/
def IsLocalScaling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (α q : ℝ) (xStar : E) : Prop :=
  ∀ x ∈ C, α / 2 * ‖fderiv ℝ f xStar‖ * ‖xStar - x‖ ^ q ≤ fderiv ℝ f xStar (x - xStar)

/-- **Lemma 2.4** (local uniform convexity gives the local scaling inequality). If `x⋆ ∈ C`
satisfies the first-order optimality condition `f'(x⋆)(x - x⋆) ≥ 0` for `x ∈ C`, and `C` is locally
`(α, q)`-uniformly convex at `x⋆`, then the local scaling inequality holds at `x⋆`. -/
def LocalScalingOfLocallyUC : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (α q : ℝ)
    (xStar : E), xStar ∈ C → (∀ x ∈ C, 0 ≤ fderiv ℝ f xStar (x - xStar)) →
    IsLocallyUniformlyConvexAt C α q xStar → IsLocalScaling C f α q xStar

/-- **Corollary 2.8** (a uniformly convex superset). If `C ⊆ Γ` for an `(α, q)`-uniformly convex
set `Γ`, and `x⋆ ∈ C` satisfies `f'(x⋆)(y - x⋆) ≥ 0` for all `y ∈ Γ` (that is, `-∇f(x⋆)` lies in
the normal cone of `Γ` at `x⋆`), then the local scaling inequality holds at `x⋆` for `C`. -/
def LocalScalingOfSuperset : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C Γ : Set E) (f : E → ℝ) (α q : ℝ)
    (xStar : E), C ⊆ Γ → IsUniformlyConvexSet Γ α q → xStar ∈ C →
    (∀ y ∈ Γ, 0 ≤ fderiv ℝ f xStar (y - xStar)) → IsLocalScaling C f α q xStar

/-- **Lemma 2.9** (scaling under a Hölderian error bound). Let `C` be `(α, q)`-uniformly convex
with `α > 0`, `f` convex over `C` and differentiable at its points with a minimizer `x⋆` and a
`(μ, θ)`-Hölderian error bound, `μ > 0`, `θ ∈ [0, 1/2]`. For `x ∈ C` and a Frank–Wolfe vertex `v`,
`(α/μ) ‖x - v‖^q (f(x) - f(x⋆))^{1-θ} ≤ f'(x)(x - v)`. -/
def HEBScaling : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (α q μ θ : ℝ) (xStar x v : E), IsUniformlyConvexSet C α q → 0 < α → ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → IsHolderErrorBound C f μ θ → 0 < μ →
    θ ∈ Set.Icc (0 : ℝ) (1 / 2) → xStar ∈ minimizers C f → x ∈ C → v ∈ C →
    (∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
      α / μ * ‖x - v‖ ^ q * (f x - f xStar) ^ (1 - θ) ≤ fderiv ℝ f x (x - v)

/-- **Theorem 2.10** (rates under a Hölderian error bound). Let `C` be compact, convex and
`(α, q)`-uniformly convex with `q ≥ 2` and diameter `D > 0`, and `f` convex and `L`-smooth with a
`(μ, θ)`-Hölderian error bound on `C`, `μ > 0`, `θ ∈ (0, 1/2]`. With `a = 1 - 2θ/q`,
`K = (L (μ/α)^{2/q})^{1/a}` and `t₀ = max {⌊log_{1/2} (2K/(L D²))⌋ + 2, 1}`, every short-step run
satisfies `f(x_t) - f(x⋆) ≤ (L D²/2) 2^{1-t}` for `1 ≤ t < t₀` and
`f(x_t) - f(x⋆) ≤ K/(1 + a (t - t₀)/2)^{1/a}` for `t ≥ t₀`: the rate `O(t^{-1/(1-2θ/q)})`. -/
def HEBRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (α q μ θ : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α q → 2 ≤ q → 0 < α → 0 < (L : ℝ) →
    0 < Metric.diam C → ConvexOn ℝ Set.univ f → IsSmooth f L → IsHolderErrorBound C f μ θ →
    0 < μ → θ ∈ Set.Ioc (0 : ℝ) (1 / 2) → IsShortStepRun C f L x v γ →
    ∀ xStar ∈ minimizers C f,
      let a := 1 - 2 * θ / q
      let K := ((L : ℝ) * (μ / α) ^ (2 / q)) ^ (1 / a)
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) (2 * K / (L * Metric.diam C ^ 2))⌋ + 2) 1
      ∀ t : ℕ, 1 ≤ t →
        ((t : ℤ) < t₀ → f (x t) - f xStar ≤ L * Metric.diam C ^ 2 / 2 * (1 / 2) ^ (t - 1)) ∧
        (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤ K / (1 + a / 2 * ((t : ℝ) - t₀)) ^ (1 / a))

end Lemmata.FWUniformlyConvex
