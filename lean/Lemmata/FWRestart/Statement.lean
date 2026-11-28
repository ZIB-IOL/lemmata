module

public import Lemmata.FWUniformlyConvex.Statement
public import Lemmata.AwayStepFW.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe Lemmata.CGBasics Lemmata.AwayStepFW

universe u

/-- **Lemma 2.3** (the strong Wolfe gap). Let `S ⊆ V` be finite, `x = ∑_{y ∈ S} λ_y y` a convex
combination with positive weights (a proper support of `x`), `f` convex over `conv V` and
differentiable at its points, `a ∈ S` a maximizer of `f'(x)` over `S` and `v ∈ V` a minimizer of
`f'(x)` over `V`, so that `w(x, S) = f'(x)(a - v)` is the strong Wolfe gap. Then
`f(x) - f(x⋆) ≤ w(x, S)` for every minimizer `x⋆` over `conv V`, and `w(x, S) = 0` if and only if
`x` minimizes `f` over `conv V`. -/
def StrongWolfeGap : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V S : Finset E) (f : E → ℝ)
    (lam : E → ℝ) (x a v : E), S ⊆ V → (∀ y ∈ S, 0 < lam y) → ∑ y ∈ S, lam y = 1 →
    x = ∑ y ∈ S, lam y • y → ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    a ∈ S → (∀ y ∈ S, fderiv ℝ f x y ≤ fderiv ℝ f x a) →
    v ∈ V → (∀ y ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
    (∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, f x - f xStar ≤ fderiv ℝ f x (a - v)) ∧
    (fderiv ℝ f x (a - v) = 0 ↔ x ∈ minimizers (convexHull ℝ (↑V : Set E)) f)

/-- **Lemma 3.6** (Hölderian error bounds give a strong Wolfe primal bound). Let `f` be convex over
`conv V`, differentiable at its points, with a `(θ, c)`-Hölderian error bound,
`dist(x, X⋆) ≤ c (f(x) - f⋆)^θ` with `c > 0` and `θ ∈ [0, 1/2]`, and let `δ > 0` have the scaling
property of `conv V` (for instance the pyramidal width). For `x ∈ conv S` with `S ⊆ V`, an away
vertex `a ∈ S` and a Frank–Wolfe vertex `v ∈ V`,
`f(x) - f⋆ ≤ (c/δ)^{1/(1-θ)} f'(x)(a - v)^{1/(1-θ)}`: the `1/(1-θ)`-strong Wolfe primal bound. -/
def HEBStrongWolfeBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V S : Finset E) (f : E → ℝ)
    (c θ δ : ℝ) (x a v xStar : E), ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f c θ → 0 < c → θ ∈ Set.Icc (0 : ℝ) (1 / 2) →
    0 < δ → IsScaling V δ → xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f → S ⊆ V →
    x ∈ convexHull ℝ (↑S : Set E) → a ∈ S → (∀ y ∈ S, fderiv ℝ f x y ≤ fderiv ℝ f x a) →
    v ∈ V → (∀ y ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
      f x - f xStar ≤ (c / δ) ^ (1 / (1 - θ)) * fderiv ℝ f x (a - v) ^ (1 / (1 - θ))

/-- **Theorem 7.3** (vanilla Frank–Wolfe over strongly convex sets). Let `C` be compact, convex and
`α`-strongly convex (`(α, 2)`-uniformly convex) with diameter `D > 0`, and `f` convex and `L`-smooth
with a `(θ, c)`-Hölderian error bound on `C`, `c > 0`, `θ ∈ (0, 1/2]`. With `K = (Lc/α)^{1/(1-θ)}`
and `t₀ = max {⌊log_{1/2} (2K/(L D²))⌋ + 2, 1}`, every short-step run satisfies
`f(x_t) - f⋆ ≤ (L D²/2) 2^{1-t}` for `1 ≤ t < t₀` and
`f(x_t) - f⋆ ≤ K/(1 + (1 - θ)(t - t₀)/2)^{1/(1-θ)}` for `t ≥ t₀`: the rate `O(t^{-1/(1-θ)})`. -/
def StronglyConvexSetRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (α c θ : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α 2 → 0 < α → 0 < (L : ℝ) →
    0 < Metric.diam C → ConvexOn ℝ Set.univ f → IsSmooth f L → IsHolderErrorBound C f c θ →
    0 < c → θ ∈ Set.Ioc (0 : ℝ) (1 / 2) → IsShortStepRun C f L x v γ →
    ∀ xStar ∈ minimizers C f,
      let K := ((L : ℝ) * (c / α)) ^ (1 / (1 - θ))
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) (2 * K / (L * Metric.diam C ^ 2))⌋ + 2) 1
      ∀ t : ℕ, 1 ≤ t →
        ((t : ℤ) < t₀ → f (x t) - f xStar ≤ L * Metric.diam C ^ 2 / 2 * (1 / 2) ^ (t - 1)) ∧
        (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
          K / (1 + (1 - θ) / 2 * ((t : ℝ) - t₀)) ^ (1 / (1 - θ)))

end Lemmata.FWRestart
