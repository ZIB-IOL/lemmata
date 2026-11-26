module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Lemmata.AwayStepFW.Defs

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

universe u

/-- **Lemma 2.26** (scaling inequality via pyramidal width). For every finite `V`, the pyramidal
width `δ` of `conv V` has the scaling property: for `S ⊆ V`, `x ∈ conv S`, `y ∈ conv V`, every
direction `ψ`, an away vertex `a` and a Frank–Wolfe vertex `v`, `δ ψ(x - y) ≤ ψ(a - v) ‖x - y‖`. -/
def ScalingViaPyramidalWidth : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E),
    IsScaling V (pyramidalWidth V)

/-- **Lemma 2.27** (geometric strong convexity). Let `conv V` have the scaling property with
constant `δ > 0`, let `f` be `μ`-strongly convex on `conv V` with `μ > 0`, and let `x⋆` minimize `f`
on `conv V`. For `S ⊆ V`, `x ∈ conv S`, an away vertex `a ∈ S` and a Frank–Wolfe vertex `v ∈ V` for
`f'(x)`, `f x - f x⋆ ≤ f'(x)(a - v)² / (2 μ δ²)`. -/
def GeometricStrongConvexity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (μ δ : ℝ),
    0 < μ → 0 < δ → IsScaling V δ →
    (∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ S ⊆ V, ∀ x ∈ convexHull ℝ (↑S : Set E),
    ∀ a ∈ S, (∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) →
    ∀ v ∈ V, (∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) →
      f x - f xStar ≤ fderiv ℝ f x (a - v) ^ 2 / (2 * μ * δ ^ 2)

/-- **Theorem 2.29** (linear convergence of away-step Frank–Wolfe). Let `conv V` have the scaling
property with constant `δ > 0` (for instance its pyramidal width), diameter `D`, and let `f` be
convex, `L`-smooth with `L > 0`, and `μ`-strongly convex on `conv V` with `μ > 0`. Every run of
away-step Frank–Wolfe satisfies `f(x_t) - f(x⋆) ≤ (1 - ρ)^⌊(t-1)/2⌋ L D²/2` for `t ≥ 1`, with
`ρ = min {1/2, μ δ² / (4 L D²)}`. -/
def AwayStepConvergence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (μ δ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ),
    0 < (L : ℝ) → 0 < μ → 0 < δ → IsScaling V δ → ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    IsAFWRun V f L x S lam →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (μ * δ ^ 2 / (4 * L * Metric.diam (↑V : Set E) ^ 2))) ^ ((t - 1) / 2) *
          (L * Metric.diam (↑V : Set E) ^ 2 / 2)

/-- **Theorem 2.34** (linear convergence of fully-corrective Frank–Wolfe). Under the assumptions of
`AwayStepConvergence`, every run of fully-corrective Frank–Wolfe satisfies
`f(x_t) - f(x⋆) ≤ (1 - min {1/2, μ δ² / (L D²)})^(t-1) L D²/2` for `t ≥ 1`. -/
def FullyCorrectiveConvergence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (μ δ : ℝ) (x : ℕ → E) (S : ℕ → Finset E),
    0 < (L : ℝ) → 0 < μ → 0 < δ → IsScaling V δ → ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    IsFCFWRun V f x S →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (μ * δ ^ 2 / (L * Metric.diam (↑V : Set E) ^ 2))) ^ (t - 1) *
          (L * Metric.diam (↑V : Set E) ^ 2 / 2)

/-- **Proposition 2.31, lower bound** (facial distance). In a finite-dimensional real normed space,
the facial distance of `conv V` (the smallest distance between a proper exposed face and the convex
hull of the remaining vertices) is a scaling constant; hence the pyramidal width is at least the
facial distance, and Theorems 2.29 and 2.34 hold with `δ` the facial distance when it is positive.
-/
def FacialDistanceScaling : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V : Finset E),
    IsScaling V (facialDistance V)

/-- **Proposition 2.31** (pyramidal width as facial distance). In a finite-dimensional real normed
space, the pyramidal width of `conv V` equals its facial distance. -/
def PyramidalWidthEqFacial : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V : Finset E),
    pyramidalWidth V = facialDistance V

end Lemmata.AwayStepFW
