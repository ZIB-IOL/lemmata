module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe

universe u

/-- The open-loop step size `η_t = ℓ/(t + ℓ)`, for every integer `t`; the paper also evaluates it at
negative indices, such as `η_{-1} = ℓ/(ℓ - 1)`. -/
noncomputable def eta (ℓ : ℝ) (t : ℤ) : ℝ := ℓ / ((t : ℝ) + ℓ)

/-- **Proposition 3.1** (convergence rate of order `O(1/t)`). Let `C` be compact, `f` convex over
`C`, differentiable at the points of `C` and `L`-smooth over `C`, and `x⋆` a minimizer. Every
Frank–Wolfe run with the open-loop step sizes `η_t = 4/(t + 4)` satisfies
`f(x_t) - f(x⋆) ≤ 8 L δ²/(t + 3)` for all `t ≥ 1`, where `δ` is the diameter of `C`. -/
def BaselineRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : ℝ)
    (x v : ℕ → E), IsCompact C → ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) →
    IsSmoothOn C f L → 0 ≤ L → IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t) →
    ∀ xStar ∈ minimizers C f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤ 8 * L * Metric.diam C ^ 2 / (t + 3)

/-- **Lemma 3.2** (Guélat–Marcotte scaling, corrected). Let `C` be compact, `f` convex over `C`
and differentiable at the points of `C`, `x⋆` a minimizer, and `β > 0` such that every point of
the affine hull of `C` within distance `β` of `x⋆` lies in `C`. For every `x ∈ C`, every atom `p`
minimizing `f'(x)` over `C` and every direction `u` of the affine hull with `‖u‖ ≤ 1`,
`β ‖x - p‖ f'(x)(u) ≤ δ f'(x)(x - p)`, where `δ` is the diameter of `C`. The paper tests the
derivative against every unit vector; that version fails when `C` is not full-dimensional. -/
def GuelatMarcotteScaling : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (β : ℝ)
    (xStar : E), IsCompact C → ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) →
    xStar ∈ minimizers C f → 0 < β → (∀ y ∈ affineSpan ℝ C, ‖y - xStar‖ ≤ β → y ∈ C) →
    ∀ x ∈ C, ∀ p ∈ C, (∀ y ∈ C, fderiv ℝ f x p ≤ fderiv ℝ f x y) →
    ∀ u ∈ vectorSpan ℝ C, ‖u‖ ≤ 1 →
      β * ‖x - p‖ * fderiv ℝ f x u ≤ Metric.diam C * fderiv ℝ f x (x - p)

/-- **Lemma 3.3** (the iterates approach the minimizers). Under the assumptions of Proposition 3.1,
with `L > 0`, `δ > 0` and a `(μ, θ)`-Hölderian error bound with `μ, θ > 0`, every Frank–Wolfe run
with `η_t = 4/(t + 4)` is within distance `β > 0` of the minimizers for all
`t ≥ ⌈8 L δ² (μ/β)^{1/θ}⌉`. -/
def IteratesNearOptimum : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (L μ θ β : ℝ) (x v : ℕ → E), IsCompact C → ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → IsSmoothOn C f L → 0 < L → 0 < Metric.diam C →
    IsHolderErrorBound C f μ θ → 0 < μ → 0 < θ → 0 < β →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t) →
    ∀ t : ℕ, ⌈8 * L * Metric.diam C ^ 2 * (μ / β) ^ (1 / θ)⌉₊ ≤ t →
      Metric.infDist (x t) (minimizers C f) ≤ β

/-- **Lemma 3.4** (scaling from a Hölderian error bound). Let `C` be compact, `f` convex over `C`,
differentiable at the points of `C`, with unique minimizer `x⋆` and a `(μ, θ)`-Hölderian error
bound with `μ > 0`. For `x ∈ C` with `x ≠ x⋆`,
`(f(x) - f(x⋆))^{1-θ}/μ ≤ f'(x)(x - x⋆)/‖x - x⋆‖ ≤ ‖f'(x)‖`. -/
def ScalingHEB : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (μ θ : ℝ)
    (xStar : E), IsCompact C → ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) →
    IsHolderErrorBound C f μ θ → 0 < μ → minimizers C f = {xStar} →
    ∀ x ∈ C, x ≠ xStar →
      (f x - f xStar) ^ (1 - θ) / μ ≤ fderiv ℝ f x (x - xStar) / ‖x - xStar‖ ∧
      fderiv ℝ f x (x - xStar) / ‖x - xStar‖ ≤ ‖fderiv ℝ f x‖

/-- **Lemma 3.5** (the sequence lemma). Let `ψ ∈ [0, 1/2]`, `S ≥ 1`, `A, B, C > 0`, `0 ≤ C_t ≤ C`
and `h_t ≥ 0` with
`h_{t+1} ≤ (1 - η_t/2) h_t - η_t A C_t h_t^{1-ψ} + η_t² B C_t` for `S ≤ t < T`, where
`η_t = 4/(t + 4)`. Then for `S ≤ t ≤ T`,
`h_t ≤ max {(η_{t-2}/η_{S-1})^{1/(1-ψ)} h_S, (η_{t-2} B/A)^{1/(1-ψ)} + η_{t-2}² B C}`. -/
def SequenceLemma : Prop :=
  ∀ (ψ A B C : ℝ) (S T : ℕ) (Cs h : ℕ → ℝ), ψ ∈ Set.Icc (0 : ℝ) (1 / 2) → 1 ≤ S → 0 < A →
    0 < B → 0 < C → (∀ t, S ≤ t → t < T → 0 ≤ Cs t ∧ Cs t ≤ C) →
    (∀ t, S ≤ t → t ≤ T → 0 ≤ h t) →
    (∀ t, S ≤ t → t < T → h (t + 1) ≤ (1 - eta 4 t / 2) * h t -
      eta 4 t * A * Cs t * h t ^ (1 - ψ) + eta 4 t ^ 2 * B * Cs t) →
    ∀ t, S ≤ t → t ≤ T →
      h t ≤ max ((eta 4 ((t : ℤ) - 2) / eta 4 ((S : ℤ) - 1)) ^ (1 / (1 - ψ)) * h S)
        ((eta 4 ((t : ℤ) - 2) * B / A) ^ (1 / (1 - ψ)) + eta 4 ((t : ℤ) - 2) ^ 2 * B * C)

/-- **Theorem 3.6** (minimizers in the relative interior). Let `C` be compact with diameter
`δ > 0`, `f` convex over `C`, differentiable at the points of `C`, `L`-smooth over `C` with
`L > 0`, with a `(μ, θ)`-Hölderian error bound, `μ > 0` and `θ ∈ [0, 1/2]`, and let `β > 0` be
such that every point of the affine hull of `C` within distance `β` of a minimizer lies in `C`.
Every Frank–Wolfe run with `η_t = 4/(t + 4)` satisfies, for every `S ≥ 1` and `t ≥ S`,
`h_t ≤ max {(η_{t-2}/η_{S-1})^{1/(1-θ)} h_S, (η_{t-2} 2μLδ³/β²)^{1/(1-θ)} + η_{t-2}² Lδ²/2}`. -/
def InteriorRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (L μ θ β : ℝ) (x v : ℕ → E) (xStar : E), IsCompact C → ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → IsSmoothOn C f L → 0 < L → 0 < Metric.diam C →
    IsHolderErrorBound C f μ θ → 0 < μ → θ ∈ Set.Icc (0 : ℝ) (1 / 2) →
    xStar ∈ minimizers C f → 0 < β →
    (∀ y ∈ minimizers C f, ∀ z ∈ affineSpan ℝ C, ‖z - y‖ ≤ β → z ∈ C) →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t) →
    ∀ S : ℕ, 1 ≤ S → ∀ t : ℕ, S ≤ t →
      f (x t) - f xStar ≤
        max ((eta 4 ((t : ℤ) - 2) / eta 4 ((S : ℤ) - 1)) ^ (1 / (1 - θ)) * (f (x S) - f xStar))
          ((eta 4 ((t : ℤ) - 2) * (2 * μ * L * Metric.diam C ^ 3 / β ^ 2)) ^ (1 / (1 - θ)) +
            eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2))

/-- **Lemma 3.9** (scaling for uniformly convex sets). Let `C` be `(α, q)`-uniformly convex with
`α > 0` and `q ≥ 2`, `f` convex over `C` and differentiable at the points of `C`, and `x⋆` a
minimizer. For `x ∈ C` and an atom `p` minimizing `f'(x)` over `C`,
`(α/2 ‖f'(x)‖)^{2/q} (f(x) - f(x⋆))^{1-2/q} ‖x - p‖² ≤ f'(x)(x - p)`. -/
def ScalingUnif : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (α q : ℝ)
    (xStar : E), IsUniformlyConvexSet C α q → 0 < α → 2 ≤ q → ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f →
    ∀ x ∈ C, ∀ p ∈ C, (∀ y ∈ C, fderiv ℝ f x p ≤ fderiv ℝ f x y) →
      (α / 2 * ‖fderiv ℝ f x‖) ^ (2 / q) * (f x - f xStar) ^ (1 - 2 / q) * ‖x - p‖ ^ 2 ≤
        fderiv ℝ f x (x - p)

/-- **Theorem 3.10** (gradients bounded away from zero). Let `C` be compact and
`(α, q)`-uniformly convex with diameter `δ > 0`, `α > 0` and `q ≥ 2`, and `f` convex over `C`,
differentiable at the points of `C`, `L`-smooth over `C` with `L > 0`, with `‖f'(y)‖ ≥ λ > 0` on
`C` (`λ` is `ν` here), and `x⋆` a minimizer. Every Frank–Wolfe run with `η_t = 4/(t + 4)`
satisfies, for `q ≥ 4` and `t ≥ 1`,
`h_t ≤ max {η_{t-2}^{1/(1-2/q)} Lδ²/2, (η_{t-2} L (2/(αλ))^{2/q})^{1/(1-2/q)} + η_{t-2}² Lδ²/2}`,
and, for `q < 4` and `t ≥ S = ⌈8Lδ²⌉`,
`h_t ≤ max {(η_{t-2}/η_{S-1})² h_S, (η_{t-2} L (2/(αλ))^{2/q})² + η_{t-2}² Lδ²/2}`. -/
def ExteriorRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (L α q ν : ℝ) (x v : ℕ → E) (xStar : E), IsCompact C → IsUniformlyConvexSet C α q →
    0 < α → 2 ≤ q → ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) → IsSmoothOn C f L →
    0 < L → 0 < Metric.diam C → 0 < ν → (∀ y ∈ C, ν ≤ ‖fderiv ℝ f y‖) →
    xStar ∈ minimizers C f → IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t) →
    (4 ≤ q → ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      max (eta 4 ((t : ℤ) - 2) ^ (1 / (1 - 2 / q)) * (L * Metric.diam C ^ 2 / 2))
        ((eta 4 ((t : ℤ) - 2) * L * (2 / (α * ν)) ^ (2 / q)) ^ (1 / (1 - 2 / q)) +
          eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2))) ∧
    (q < 4 → ∀ t : ℕ, ⌈8 * L * Metric.diam C ^ 2⌉₊ ≤ t → f (x t) - f xStar ≤
      max ((eta 4 ((t : ℤ) - 2) / eta 4 ((⌈8 * L * Metric.diam C ^ 2⌉₊ : ℤ) - 1)) ^ 2 *
          (f (x ⌈8 * L * Metric.diam C ^ 2⌉₊) - f xStar))
        ((eta 4 ((t : ℤ) - 2) * L * (2 / (α * ν)) ^ (2 / q)) ^ 2 +
          eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2)))

/-- **Theorem 3.12** (no assumption on the location of the minimizer). Let `C` be compact and
`(α, q)`-uniformly convex with diameter `δ > 0`, `α > 0` and `q ≥ 2`, and `f` convex over `C`,
differentiable at the points of `C`, `L`-smooth over `C` with `L > 0`, with a
`(μ, θ)`-Hölderian error bound, `μ > 0` and `θ ∈ [0, 1/2]`, and `x⋆` a minimizer. Every
Frank–Wolfe run with `η_t = 4/(t + 4)` satisfies, for `t ≥ 1`,
`h_t ≤ max {η_{t-2}^{1/(1-2θ/q)} Lδ²/2, (η_{t-2} L (2μ/α)^{2/q})^{1/(1-2θ/q)} + η_{t-2}² Lδ²/2}`. -/
def UnrestrictedRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (L α q μ θ : ℝ) (x v : ℕ → E) (xStar : E), IsCompact C → IsUniformlyConvexSet C α q →
    0 < α → 2 ≤ q → ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) → IsSmoothOn C f L →
    0 < L → 0 < Metric.diam C → IsHolderErrorBound C f μ θ → 0 < μ →
    θ ∈ Set.Icc (0 : ℝ) (1 / 2) → xStar ∈ minimizers C f →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta 4 t) →
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      max (eta 4 ((t : ℤ) - 2) ^ (1 / (1 - 2 * θ / q)) * (L * Metric.diam C ^ 2 / 2))
        ((eta 4 ((t : ℤ) - 2) * L * (2 * μ / α) ^ (2 / q)) ^ (1 / (1 - 2 * θ / q)) +
          eta 4 ((t : ℤ) - 2) ^ 2 * (L * Metric.diam C ^ 2 / 2))

end Lemmata.FWOpenLoop
