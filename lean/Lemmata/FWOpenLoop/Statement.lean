module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Lemmata.AwayStepFW.Statement
public import Mathlib.Analysis.InnerProductSpace.Basic

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

/-- **Proposition 5.2** (decomposition-invariant pairwise Frank–Wolfe, rate `O(1/t)`). Let
`C = conv V` be simplex-like with diameter `δ`, `f` convex over `C`, differentiable at the points of
`C` and `L`-smooth over `C` with `L ≥ 0`, and `x⋆` a minimizer. For `t ≥ 1` let `γ_t` be the largest
power of `1/2` that is at most `η_t = 8/(t + 8)`. Every run of decomposition-invariant pairwise
Frank–Wolfe with these step sizes satisfies `f(x_t) - f(x⋆) ≤ 32 L δ²/(t + 7)` for all `t ≥ 1`. -/
def DIPFWBaseline : Prop :=
  ∀ (n : ℕ) (V : Finset (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (γ : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)), AwayStepFW.IsSimplexLike V →
    ConvexOn ℝ (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f →
    (∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f L → 0 ≤ L →
    (∀ t : ℕ, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ eta 8 t / 2 < γ t ∧ γ t ≤ eta 8 t) →
    AwayStepFW.IsDIPFWRun V f γ x →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f,
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      32 * L * Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) ^ 2 / (t + 7)

/-- **Theorem 5.3** (decomposition-invariant pairwise Frank–Wolfe, rates up to `O(1/t²)`). In the
setting of Proposition 5.2, with `L > 0`, `δ > 0`, a unique minimizer `x⋆` and a
`(μ, θ)`-Hölderian error bound with `μ > 0` and `θ ∈ [0, 1/2]`, every run satisfies, for `t ≥ 1`,
`h_t ≤ max {η_{t-2}^{1/(1-θ)} Lδ²/2, (η_{t-2} 2μLδ² √‖x⋆‖₀)^{1/(1-θ)} + η_{t-2}² Lδ²/2}`, where
`‖x⋆‖₀` is the number of nonzero coordinates of `x⋆` and `η_t = 8/(t + 8)`. -/
def DIPFWOpenLoopRate : Prop :=
  ∀ (n : ℕ) (V : Finset (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L μ θ : ℝ) (γ : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (xStar : EuclideanSpace ℝ (Fin n)),
    AwayStepFW.IsSimplexLike V →
    ConvexOn ℝ (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f →
    (∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f L → 0 < L →
    0 < Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) →
    IsHolderErrorBound (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f μ θ → 0 < μ →
    θ ∈ Set.Icc (0 : ℝ) (1 / 2) →
    minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f = {xStar} →
    (∀ t : ℕ, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ eta 8 t / 2 < γ t ∧ γ t ≤ eta 8 t) →
    AwayStepFW.IsDIPFWRun V f γ x →
    let δ := Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))))
    let k := ((Finset.univ.filter fun i => xStar i ≠ 0).card : ℝ)
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      max (eta 8 ((t : ℤ) - 2) ^ (1 / (1 - θ)) * (L * δ ^ 2 / 2))
        ((eta 8 ((t : ℤ) - 2) * (2 * μ * L * δ ^ 2 * √k)) ^ (1 / (1 - θ)) +
          eta 8 ((t : ℤ) - 2) ^ 2 * (L * δ ^ 2 / 2))

open Classical in
/-- One step of **away-step Frank–Wolfe with open-loop step sizes** (Algorithm 5 of the paper) from
the state `(x, S, λ, ℓ)`, where `ℓ` counts the progress steps so far, with Frank–Wolfe vertex `v`,
away vertex `a` for `g = f'(x)`, smoothness constant `L` and diameter `D`. With
`η = η_ℓ = 4/(ℓ + 4)`, the Frank–Wolfe step (when `g(a - x) ≤ g(x - v)`) has length
`γ = min {η, 1}` and the away step `γ = min {η, λ_a/(1 - λ_a)}`; weights and active set are updated
as usual, and the step is a progress step, `ℓ' = ℓ + 1`, when
`(η - γ) g(a - v) ≤ (η² - γ²) L D²`, and `ℓ' = ℓ` otherwise. -/
def IsOLAFWStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L D : ℝ)
    (g : StrongDual ℝ E) (x : E) (S : Finset E) (lam : E → ℝ) (ℓ : ℕ) (v a : E) (x' : E)
    (S' : Finset E) (lam' : E → ℝ) (ℓ' : ℕ) : Prop :=
  let η := eta 4 ℓ
  if g (a - x) ≤ g (x - v) then
    let γ := min η 1
    x' = x + γ • (v - x) ∧ lam' = (fun w => (1 - γ) * lam w + if w = v then γ else 0) ∧
      S' = (if γ = 1 then {v} else insert v S) ∧
      ℓ' = if (η - γ) * g (a - v) ≤ (η ^ 2 - γ ^ 2) * (L * D ^ 2) then ℓ + 1 else ℓ
  else
    let γ := min η (lam a / (1 - lam a))
    x' = x + γ • (x - a) ∧ lam' = (fun w => (1 + γ) * lam w - if w = a then γ else 0) ∧
      S' = (if γ = lam a / (1 - lam a) then S.erase a else S) ∧
      ℓ' = if (η - γ) * g (a - v) ≤ (η ^ 2 - γ ^ 2) * (L * D ^ 2) then ℓ + 1 else ℓ

open Classical in
/-- A run of **away-step Frank–Wolfe with open-loop step sizes** on `conv V` for `f` with
smoothness constant `L`: it starts at a vertex with active set `{x₀}`, weight `1` and no progress
steps, and every step is a step of `IsOLAFWStep` with the diameter `D` of `V`, some Frank–Wolfe
vertex (a minimizer of `f'(x_t)` over `V`) and some away vertex (a maximizer over `S_t`). -/
def IsOLAFWRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (L : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (ℓ : ℕ → ℕ) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ lam 0 = (fun w => if w = x 0 then 1 else 0) ∧ ℓ 0 = 0 ∧
    ∀ t, ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
      ∃ a ∈ S t, (∀ w ∈ S t, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) a) ∧
        IsOLAFWStep L (Metric.diam (↑V : Set E)) (fderiv ℝ f (x t)) (x t) (S t) (lam t) (ℓ t) v a
          (x (t + 1)) (S (t + 1)) (lam (t + 1)) (ℓ (t + 1))

/-- **Lemma 5.5** (drop-step characterization). For `A, B > 0`, `g(η) = -ηA + η²B` and
`γ ∈ [0, η]`, either `g(γ) ≤ g(0)` or `g(γ) ≤ g(η)`. -/
def DropStep : Prop :=
  ∀ A B η γ : ℝ, 0 < A → 0 < B → 0 ≤ γ → γ ≤ η →
    -γ * A + γ ^ 2 * B ≤ 0 ∨ -γ * A + γ ^ 2 * B ≤ -η * A + η ^ 2 * B

/-- **Lemma 5.6** (number of progress steps). Every run of away-step Frank–Wolfe with open-loop step
sizes has performed at least `⌈t/2⌉` progress steps before iteration `t`: `t ≤ 2 ℓ_t`. -/
def ProgressSteps : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : ℝ)
    (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (ℓ : ℕ → ℕ),
    IsOLAFWRun V f L x S lam ℓ → ∀ t, t ≤ 2 * ℓ t

/-- **Proposition 5.7** (away-step Frank–Wolfe with open-loop step sizes, rate `O(1/t)`). Let `f` be
convex over `conv V`, differentiable at its points and `L`-smooth over it with `L ≥ 0`, and `x⋆` a
minimizer. Every run satisfies `f(x_t) - f(x⋆) ≤ 16 L δ²/(t + 6)` for all `t ≥ 1`, where `δ` is the
diameter of `V`. -/
def OLAFWBaseline : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : ℝ)
    (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (ℓ : ℕ → ℕ),
    ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set E)) f L → 0 ≤ L → IsOLAFWRun V f L x S lam ℓ →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤ 16 * L * Metric.diam (↑V : Set E) ^ 2 / (t + 6)

/-- **Theorem 5.9** (away-step Frank–Wolfe with open-loop step sizes, rates up to `O(1/t²)`). In the
setting of Proposition 5.7, with `L > 0`, `δ > 0`, pyramidal width `ω > 0` and a
`(μ, θ)`-Hölderian error bound with `μ > 0` and `θ ∈ [0, 1/2]`, every run satisfies, for `t ≥ 1`
and `k = ⌈t/2⌉`, `h_t ≤ max {η_{k-2}^{1/(1-θ)} Lδ²/2, (η_{k-2} 2μLδ²/ω)^{1/(1-θ)} + η_{k-2}² Lδ²/2}`
with `η_t = 4/(t + 4)`. -/
def OLAFWRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (L μ θ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (ℓ : ℕ → ℕ),
    ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set E)) f L → 0 < L → 0 < Metric.diam (↑V : Set E) →
    0 < AwayStepFW.pyramidalWidth V →
    IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ → 0 < μ → θ ∈ Set.Icc (0 : ℝ) (1 / 2) →
    IsOLAFWRun V f L x S lam ℓ →
    let δ := Metric.diam (↑V : Set E)
    let ω := AwayStepFW.pyramidalWidth V
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        max (eta 4 ((((t + 1) / 2 : ℕ) : ℤ) - 2) ^ (1 / (1 - θ)) * (L * δ ^ 2 / 2))
          ((eta 4 ((((t + 1) / 2 : ℕ) : ℤ) - 2) * (2 * μ * L * δ ^ 2 / ω)) ^ (1 / (1 - θ)) +
            eta 4 ((((t + 1) / 2 : ℕ) : ℤ) - 2) ^ 2 * (L * δ ^ 2 / 2))

/-- **Lemma 4.1** (active set identification). Let `C = conv V` with diameter `δ > 0`, `F ⊆ V`, and
`f` convex over `C`, differentiable at its points, `L`-smooth over `C` with `L > 0` and with
`L`-Lipschitz derivative on `C`, with unique minimizer `x⋆` and a `(μ, θ)`-Hölderian error bound,
`μ > 0`, `θ ∈ (0, 1/2]`. Under strict complementarity with `κ > 0`, `f'(x⋆)(p - x⋆) ≥ κ` for
`p ∈ V \ F` and `f'(x⋆)(p - x⋆) = 0` for `p ∈ F`, every Frank–Wolfe run with `η_t = 4/(t + 4)` has
its atoms in `conv F` from `t = ⌈8Lδ² (2μLδ/κ)^{1/θ}⌉` on. -/
def ActiveSetIdentification : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V F : Finset E) (f : E → ℝ)
    (L μ θ κ : ℝ) (x v : ℕ → E) (xStar : E), F ⊆ V →
    ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set E)) f L → 0 < L →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) →
    0 < Metric.diam (convexHull ℝ (↑V : Set E)) →
    minimizers (convexHull ℝ (↑V : Set E)) f = {xStar} →
    IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ → 0 < μ → θ ∈ Set.Ioc (0 : ℝ) (1 / 2) →
    0 < κ → (∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar)) →
    (∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0) →
    IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t) →
    ∀ t : ℕ, ⌈8 * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 *
        (2 * μ * L * Metric.diam (convexHull ℝ (↑V : Set E)) / κ) ^ (1 / θ)⌉₊ ≤ t →
      v t ∈ convexHull ℝ (↑F : Set E)

/-- **Lemma 4.2** (scaling at the boundary, Bach). Let `C = conv V`, `f` convex over `C` and
differentiable at its points, and `x⋆` a minimizer in the affine hull of `F ⊆ V` such that every
point of that affine hull within distance `β > 0` of `x⋆` lies in `C`. For `x ∈ C`, an atom `p`
minimizing `f'(x)` over `C` and every direction `u` of the affine hull of `F` with `‖u‖ ≤ 1`,
`β f'(x)(u) ≤ f'(x)(x - p)`. In a Euclidean space the supremum over `u` is the norm of the gradient
projected onto these directions, which is the paper's statement. -/
def ScalingBoundary : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V F : Finset E) (f : E → ℝ) (β : ℝ)
    (xStar : E), ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f → xStar ∈ affineSpan ℝ (↑F : Set E) → 0 < β →
    (∀ y ∈ affineSpan ℝ (↑F : Set E), ‖y - xStar‖ ≤ β → y ∈ convexHull ℝ (↑V : Set E)) →
    ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ p ∈ convexHull ℝ (↑V : Set E),
      (∀ y ∈ convexHull ℝ (↑V : Set E), fderiv ℝ f x p ≤ fderiv ℝ f x y) →
      ∀ u ∈ vectorSpan ℝ (↑F : Set E), ‖u‖ ≤ 1 → β * fderiv ℝ f x u ≤ fderiv ℝ f x (x - p)

/-- **Lemma 4.3** (distance to the optimal face). Under the assumptions of Lemma 4.1, with the
minimizer `x⋆` in the affine hull of `F` and `β > 0`, let
`S = max {⌈8Lδ² (μ/β)^{1/θ}⌉, ⌈8Lδ² (2μLδ/κ)^{1/θ}⌉}`. Every Frank–Wolfe run with
`η_t = 4/(t + 4)` is within distance `(η_t/η_S)⁴ β` of the affine hull of `F` for all `t ≥ S`. In a
Euclidean space this distance is `‖(I - Π)(x_t - x⋆)‖`. -/
def DistanceToFace : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V F : Finset E) (f : E → ℝ)
    (L μ θ β κ : ℝ) (x v : ℕ → E) (xStar : E), F ⊆ V →
    ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set E)) f L → 0 < L →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) →
    0 < Metric.diam (convexHull ℝ (↑V : Set E)) →
    minimizers (convexHull ℝ (↑V : Set E)) f = {xStar} → xStar ∈ affineSpan ℝ (↑F : Set E) →
    IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ → 0 < μ → θ ∈ Set.Ioc (0 : ℝ) (1 / 2) →
    0 < β → 0 < κ → (∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar)) →
    (∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0) →
    IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t) →
    let δ := Metric.diam (convexHull ℝ (↑V : Set E))
    let S := max ⌈8 * L * δ ^ 2 * (μ / β) ^ (1 / θ)⌉₊
      ⌈8 * L * δ ^ 2 * (2 * μ * L * δ / κ) ^ (1 / θ)⌉₊
    ∀ t : ℕ, S ≤ t →
      Metric.infDist (x t) (affineSpan ℝ (↑F : Set E)) ≤ (eta 4 t / eta 4 S) ^ 4 * β

/-- **Lemma 4.4** (scaling from strong convexity near the optimal face). In a real inner product
space, let `C = conv V` with diameter `δ > 0`, `F ⊆ V`, `f` `α`-strongly convex on `C` with
`α > 0`, differentiable at the points of `C`, `L`-smooth over `C` with `L > 0` and with
`L`-Lipschitz derivative on `C`, with unique minimizer `x⋆` in the affine hull of `F`, such that
every point of that affine hull within distance `β > 0` of `x⋆` lies in `C`, and with strict
complementarity with `κ > 0`. Let `M = sup_{y ∈ C} ‖f'(y)‖` and
`S = max {⌈16Lδ²/(αβ²)⌉, ⌈64L³δ⁴/(ακ²)⌉}`. Every Frank–Wolfe run with `η_t = 4/(t + 4)` satisfies,
for `t ≥ S`, `h_t ≤ (η_t/η_S)⁴ βM` or there is a direction `u` of the affine hull of `F` with
`‖u‖ ≤ 1` and
`f'(x_t)(u) ≥ √(α/2) √h_t - (η_t/η_S)² √(αβM/2) - (η_t/η_S)⁴ Lβ`. -/
def ScalingCVX : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V F : Finset E) (f : E → ℝ)
    (L α β κ : ℝ) (x v : ℕ → E) (xStar : E), F ⊆ V →
    StrongConvexOn (convexHull ℝ (↑V : Set E)) α f → 0 < α →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set E)) f L → 0 < L →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) →
    0 < Metric.diam (convexHull ℝ (↑V : Set E)) →
    minimizers (convexHull ℝ (↑V : Set E)) f = {xStar} → xStar ∈ affineSpan ℝ (↑F : Set E) →
    0 < β → (∀ y ∈ affineSpan ℝ (↑F : Set E), ‖y - xStar‖ ≤ β → y ∈ convexHull ℝ (↑V : Set E)) →
    0 < κ → (∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar)) →
    (∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0) →
    IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t) →
    let δ := Metric.diam (convexHull ℝ (↑V : Set E))
    let M := sSup ((fun y => ‖fderiv ℝ f y‖) '' convexHull ℝ (↑V : Set E))
    let S := max ⌈16 * L * δ ^ 2 / (α * β ^ 2)⌉₊ ⌈64 * L ^ 3 * δ ^ 4 / (α * κ ^ 2)⌉₊
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤ (eta 4 t / eta 4 S) ^ 4 * β * M ∨
      ∃ u ∈ vectorSpan ℝ (↑F : Set E), ‖u‖ ≤ 1 ∧
        √(α / 2) * √(f (x t) - f xStar) - (eta 4 t / eta 4 S) ^ 2 * √(α * β * M / 2) -
          (eta 4 t / eta 4 S) ^ 4 * L * β ≤ fderiv ℝ f (x t) u

/-- **Theorem 4.5** (minimizer in the relative interior of a face). Under the assumptions of
Lemma 4.4, with `A = √α β/(2√2)`, `B = Lδ²/2 + β√(αβM)/(2√2 η_S) + Lβ²/(2η_S)`, `D = βM` and
`E = Lδ²/2`, every Frank–Wolfe run with `η_t = 4/(t + 4)` satisfies, for `t ≥ S`,
`h_t ≤ η_{t-2}² max {h_S/η_{S-1}², B²/A² + B, D/η_S² + E}`. -/
def PolytopeFaceRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V F : Finset E) (f : E → ℝ)
    (L α β κ : ℝ) (x v : ℕ → E) (xStar : E), F ⊆ V →
    StrongConvexOn (convexHull ℝ (↑V : Set E)) α f → 0 < α →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsSmoothOn (convexHull ℝ (↑V : Set E)) f L → 0 < L →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) →
    0 < Metric.diam (convexHull ℝ (↑V : Set E)) →
    minimizers (convexHull ℝ (↑V : Set E)) f = {xStar} → xStar ∈ affineSpan ℝ (↑F : Set E) →
    0 < β → (∀ y ∈ affineSpan ℝ (↑F : Set E), ‖y - xStar‖ ≤ β → y ∈ convexHull ℝ (↑V : Set E)) →
    0 < κ → (∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar)) →
    (∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0) →
    IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta 4 t) →
    let δ := Metric.diam (convexHull ℝ (↑V : Set E))
    let M := sSup ((fun y => ‖fderiv ℝ f y‖) '' convexHull ℝ (↑V : Set E))
    let S := max ⌈16 * L * δ ^ 2 / (α * β ^ 2)⌉₊ ⌈64 * L ^ 3 * δ ^ 4 / (α * κ ^ 2)⌉₊
    let cA := √α * β / (2 * √2)
    let cB := L * δ ^ 2 / 2 + β * √(α * β * M) / (eta 4 S * 2 * √2) + L * β ^ 2 / (eta 4 S * 2)
    let cD := β * M
    let cE := L * δ ^ 2 / 2
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤ eta 4 ((t : ℤ) - 2) ^ 2 *
      max (max ((f (x S) - f xStar) / eta 4 ((S : ℤ) - 1) ^ 2) (cB ^ 2 / cA ^ 2 + cB))
        (cD / eta 4 S ^ 2 + cE)

end Lemmata.FWOpenLoop
