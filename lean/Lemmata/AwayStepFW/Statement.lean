module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Lemmata.AwayStepFW.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2

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

open Classical in
/-- **Corollary 2.32, corrected** (pyramidal width from an inequality description). Let the rows
`a_i x ≤ b_i` hold on `V`, and let every vertex off a proper exposed face be slack in some row that
is tight on the face. Then the pyramidal width is at least the infimum of `(∑_{i ∈ I} (b_i - a_i v))
/ ‖∑_{i ∈ I} a_i‖` over row sets `I` tight at some vertex and vertices `v` with positive total slack
on `I`. -/
def PyramidalWidthLowerBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V : Finset E)
    {ι : Type} [Fintype ι] (a : ι → StrongDual ℝ E) (b : ι → ℝ),
    (∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V) → (∀ v ∈ V, ∀ i, a i v ≤ b i) →
    (∀ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V → ∀ v ∈ V \ exposedFace V ψ,
      ∃ i, (∀ w ∈ exposedFace V ψ, a i w = b i) ∧ a i v < b i) →
    sInf {r : ℝ | ∃ I : Finset ι, ∃ w ∈ V, (∀ i ∈ I, a i w = b i) ∧ ∃ v ∈ V,
      0 < ∑ i ∈ I, (b i - a i v) ∧ r = (∑ i ∈ I, (b i - a i v)) / ‖∑ i ∈ I, a i‖} ≤
      pyramidalWidth V

/-- **Theorem 3.2** (linear convergence of pairwise Frank–Wolfe). Under the assumptions of
`AwayStepConvergence`, every run of pairwise Frank–Wolfe satisfies
`f(x_t) - f(x⋆) ≤ (1 - min {1/2, μ δ² / (L D²)})^⌊(t-1)/(2|V|! + 2)⌋ L D²/2` for `t ≥ 1`. -/
def PairwiseConvergence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (μ δ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ),
    0 < (L : ℝ) → 0 < μ → 0 < δ → IsScaling V δ → ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    IsPFWRun V f L x S lam →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (μ * δ ^ 2 / (L * Metric.diam (↑V : Set E) ^ 2))) ^
            ((t - 1) / (2 * V.card.factorial + 2)) * (L * Metric.diam (↑V : Set E) ^ 2 / 2)

/-- A **simplex-like polytope** (Section 3.1.1): every point of `V` is a `0/1` vector, and `conv V`
is cut out of an affine subspace `W` by the nonnegativity constraints, i.e.
`conv V = {x ∈ ℝⁿ | x ≥ 0, A x = b}`. -/
def IsSimplexLike {n : ℕ} (V : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ v ∈ V, ∀ i, v i = 0 ∨ v i = 1) ∧
    ∃ W : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
      convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) = {x | ∀ i, 0 ≤ x i} ∩ (W : Set _)

/-- A run of **decomposition-invariant pairwise Frank–Wolfe** (Algorithm 3.3) with step sizes `γ`.
As in Garber and Meshi, `x₀ ∈ conv V` and `x₁ ∈ V` is a Frank–Wolfe vertex for `f'(x₀)`. For
`t ≥ 1`, `x_{t+1} = x_t + γ_t (v_t - a_t)` with a Frank–Wolfe vertex `v_t` and a vertex `a_t` that
maximizes `f'(x_t)` over the vertices whose support lies in that of `x_t`, i.e. over the vertices of
the minimal face of `x_t`. -/
def IsDIPFWRun {n : ℕ} (V : Finset (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (γ : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 0 ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) ∧ x 1 ∈ V ∧
    (∀ w ∈ V, fderiv ℝ f (x 0) (x 1) ≤ fderiv ℝ f (x 0) w) ∧
    ∀ t, 1 ≤ t → ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
      ∃ a ∈ V, (∀ i, x t i = 0 → a i = 0) ∧
        (∀ w ∈ V, (∀ i, x t i = 0 → w i = 0) → fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) a) ∧
        x (t + 1) = x t + γ t • (v - a)

/-- **Sparsity scaling** (Garber and Meshi, Lemma 2). Let `conv V` be simplex-like, `x, y ∈ conv V`,
`ψ` a direction, `a ∈ V` a vertex maximizing `ψ` over the vertices whose support lies in that of
`x`, and `v ∈ V` a Frank–Wolfe vertex. Then `ψ(x - y) ≤ √‖y‖₀ ‖x - y‖ ψ(a - v)`, where `‖y‖₀` is
the number of nonzero coordinates of `y`. -/
def SparsityScaling : Prop :=
  ∀ (n : ℕ) (V : Finset (EuclideanSpace ℝ (Fin n))), IsSimplexLike V →
    ∀ x ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))),
    ∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))),
    ∀ (ψ : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) (a v : EuclideanSpace ℝ (Fin n)),
    a ∈ V → (∀ i, x i = 0 → a i = 0) → (∀ w ∈ V, (∀ i, x i = 0 → w i = 0) → ψ w ≤ ψ a) →
    v ∈ V → (∀ w ∈ V, ψ v ≤ ψ w) →
      ψ (x - y) ≤ √((Finset.univ.filter fun i => y i ≠ 0).card : ℝ) * ‖x - y‖ * ψ (a - v)

/-- **Feasibility** (Garber and Meshi, Lemma 1). On a simplex-like polytope, if the step sizes `γ_t`
for `t ≥ 1` are nonincreasing powers of `1/2`, every run of DI-PFW stays in `conv V`. -/
def DIPFWFeasible : Prop :=
  ∀ (n : ℕ) (V : Finset (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (γ : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)), IsSimplexLike V →
    (∀ t, 1 ≤ t → ∃ m : ℕ, γ t = (1 / 2) ^ m) → (∀ t, 1 ≤ t → γ (t + 1) ≤ γ t) →
    IsDIPFWRun V f γ x → ∀ t, x t ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))

/-- **Theorem 3.8** (decomposition-invariant pairwise Frank–Wolfe), with the rate that the proof
gives. Let `conv V` be simplex-like and `f` `L`-smooth and `μ`-strongly convex on `conv V` with
minimizer `x⋆`, and let `c = μ/(16 L D² ‖x⋆‖₀)`. If for `t ≥ 1` the step sizes `γ_t` are
nonincreasing powers of `1/2` in `[η_t/2, η_t]` with `η_t = √c (1 - c)^{(t-1)/2}`, then every run
of DI-PFW satisfies `f(x_t) - f(x⋆) ≤ (L D²/2) (1 - c)^{t-1}` for `t ≥ 1`. -/
def DIPFWRate : Prop :=
  ∀ (n : ℕ) (V : Finset (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : NNReal) (μ : ℝ) (γ : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)), IsSimplexLike V →
    IsSmooth f L → 0 < μ →
    (∀ x ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))),
      ∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f,
      let c := μ / (16 * L * Metric.diam (↑V : Set (EuclideanSpace ℝ (Fin n))) ^ 2 *
        (Finset.univ.filter fun i => xStar i ≠ 0).card)
      (∀ t, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ γ (t + 1) ≤ γ t ∧
        √c * (1 - c) ^ (((t : ℝ) - 1) / 2) / 2 ≤ γ t ∧
        γ t ≤ √c * (1 - c) ^ (((t : ℝ) - 1) / 2)) →
      IsDIPFWRun V f γ x → ∀ t, 1 ≤ t →
        f (x t) - f xStar ≤
          L * Metric.diam (↑V : Set (EuclideanSpace ℝ (Fin n))) ^ 2 / 2 * (1 - c) ^ (t - 1)

end Lemmata.AwayStepFW
