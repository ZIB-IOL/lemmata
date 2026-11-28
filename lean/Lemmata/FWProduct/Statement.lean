module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Lemmata.AwayStepFW.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe Lemmata.AwayStepFW

universe u

/-- The objective `f(x) = (1/(2k)) ∑_{i < j} ‖x^i - x^j‖²` of the approximate feasibility problem
for an intersection of `k` sets, on the Euclidean product of `k` copies of `E`. -/
noncomputable def feasibilityObjective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (x : PiLp 2 (fun _ : Fin k => E)) : ℝ :=
  1 / (2 * k) * ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖ ^ 2

/-- **Proposition 5.1** (convexity, smoothness and PL). On the Euclidean product of `k` copies of a
real inner product space, the objective `f(x) = (1/(2k)) ∑_{i < j} ‖x^i - x^j‖²` is differentiable
and convex, satisfies the quadratic upper bound with constant `1` (it is `1`-smooth), has a
`1`-Lipschitz derivative, and `‖f'(x)‖² = 2 f(x)`; since `f ≥ 0`, it is `1`-PL:
`‖f'(x)‖²/2 ≥ f(x) - f(y)` for all `x, y`. -/
def FeasibilityObjective : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ),
    Differentiable ℝ (feasibilityObjective (E := E) k) ∧
      ConvexOn ℝ Set.univ (feasibilityObjective (E := E) k) ∧
      (∀ x y, feasibilityObjective k y ≤ feasibilityObjective k x +
        fderiv ℝ (feasibilityObjective (E := E) k) x (y - x) + 1 / 2 * ‖y - x‖ ^ 2) ∧
      LipschitzWith 1 (fderiv ℝ (feasibilityObjective (E := E) k)) ∧
      ∀ x, ‖fderiv ℝ (feasibilityObjective (E := E) k) x‖ ^ 2 = 2 * feasibilityObjective k x

/-- **Lemma A.2** (preparatory bounds). For `a, b > 0`,
`min {a, b}/√2 ≤ √(a²b²/(a² + b²)) < min {a, b}`, and `√(a²b²/(a² + b²))` is nondecreasing in
`a` (and, by symmetry, in `b`). -/
def PreparatoryBounds : Prop :=
  (∀ a b : ℝ, 0 < a → 0 < b →
    min a b / Real.sqrt 2 ≤ Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) ∧
      Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) < min a b) ∧
  ∀ a a' b : ℝ, 0 < a → a ≤ a' → 0 < b →
    Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) ≤ Real.sqrt (a' ^ 2 * b ^ 2 / (a' ^ 2 + b ^ 2))

open Classical in
/-- The **affine pyramidal width** of `conv V` (Definition 4.2): the infimum of `‖a - q‖` over
proper exposed faces `F`, points `a` of the affine hull of `F` and `q ∈ conv (V \ F)`. The
pyramidal width of the paper (Definition 4.1) is the facial distance `AwayStepFW.facialDistance`,
with `a ∈ conv F`. -/
noncomputable def affinePyramidalWidth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Finset E) : ℝ :=
  sInf {r : ℝ | ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
    ∃ a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E),
      ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), r = ‖a - q‖}

open Classical in
/-- The vertex set `V₁ × V₂` of the product polytope, in the Euclidean product of the spaces. -/
noncomputable def productVertices {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    (V₁ : Finset E₁) (V₂ : Finset E₂) : Finset (WithLp 2 (E₁ × E₂)) :=
  (V₁ ×ˢ V₂).image (WithLp.toLp 2)

/-- **Corollary 4.4**, the easy inequality: the affine pyramidal width is at most the pyramidal
width (the facial distance). -/
def AffineWidthLeFacial : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E),
    affinePyramidalWidth V ≤ facialDistance V

/-- **Theorem 4.5**, the lower bound. For finite nonempty sets `V₁, V₂` in real inner product
spaces, with affine pyramidal widths `ŵ₁, ŵ₂`, the pyramidal width (the facial distance) of the
product `conv V₁ × conv V₂` in the Euclidean product is at least `√(ŵ₁² ŵ₂²/(ŵ₁² + ŵ₂²))`. -/
def ProductWidthLowerBound : Prop :=
  ∀ {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₂] (V₁ : Finset E₁) (V₂ : Finset E₂), V₁.Nonempty → V₂.Nonempty →
    Real.sqrt (affinePyramidalWidth V₁ ^ 2 * affinePyramidalWidth V₂ ^ 2 /
      (affinePyramidalWidth V₁ ^ 2 + affinePyramidalWidth V₂ ^ 2)) ≤
      facialDistance (productVertices V₁ V₂)

/-- **Theorem 4.5**, the upper bound. For finite sets `V₁, V₂` with at least two points each in real
inner product spaces, with pyramidal widths (facial distances) `δ₁, δ₂`, the pyramidal width of the
product `conv V₁ × conv V₂` in the Euclidean product is at most `√(δ₁² δ₂²/(δ₁² + δ₂²))`. -/
def ProductWidthUpperBound : Prop :=
  ∀ {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₂] (V₁ : Finset E₁) (V₂ : Finset E₂), 1 < V₁.card → 1 < V₂.card →
    facialDistance (productVertices V₁ V₂) ≤
      Real.sqrt (facialDistance V₁ ^ 2 * facialDistance V₂ ^ 2 /
        (facialDistance V₁ ^ 2 + facialDistance V₂ ^ 2))

/-- **Proposition 4.8**, for a product of two polytopes and quadratic growth. Let `E₁, E₂` be
finite-dimensional real inner product spaces, `V₁, V₂` finite sets with positive affine pyramidal
widths `ŵ₁, ŵ₂`, and `α² = ŵ₁² ŵ₂²/(ŵ₁² + ŵ₂²)`. Let `f` be convex and `L`-smooth with `L > 0` and
have `μ`-quadratic growth on the product polytope `P = conv V₁ × conv V₂`:
`μ/2 dist(y, Ω*)² ≤ f(y) - f(x⋆)` for `y ∈ P`, where `Ω*` is the set of minimizers. Every run of
away-step Frank–Wolfe over `P` satisfies
`f(x_t) - f(x⋆) ≤ (1 - min {1/2, μ α²/(16 L D²)})^⌊(t-1)/2⌋ L D²/2` for `t ≥ 1`, where `D` is the
diameter of `V₁ × V₂`. -/
def ProductAwayLinear : Prop :=
  ∀ {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (V₁ : Finset E₁) (V₂ : Finset E₂) (f : WithLp 2 (E₁ × E₂) → ℝ) (L : NNReal) (μ : ℝ)
    (x : ℕ → WithLp 2 (E₁ × E₂)) (S : ℕ → Finset (WithLp 2 (E₁ × E₂)))
    (lam : ℕ → WithLp 2 (E₁ × E₂) → ℝ),
    0 < (L : ℝ) → 0 < μ → 0 < affinePyramidalWidth V₁ → 0 < affinePyramidalWidth V₂ →
    ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ y ∈ convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂))),
      ∀ xStar ∈ minimizers (convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂)))) f,
        μ / 2 * Metric.infDist y
          (minimizers (convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂)))) f) ^ 2 ≤
          f y - f xStar) →
    IsAFWRun (productVertices V₁ V₂) f L x S lam →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂)))) f,
    ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (μ * (affinePyramidalWidth V₁ ^ 2 * affinePyramidalWidth V₂ ^ 2 /
            (affinePyramidalWidth V₁ ^ 2 + affinePyramidalWidth V₂ ^ 2)) /
          (16 * L * Metric.diam (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂))) ^ 2))) ^
            ((t - 1) / 2) *
          (L * Metric.diam (↑(productVertices V₁ V₂) : Set (WithLp 2 (E₁ × E₂))) ^ 2 / 2)

/-- A **facet** of `conv V`: a proper exposed face (given by its vertex set `F`) that is contained
in no other proper exposed face. -/
def IsFacet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V F : Finset E) : Prop :=
  (∃ ψ : StrongDual ℝ E, exposedFace V ψ = F) ∧ F ≠ V ∧
    ∀ φ : StrongDual ℝ E, F ⊆ exposedFace V φ → exposedFace V φ ≠ V → exposedFace V φ = F

open Classical in
/-- The **vertex-facet distance** of `conv V` (Definition 4.6): the infimum of `‖a - v‖` over facets
`F`, points `a` of the affine hull of `F` and vertices `v ∈ V \ F`. -/
noncomputable def vertexFacetDistance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Finset E) : ℝ :=
  sInf {r : ℝ | ∃ F : Finset E, IsFacet V F ∧ ∃ a ∈ affineSpan ℝ (↑F : Set E), ∃ v ∈ V \ F,
    r = ‖a - v‖}

/-- **Proposition 4.7** (vertex-facet distance of the product). For finite sets `V₁, V₂` with at
least two points each in real inner product spaces, the vertex-facet distance of
`conv V₁ × conv V₂` in the Euclidean product is the smaller of the vertex-facet distances of the
factors. -/
def ProductVertexFacet : Prop :=
  ∀ {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₂] (V₁ : Finset E₁) (V₂ : Finset E₂), 1 < V₁.card → 1 < V₂.card →
    vertexFacetDistance (productVertices V₁ V₂) =
      min (vertexFacetDistance V₁) (vertexFacetDistance V₂)

open Classical in
/-- **Lemma 4.3**. Let `E` be a finite-dimensional real inner product space and `V` a finite set.
If a proper exposed face `F` of `conv V`, a point `a` of the affine hull of `F` and a point
`q ∈ conv (V \ F)` realize the affine pyramidal width, `‖a - q‖ = ŵ`, then `a` lies in the relative
interior of `conv F`: it lies in `conv F`, and its minimal face is `F` (it lies in no proper face
of `conv F`). -/
def AffineWidthRelint : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Finset E) (ψ : StrongDual ℝ E) (a q : E), exposedFace V ψ ≠ V →
    a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E) →
    q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E) → ‖a - q‖ = affinePyramidalWidth V →
    a ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E) ∧
      minFace (exposedFace V ψ) a = exposedFace V ψ

/-- **Corollary 4.4**. In a finite-dimensional real normed space, the affine pyramidal width of
`conv V` equals its pyramidal width, the facial distance. -/
def AffineWidthEq : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Finset E), affinePyramidalWidth V = facialDistance V

/-- **Theorem 4.5**. For finite sets `V₁, V₂` with at least two points each in finite-dimensional
real inner product spaces, with pyramidal widths (facial distances) `δ₁, δ₂`, the pyramidal width
of the product `conv V₁ × conv V₂` in the Euclidean product is `√(δ₁² δ₂²/(δ₁² + δ₂²))`. -/
def ProductWidthEq : Prop :=
  ∀ {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (V₁ : Finset E₁) (V₂ : Finset E₂), 1 < V₁.card → 1 < V₂.card →
    facialDistance (productVertices V₁ V₂) =
      Real.sqrt (facialDistance V₁ ^ 2 * facialDistance V₂ ^ 2 /
        (facialDistance V₁ ^ 2 + facialDistance V₂ ^ 2))

open Classical in
/-- The vertex set `V₀ × ⋯ × V_{k-1}` of a product of `k` polytopes, in the Euclidean product of
`k` copies of `E`. -/
noncomputable def piVertices {E : Type*} [NormedAddCommGroup E] {k : ℕ} (V : Fin k → Finset E) :
    Finset (PiLp 2 (fun _ : Fin k => E)) :=
  (Fintype.piFinset V).image (WithLp.toLp 2)

/-- **Corollary A.3** (products of `k` polytopes), with the exact value. Let `V₀, …, V_k` be finite
sets with at least two points each in a finite-dimensional real inner product space, with pyramidal
widths (facial distances) `δ_i`. The pyramidal width of their product, in the Euclidean product, is
`(∑ δ_i^{-2})^{-1/2}`; hence it is at least `m/√(k+1)` whenever `0 ≤ m ≤ δ_i` for all `i`. -/
def ProductWidthMany : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (V : Fin (k + 1) → Finset E), (∀ i, 1 < (V i).card) →
    facialDistance (piVertices V) = (∑ i, facialDistance (V i) ^ (-2 : ℝ)) ^ (-(1 / 2 : ℝ)) ∧
    ∀ m : ℝ, 0 ≤ m → (∀ i, m ≤ facialDistance (V i)) →
      m / Real.sqrt (k + 1) ≤ facialDistance (piVertices V)

end Lemmata.FWProduct
