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

end Lemmata.FWProduct
