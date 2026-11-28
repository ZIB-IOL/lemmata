module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Lemmata.CGBasics.Statement
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWCaratheodory

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

/-- The objective `f(z) = ‖z - x⋆‖²/2` of the approximate Carathéodory problem. -/
noncomputable def lpObjective {E : Type*} [NormedAddCommGroup E] (xStar : E) (z : E) : ℝ :=
  ‖z - xStar‖ ^ 2 / 2

/-- **Lemma 3.1** (the objective). Let `2 ≤ p < ∞`, `x⋆ ∈ ℓ_p^n` and `f(z) = ‖z - x⋆‖_p²/2`. Then
`f` is differentiable and convex, satisfies the quadratic upper bound
`f(y) ≤ f(x) + f'(x)(y - x) + (p - 1)/2 ‖y - x‖_p²` (it is `(p - 1)`-smooth), has a
`(p - 1)`-Lipschitz derivative, and `‖f'(z)‖ = ‖z - x⋆‖_p`, so that `f(z) = ‖f'(z)‖²/2` and `f` is
`1`-gradient dominated. On every set `C` containing `x⋆`, `f` satisfies a `(√2, 1/2)`-Hölderian
error bound (it is `√2`-sharp). -/
def LpObjective : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ xStar : PiLp p (fun _ : Fin n => ℝ),
      Differentiable ℝ (lpObjective xStar) ∧ ConvexOn ℝ Set.univ (lpObjective xStar) ∧
      (∀ x y, lpObjective xStar y ≤ lpObjective xStar x + fderiv ℝ (lpObjective xStar) x (y - x) +
        (p.toReal - 1) / 2 * ‖y - x‖ ^ 2) ∧
      LipschitzWith (Real.toNNReal (p.toReal - 1)) (fderiv ℝ (lpObjective xStar)) ∧
      (∀ z, ‖fderiv ℝ (lpObjective xStar) z‖ = ‖z - xStar‖) ∧
      ∀ C : Set (PiLp p (fun _ : Fin n => ℝ)), xStar ∈ C →
        IsHolderErrorBound C (lpObjective xStar) (Real.sqrt 2) (1 / 2)

/-- The `j`-th column of a matrix `H`, normalized by `n^{1/p}`, as a point of `ℓ_p^n`. -/
noncomputable def hadamardVertex {n : ℕ} (p : ENNReal) (H : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    PiLp p (fun _ : Fin n => ℝ) :=
  WithLp.toLp p (fun i => H i j / (n : ℝ) ^ (1 / p.toReal))

/-- The barycenter of the normalized columns. For Sylvester's Hadamard matrix it is
`e₁/n^{1/p}`. -/
noncomputable def hadamardCenter {n : ℕ} (p : ENNReal) (H : Matrix (Fin n) (Fin n) ℝ) :
    PiLp p (fun _ : Fin n => ℝ) :=
  (1 / (n : ℝ)) • ∑ j, hadamardVertex p H j

/-- **Theorem 8.1** (a lower bound). Let `2 ≤ p < ∞` and let `H` be a Hadamard matrix of order
`n`: its entries are `±1` and its columns are orthogonal. If a point `x` of the convex hull of the
normalized columns `H_j/n^{1/p}`, `j ∈ S`, satisfies `‖x - x⋆‖_p ≤ ε` for the barycenter `x⋆` of all
normalized columns, then `|S| ≥ 1/(ε² + 1/n)`. -/
def HadamardLowerBound : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ H : Matrix (Fin n) (Fin n) ℝ, (∀ i j, H i j = 1 ∨ H i j = -1) →
      (∀ j k, j ≠ k → ∑ i, H i j * H i k = 0) →
      ∀ (ε : ℝ) (S : Finset (Fin n)) (x : PiLp p (fun _ : Fin n => ℝ)),
        x ∈ convexHull ℝ (hadamardVertex p H '' ↑S) → ‖x - hadamardCenter p H‖ ≤ ε →
          1 ≤ (S.card : ℝ) * (ε ^ 2 + 1 / n)

/-- **Sparse iterates** (Section 3). Every Frank–Wolfe run that starts at a point of `V` and only
uses atoms in `V` writes `x_t` as a convex combination of at most `t + 1` points of `V`. -/
def RunSparsity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C V : Set E)
    (f' : E → StrongDual ℝ E) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsFWRun C f' x v γ → x 0 ∈ V → (∀ t, v t ∈ V) →
      ∀ t : ℕ, ∃ S : Finset E, ↑S ⊆ V ∧ S.card ≤ t + 1 ∧ x t ∈ convexHull ℝ (↑S : Set E)

/-- **Corollary 5.1**, for short steps. Let `2 ≤ p < ∞`, let `V ⊆ ℓ_p^n` be finite with diameter
`D` and `x⋆ ∈ conv(V)`. Every short-step Frank–Wolfe run for `‖z - x⋆‖_p²/2` over `conv(V)` that
starts at a point of `V` and uses atoms in `V` satisfies `‖x_t - x⋆‖_p ≤ ε` as soon as
`t + 3 ≥ 4 (p - 1) D²/ε²`, with `x_t` a convex combination of at most `t + 1` points of `V`. -/
def ShortStepCardinality : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ (V : Set (PiLp p (fun _ : Fin n => ℝ))) (xStar : PiLp p (fun _ : Fin n => ℝ))
      (x v : ℕ → PiLp p (fun _ : Fin n => ℝ)) (γ : ℕ → ℝ),
      V.Finite → xStar ∈ convexHull ℝ V → x 0 ∈ V → (∀ t, v t ∈ V) →
      IsShortStepRun (convexHull ℝ V) (lpObjective xStar) (Real.toNNReal (p.toReal - 1)) x v γ →
      ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
        4 * (p.toReal - 1) * Metric.diam V ^ 2 / ε ^ 2 ≤ (t : ℝ) + 3 →
        ‖x t - xStar‖ ≤ ε ∧ ∃ S : Finset (PiLp p (fun _ : Fin n => ℝ)), ↑S ⊆ V ∧ S.card ≤ t + 1 ∧
          x t ∈ convexHull ℝ (↑S : Set (PiLp p (fun _ : Fin n => ℝ)))

/-- **Corollary 5.3** (a target in the relative interior). In the setting of
`ShortStepCardinality`, let every point of the affine hull of `conv(V)` within distance `r > 0` of
`x⋆` lie in `conv(V)`. With `K = max {2, 4 (p - 1) D²/r²}`, every such run satisfies
`‖x_t - x⋆‖_p ≤ ε` as soon as `t ≥ 1 + K log((p - 1) D²/ε²)`, with `x_t` a convex combination of at
most `t + 1` points of `V`. -/
def InteriorCardinality : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ (V : Set (PiLp p (fun _ : Fin n => ℝ))) (xStar : PiLp p (fun _ : Fin n => ℝ)) (r : ℝ)
      (x v : ℕ → PiLp p (fun _ : Fin n => ℝ)) (γ : ℕ → ℝ),
      V.Finite → xStar ∈ convexHull ℝ V → 0 < r →
      (∀ z ∈ affineSpan ℝ (convexHull ℝ V), ‖z - xStar‖ ≤ r → z ∈ convexHull ℝ V) →
      x 0 ∈ V → (∀ t, v t ∈ V) →
      IsShortStepRun (convexHull ℝ V) (lpObjective xStar) (Real.toNNReal (p.toReal - 1)) x v γ →
      ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
        1 + max 2 (4 * (p.toReal - 1) * Metric.diam V ^ 2 / r ^ 2) *
          Real.log ((p.toReal - 1) * Metric.diam V ^ 2 / ε ^ 2) ≤ t →
        ‖x t - xStar‖ ≤ ε ∧ ∃ S : Finset (PiLp p (fun _ : Fin n => ℝ)), ↑S ⊆ V ∧ S.card ≤ t + 1 ∧
          x t ∈ convexHull ℝ (↑S : Set (PiLp p (fun _ : Fin n => ℝ)))

/-- **Corollary 7.1** (sparse approximate projections onto strongly convex sets). Let `2 ≤ p < ∞`,
let `C ⊆ ℓ_p^n` be compact, convex and `α`-strongly convex with diameter `D`, let `V ⊆ C` (for
instance its extreme points) and `x⋆ ∉ C`, and let `c = dist(x⋆, C)`. With
`K = max {2, 2 (p - 1)/(α c)}`, every short-step Frank–Wolfe run for `‖z - x⋆‖_p²/2` over `C` that
starts at a point of `V` and uses atoms in `V` satisfies `‖x_t - x⋆‖_p² - c² ≤ ε²` as soon as
`t ≥ 1 + K log((p - 1) D²/ε²)`, with `x_t` a convex combination of at most `t + 1` points of
`V`. -/
def ProjectionCardinality : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ (C V : Set (PiLp p (fun _ : Fin n => ℝ))) (α : ℝ) (xStar : PiLp p (fun _ : Fin n => ℝ))
      (x v : ℕ → PiLp p (fun _ : Fin n => ℝ)) (γ : ℕ → ℝ),
      IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α 2 → 0 < α → V ⊆ C → xStar ∉ C →
      x 0 ∈ V → (∀ t, v t ∈ V) →
      IsShortStepRun C (lpObjective xStar) (Real.toNNReal (p.toReal - 1)) x v γ →
      ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
        1 + max 2 (2 * (p.toReal - 1) / (α * Metric.infDist xStar C)) *
          Real.log ((p.toReal - 1) * Metric.diam C ^ 2 / ε ^ 2) ≤ t →
        ‖x t - xStar‖ ^ 2 - Metric.infDist xStar C ^ 2 ≤ ε ^ 2 ∧
          ∃ S : Finset (PiLp p (fun _ : Fin n => ℝ)), ↑S ⊆ V ∧ S.card ≤ t + 1 ∧
            x t ∈ convexHull ℝ (↑S : Set (PiLp p (fun _ : Fin n => ℝ)))

end Lemmata.FWCaratheodory
