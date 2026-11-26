module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Lemmata.FrankWolfe.Polytope.Defs
public import Lemmata.FrankWolfe.HilbertDefs
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# The basic results, as statements without proofs

One proposition per result of the core, about the objects of `Defs.lean` (in a real normed
space, with derivatives `fderiv ℝ f`) and of `HilbertDefs.lean` (in a Hilbert space, with
gradients). `Main.lean` proves them; nothing here depends on a proof.
-/

namespace Lemmata.FrankWolfe

universe u

/-- **The gap inequalities.** For a convex differentiable `f`, a minimizer `x⋆` over a compact
set `C` and `x ∈ C`, the primal gap is at most the dual gap, which is at most the Frank–Wolfe gap:
`f x - f x⋆ ≤ f'(x)(x - x⋆) ≤ max_{v ∈ C} f'(x)(x - v)`. -/
def GapInequalities : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ),
    IsCompact C → ConvexOn ℝ Set.univ f → Differentiable ℝ f →
    ∀ xStar ∈ minimizers C f, ∀ x ∈ C,
      f x - f xStar ≤ fderiv ℝ f x (x - xStar) ∧ fderiv ℝ f x (x - xStar) ≤ fwGap C (fderiv ℝ f) x

/-- **The descent lemma.** An `L`-smooth function lies below its quadratic upper model:
`f y ≤ f x + f'(x)(y - x) + L/2 ‖y - x‖²`. -/
def DescentLemma : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal),
    IsSmooth f L → ∀ x y : E, f y ≤ f x + fderiv ℝ f x (y - x) + L / 2 * ‖y - x‖ ^ 2

/-- **Primal progress from smoothness.** A step of length `γ` from `x` toward `v` decreases an
`L`-smooth `f` by at least `γ f'(x)(x - v) - γ² L/2 ‖v - x‖²`. -/
def ProgressLemma : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal),
    IsSmooth f L → ∀ (x v : E) (γ : ℝ),
      f (x + γ • (v - x)) ≤ f x - γ * fderiv ℝ f x (x - v) + γ ^ 2 * L / 2 * ‖v - x‖ ^ 2

/-- **`O(1/t)` convergence.** Under the standing assumptions, with the open-loop rule
`γ_t = 2/(t+2)`, short steps or exact line search, `f(x_t) - f(x⋆) ≤ 2 L D² / (t + 2)` for every
`t ≥ 1`, where `D` is the diameter of `C`. -/
def StandardRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (lmo : StrongDual ℝ E → E) (f : E → ℝ) (L : NNReal),
    StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f (fderiv ℝ f) σ →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ t : ℕ, 1 ≤ t →
      f (fwIterates lmo (fderiv ℝ f) (openLoopStep 2) x₀ t) - f xStar ≤
        2 * L * Metric.diam C ^ 2 / (t + 2) ∧
      f (fwIterates lmo (fderiv ℝ f) (shortStep lmo (fderiv ℝ f) L) x₀ t) - f xStar ≤
        2 * L * Metric.diam C ^ 2 / (t + 2) ∧
      f (fwIterates lmo (fderiv ℝ f) (fun _ => σ) x₀ t) - f xStar ≤
        2 * L * Metric.diam C ^ 2 / (t + 2)

/-- **`O(1/t)` convergence in a Hilbert space**, in the language of gradients: the statement of
`StandardRate` for the objects of `HilbertDefs.lean`. -/
def StandardRateHilbert : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), Hilbert.StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, Hilbert.IsExactLineSearch lmo f σ →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ t : ℕ, 1 ≤ t →
      f (Hilbert.fwIterates lmo f Hilbert.openLoopStep x₀ t) - f xStar ≤
        2 * L * Metric.diam C ^ 2 / (t + 2) ∧
      f (Hilbert.fwIterates lmo f (Hilbert.shortStep lmo f L) x₀ t) - f xStar ≤
        2 * L * Metric.diam C ^ 2 / (t + 2) ∧
      f (Hilbert.fwIterates lmo f (fun _ => σ) x₀ t) - f xStar ≤
        2 * L * Metric.diam C ^ 2 / (t + 2)

/-- **Farkas lemma.** In a finite-dimensional real normed space, a point outside the cone generated
by a finite set `G` is separated from it by a functional that is nonpositive on `G` and positive at
the point. -/
def FarkasLemma : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (G : Finset E)
    (x : E), x ∉ coneHull G → ∃ ψ : StrongDual ℝ E, (∀ g ∈ G, ψ g ≤ 0) ∧ 0 < ψ x

/-- **The minimal face of a point of a polytope.** For `y ∈ conv V` in a finite-dimensional real
normed space, the minimal face of `y` is an exposed face, its convex hull contains `y`, and every
vertex `v` of it can be pushed away from: `(1 + γ) y - γ v ∈ conv V` for some `γ > 0`. -/
def MinimalFace : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V : Finset E)
    (y : E), y ∈ convexHull ℝ (↑V : Set E) →
      (∃ Ψ : StrongDual ℝ E, (∀ u ∈ V, Ψ u ≤ Ψ y) ∧ minFace V y = exposedFace V Ψ) ∧
      y ∈ convexHull ℝ (↑(minFace V y) : Set E) ∧
      ∀ v ∈ minFace V y, ∃ γ : ℝ, 0 < γ ∧ (1 + γ) • y - γ • v ∈ convexHull ℝ (↑V : Set E)

end Lemmata.FrankWolfe
