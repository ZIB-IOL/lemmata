module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Lemmata.FrankWolfe.Polytope.Defs
public import Lemmata.FrankWolfe.HilbertDefs
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Convex.Strong

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

/-- **Runs stay feasible.** The iterates of a Frank–Wolfe run on a convex set stay in it. -/
def FWRunMem : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f' : E → StrongDual ℝ E)
    (x v : ℕ → E) (γ : ℕ → ℝ), Convex ℝ C → IsFWRun C f' x v γ → ∀ t, x t ∈ C

/-- **The iterates form a run.** For a linear minimization oracle and step sizes in `[0, 1]`, the
iterates `fwIterates` started in `C` form a Frank–Wolfe run, with atoms `lmo (f'(x_t))` and step
sizes `step t x_t`. -/
def FWIteratesIsRun : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (lmo : StrongDual ℝ E → E)
    (f' : E → StrongDual ℝ E) (step : ℕ → E → ℝ) (x₀ : E),
    IsLMO C lmo → (∀ t y, step t y ∈ Set.Icc (0 : ℝ) 1) → x₀ ∈ C →
      IsFWRun C f' (fwIterates lmo f' step x₀) (fun t => lmo (f' (fwIterates lmo f' step x₀ t)))
        (fun t => step t (fwIterates lmo f' step x₀ t))

/-- **Smoothness over a set.** An `L`-smooth function is `L`-smooth over every set. -/
def SmoothOnOfSmooth : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal),
    IsSmooth f L → IsSmoothOn C f L

/-- **Primal progress of a run.** In a Frank–Wolfe run on a convex `C` for an `f` that is
`L`-smooth over `C`, `f(x_{t+1}) ≤ f(x_t) - γ_t f'(x_t)(x_t - v_t) + γ_t² L/2 ‖v_t - x_t‖²`. -/
def RunProgress : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : ℝ)
    (x v : ℕ → E) (γ : ℕ → ℝ), Convex ℝ C → IsSmoothOn C f L → IsFWRun C (fderiv ℝ f) x v γ →
    ∀ t, f (x (t + 1)) ≤
      f (x t) - γ t * fderiv ℝ f (x t) (x t - v t) + γ t ^ 2 * L / 2 * ‖v t - x t‖ ^ 2

/-- **Scaling from a Hölderian error bound.** Let `C` be compact, and let `f` be convex over `C`,
differentiable at the points of `C` and `(μ, θ)`-sharp over `C`. Every `x ∈ C` with positive
primal gap `h = f(x) - f(x⋆)` has a nearest minimizer `y ≠ x` with
`h^{1-θ} ‖x - y‖ ≤ μ f'(x)(x - y)`; in particular `h^{1-θ} ≤ μ ‖f'(x)‖`. -/
def HEBScaling : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (μ θ : ℝ),
    IsCompact C → ConvexOn ℝ C f → (∀ x ∈ C, DifferentiableAt ℝ f x) →
    IsHolderErrorBound C f μ θ → ∀ xStar ∈ minimizers C f, ∀ x ∈ C, f xStar < f x →
      ∃ y ∈ minimizers C f, x ≠ y ∧ ‖x - y‖ = Metric.infDist x (minimizers C f) ∧
        (f x - f xStar) ^ (1 - θ) * ‖x - y‖ ≤ μ * fderiv ℝ f x (x - y) ∧
        (f x - f xStar) ^ (1 - θ) ≤ μ * ‖fderiv ℝ f x‖

/-- **First-order strong convexity.** If `f` is `μ`-strongly convex on `C` (in the sense of
Mathlib's `StrongConvexOn`) and differentiable at `x ∈ C`, then
`f(x) + f'(x)(y - x) + μ/2 ‖y - x‖² ≤ f(y)` for all `y ∈ C`. For `μ = 0` this is first-order
convexity on `C`. -/
def StrongConvexFirstOrder : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (μ : ℝ),
    StrongConvexOn C μ f → ∀ x ∈ C, DifferentiableAt ℝ f x → ∀ y ∈ C,
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

/-- **Quadratic growth and an error bound from strong convexity.** If `f` is `μ`-strongly convex
on `C` with `μ > 0`, then `μ/2 ‖x - x⋆‖² ≤ f(x) - f(x⋆)` for every minimizer `x⋆` and every
`x ∈ C`, and `f` satisfies a `(√(2/μ), 1/2)`-Hölderian error bound on `C`. -/
def StrongConvexHEB : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (μ : ℝ),
    StrongConvexOn C μ f → 0 < μ →
      (∀ xStar ∈ minimizers C f, ∀ x ∈ C, μ / 2 * ‖x - xStar‖ ^ 2 ≤ f x - f xStar) ∧
      IsHolderErrorBound C f (Real.sqrt (2 / μ)) (1 / 2)

end Lemmata.FrankWolfe
