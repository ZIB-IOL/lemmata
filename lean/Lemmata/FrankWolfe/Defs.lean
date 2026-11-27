module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Frank–Wolfe: the objects

The definitions shared by the Frank–Wolfe entries of the archive, for a feasible region `C` in a
real normed space `E`. Derivatives are continuous linear functionals: the derivative map of `f`
is `fderiv ℝ f : E → StrongDual ℝ E`, and a linear minimization oracle answers functionals.
`HilbertDefs.lean` has the same objects in the language of inner products and gradients.
-/

namespace Lemmata.FrankWolfe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `lmo` is a linear minimization oracle for `C`: for every continuous linear functional `g` it
returns a point of `C` that minimizes `g` over `C`. When there are several minimizers, `lmo` is
the rule that selects one of them; any rule is allowed, but it is fixed. -/
def IsLMO (C : Set E) (lmo : StrongDual ℝ E → E) : Prop :=
  ∀ g : StrongDual ℝ E, lmo g ∈ C ∧ ∀ y ∈ C, g (lmo g) ≤ g y

/-- One Frank–Wolfe step from `x` with step size `γ`: move toward the atom `lmo (f' x)` that the
oracle returns for the derivative `f' x`. -/
def fwStep (lmo : StrongDual ℝ E → E) (f' : E → StrongDual ℝ E) (x : E) (γ : ℝ) : E :=
  x + γ • (lmo (f' x) - x)

/-- The iterates `x₀, x₁, …` of the Frank–Wolfe algorithm started at `x₀`, where the step size in
iteration `t` at the current iterate `x` is `step t x`. -/
def fwIterates (lmo : StrongDual ℝ E → E) (f' : E → StrongDual ℝ E) (step : ℕ → E → ℝ)
    (x₀ : E) : ℕ → E
  | 0 => x₀
  | t + 1 => fwStep lmo f' (fwIterates lmo f' step x₀ t) (step t (fwIterates lmo f' step x₀ t))

/-- The open-loop step sizes `γ_t = ℓ/(t + ℓ)`; the classical rule is `ℓ = 2`. -/
noncomputable def openLoopStep (ℓ : ℝ) : ℕ → E → ℝ :=
  fun t _ => ℓ / ((t : ℝ) + ℓ)

/-- The short-step rule for smoothness constant `L`: with `v = lmo (f' x)`,
`γ = min {f' x (x - v) / (L ‖v - x‖²), 1}` (and `γ = 0` if `v = x`). -/
noncomputable def shortStep (lmo : StrongDual ℝ E → E) (f' : E → StrongDual ℝ E) (L : NNReal) :
    ℕ → E → ℝ :=
  fun _ x => min (f' x (x - lmo (f' x)) / ((L : ℝ) * ‖lmo (f' x) - x‖ ^ 2)) 1

/-- `σ` is an exact line-search rule: at every point `x` it selects a step size in `[0, 1]` that
minimizes `f` along the Frank–Wolfe segment from `x`, by a fixed rule among the minimizers. -/
def IsExactLineSearch (lmo : StrongDual ℝ E → E) (f : E → ℝ) (f' : E → StrongDual ℝ E)
    (σ : E → ℝ) : Prop :=
  ∀ x : E, σ x ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ γ ∈ Set.Icc (0 : ℝ) 1, f (fwStep lmo f' x (σ x)) ≤ f (fwStep lmo f' x γ)

/-- The Frank–Wolfe gap `max_{v ∈ C} f' x (x - v)` at `x`. -/
noncomputable def fwGap (C : Set E) (f' : E → StrongDual ℝ E) (x : E) : ℝ :=
  sSup ((fun v => f' x (x - v)) '' C)

/-- The minimizer set `argmin_{x ∈ C} f(x)`. -/
def minimizers (C : Set E) (f : E → ℝ) : Set E :=
  {x | x ∈ C ∧ ∀ y ∈ C, f x ≤ f y}

/-- `f` is `L`-smooth: differentiable, with `L`-Lipschitz derivative (in the operator norm). -/
def IsSmooth (f : E → ℝ) (L : NNReal) : Prop :=
  Differentiable ℝ f ∧ LipschitzWith L (fderiv ℝ f)

/-- The standing assumptions: `C` is compact and convex with linear minimization oracle `lmo`,
and `f` is convex and `L`-smooth with `L > 0`. -/
def StandingAssumptions (C : Set E) (lmo : StrongDual ℝ E → E) (f : E → ℝ) (L : NNReal) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ IsLMO C lmo ∧ ConvexOn ℝ Set.univ f ∧ IsSmooth f L ∧ 0 < L

/-- Power-type uniform convexity: `C` is `(α, q)`-uniformly convex if for all `x, y ∈ C`, every
`θ ∈ [0, 1]` and every unit vector `z`, `θ x + (1 - θ) y + θ (1 - θ) α ‖x - y‖^q z ∈ C`. -/
def IsUniformlyConvexSet (C : Set E) (α q : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ z : E, ‖z‖ = 1 →
    θ • x + (1 - θ) • y + (θ * (1 - θ) * α * ‖x - y‖ ^ q) • z ∈ C

/-- A Frank–Wolfe run on `C` for the derivative `f'`, with any tie-breaking: `x₀ ∈ C`, every atom
`v t ∈ C` minimizes `f'(x t)` over `C`, every step size `γ t` lies in `[0, 1]`, and
`x (t + 1) = x t + γ t • (v t - x t)`. Unlike `fwIterates`, which follows one fixed oracle, a run
may break ties differently in every iteration, and its step sizes are arbitrary. -/
def IsFWRun (C : Set E) (f' : E → StrongDual ℝ E) (x v : ℕ → E) (γ : ℕ → ℝ) : Prop :=
  x 0 ∈ C ∧ ∀ t, v t ∈ C ∧ (∀ y ∈ C, f' (x t) (v t) ≤ f' (x t) y) ∧ γ t ∈ Set.Icc (0 : ℝ) 1 ∧
    x (t + 1) = x t + γ t • (v t - x t)

/-- `f` is `L`-smooth over `C`: the quadratic upper bound
`f y ≤ f x + f'(x)(y - x) + L/2 ‖y - x‖²` holds for all `x, y ∈ C`. An `L`-smooth function
(`IsSmooth`) is `L`-smooth over every set; this weaker notion only constrains `f` on `C`. -/
def IsSmoothOn (C : Set E) (f : E → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, f y ≤ f x + fderiv ℝ f x (y - x) + L / 2 * ‖y - x‖ ^ 2

/-- `f` satisfies a `(μ, θ)`-Hölderian error bound on `C` (it is `(μ, θ)`-sharp): every `x ∈ C`
lies within distance `μ (f(x) - f(x⋆))^θ` of the set of minimizers of `f` over `C`. -/
def IsHolderErrorBound (C : Set E) (f : E → ℝ) (μ θ : ℝ) : Prop :=
  ∀ x ∈ C, ∀ xStar ∈ minimizers C f, Metric.infDist x (minimizers C f) ≤ μ * (f x - f xStar) ^ θ

end Lemmata.FrankWolfe
