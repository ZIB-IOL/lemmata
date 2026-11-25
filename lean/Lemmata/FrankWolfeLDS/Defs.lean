module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Frank–Wolfe with local dual sharpness: the objects

The definitions that the statements in `Statement.lean` are about, in the order of the paper
(arXiv:2604.28006): the linear minimization oracle and the step-size rules of the Frank–Wolfe
algorithm, the standing assumptions, the minimizer set, power-type uniform convexity (Definition 2.4), local dual
sharpness (Definition 3.1) and the local Hölder error bound (Definition 4.1).

The space `E` is a real inner product space (the statements add completeness), `C ⊆ E` is the
feasible region, `f : E → ℝ` the objective, and `∇ f` is Mathlib's `gradient f`. The paper works
in `ℝ^d`; nothing here needs finite dimension.
-/

namespace Lemmata.FrankWolfeLDS

open scoped Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `lmo` is a linear minimization oracle for `C`: for every direction `g` it returns a point
of `C` that minimizes `⟪g, ·⟫` over `C`. When there are several minimizers, `lmo` is the rule
that selects one of them; any rule is allowed, but it is fixed. -/
def IsLinearMinimizationOracle (C : Set E) (lmo : E → E) : Prop :=
  ∀ g : E, lmo g ∈ C ∧ ∀ y ∈ C, ⟪g, lmo g⟫_ℝ ≤ ⟪g, y⟫_ℝ

section Gradient

variable [CompleteSpace E]

/-- One Frank–Wolfe step from `x` with step size `γ`: move from `x` toward the atom
`lmo (∇ f x)` that the oracle returns for the gradient. -/
noncomputable def fwStep (lmo : E → E) (f : E → ℝ) (x : E) (γ : ℝ) : E :=
  x + γ • (lmo (∇ f x) - x)

/-- The iterates `x₀, x₁, …` of the Frank–Wolfe algorithm started at `x₀`, where the step size
in iteration `t` at the current iterate `x` is `step t x`. -/
noncomputable def fwIterates (lmo : E → E) (f : E → ℝ) (step : ℕ → E → ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | t + 1 => fwStep lmo f (fwIterates lmo f step x₀ t) (step t (fwIterates lmo f step x₀ t))

/-- The classical open-loop step-size rule `γ_t = 2/(t+2)`. -/
noncomputable def openLoopStep : ℕ → E → ℝ :=
  fun t _ => 2 / ((t : ℝ) + 2)

/-- The short-step rule for smoothness constant `L`: with `v = lmo (∇ f x)`,
`γ = min {⟪∇ f x, x - v⟫ / (L ‖v - x‖²), 1}` (and `γ = 0` if `v = x`). -/
noncomputable def shortStep (lmo : E → E) (f : E → ℝ) (L : NNReal) : ℕ → E → ℝ :=
  fun _ x => min (⟪∇ f x, x - lmo (∇ f x)⟫_ℝ / ((L : ℝ) * ‖lmo (∇ f x) - x‖ ^ 2)) 1

/-- The standing assumptions of the paper: the feasible region `C` is compact and convex and
`lmo` is a linear minimization oracle for it; the objective `f` is convex and differentiable,
and `L`-smooth with `L > 0`, that is, its gradient `∇ f` is `L`-Lipschitz. -/
def StandingAssumptions (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal) : Prop :=
  IsCompact C ∧ Convex ℝ C ∧ IsLinearMinimizationOracle C lmo ∧
    Differentiable ℝ f ∧ ConvexOn ℝ Set.univ f ∧ LipschitzWith L (∇ f) ∧ 0 < L

/-- `σ` is an exact line-search rule: at every point `x` it selects a step size in `[0, 1]`
that minimizes `f` along the Frank–Wolfe segment from `x`. When there are several minimizers,
`σ` is the rule that selects one of them; any rule is allowed. -/
def IsExactLineSearch (lmo : E → E) (f : E → ℝ) (σ : E → ℝ) : Prop :=
  ∀ x : E, σ x ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ γ ∈ Set.Icc (0 : ℝ) 1, f (fwStep lmo f x (σ x)) ≤ f (fwStep lmo f x γ)

end Gradient

/-- The minimizer set `𝓜 = argmin_{x ∈ C} f(x)`. -/
def minimizers (C : Set E) (f : E → ℝ) : Set E :=
  {x | x ∈ C ∧ ∀ y ∈ C, f x ≤ f y}

/-- Power-type uniform convexity (Definition 2.4): `C` is `(α, q)`-uniformly convex if for all
`x, y ∈ C`, every `θ ∈ [0, 1]` and every unit vector `z`,
`θ x + (1 - θ) y + θ (1 - θ) α ‖x - y‖^q z ∈ C`. -/
def IsUniformlyConvexSet (C : Set E) (α q : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ z : E, ‖z‖ = 1 →
    θ • x + (1 - θ) • y + (θ * (1 - θ) * α * ‖x - y‖ ^ q) • z ∈ C

/-- Local dual sharpness around `M` with constants `(A, q)` (Definition 3.1), for the
feasible region `C` together with its oracle `lmo`: there is `ρ > 0` such that every `x ∈ C`
with `dist(x, M) < ρ` satisfies `A ‖g‖ ‖x - s‖^q ≤ ⟪g, x - s⟫` for every direction `g` and the
atom `s = lmo g` selected by the oracle. -/
def LocalDualSharpness (C : Set E) (lmo : E → E) (M : Set E) (A q : ℝ) : Prop :=
  ∃ ρ > 0, ∀ x ∈ C, Metric.infDist x M < ρ →
    ∀ g : E, A * ‖g‖ * ‖x - lmo g‖ ^ q ≤ ⟪g, x - lmo g⟫_ℝ

/-- A local Hölder error bound of order `r` with constant `B` (Definition 4.1), around `M`
and relative to the value `fStar`: there is `ρ > 0` such that every `x ∈ C` with
`dist(x, M) < ρ` satisfies `dist(x, M)^r ≤ B (f x - fStar)`. The statements use it with `M` the
minimizer set and `fStar` the optimal value. -/
def LocalHolderErrorBound (C : Set E) (f : E → ℝ) (M : Set E) (fStar B r : ℝ) : Prop :=
  ∃ ρ > 0, ∀ x ∈ C, Metric.infDist x M < ρ → Metric.infDist x M ^ r ≤ B * (f x - fStar)

end Lemmata.FrankWolfeLDS
