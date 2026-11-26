module

public import Lemmata.FrankWolfe.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Frank–Wolfe: the objects in a Hilbert space

The objects of `Defs.lean` in the language of inner products and gradients: the oracle answers
gradient vectors, and the steps use `∇ f`. The minimizer set and uniform convexity are the ones of
`Defs.lean`. `Hilbert.lean` relates the two languages.
-/

namespace Lemmata.FrankWolfe.Hilbert

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

end Lemmata.FrankWolfe.Hilbert
