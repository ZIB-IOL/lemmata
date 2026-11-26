module

public import Lemmata.FrankWolfeBSS.Defs

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FrankWolfeBSS

open Lemmata.FrankWolfe

universe u

/-- **The primal-dual gap bounds the primal gap.** For a convex differentiable `f` and every
Frank–Wolfe run on `C`, `f(x_{t+1}) - f(y) ≤ G_t` for all `y ∈ C` and all `t`. -/
def GapBoundsPrimal : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (x v : ℕ → E) (γ : ℕ → ℝ),
    ConvexOn ℝ Set.univ f → Differentiable ℝ f → IsFWRun C (fderiv ℝ f) x v γ →
      ∀ y ∈ C, ∀ t, f (x (t + 1)) - f y ≤ pdGap f (fderiv ℝ f) x v γ t

/-- **Proposition 4.1, first part** (the primal-dual gap recursion). For every Frank–Wolfe run,
`G_{t+1} = (1 - γ) G_t - γ f'(x)(v - x) - f(x) + f(x + γ (v - x))` with `x = x_{t+1}`, `v = v_{t+1}`
and `γ = γ_{t+1}`. The paper states the inequality `≤`, which also covers the heavy-ball variant. -/
def GapRecursion : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (x v : ℕ → E) (γ : ℕ → ℝ),
    IsFWRun C (fderiv ℝ f) x v γ → ∀ t,
      pdGap f (fderiv ℝ f) x v γ (t + 1) =
        pdBound f (fderiv ℝ f) (pdGap f (fderiv ℝ f) x v γ t) (x (t + 1)) (v (t + 1)) (γ (t + 1))

/-- **Proposition 4.1, convexity.** For a convex `f`, the bound
`s ↦ (1 - s) G - s f'(x)(v - x) - f(x) + f(x + s (v - x))` is convex in the step size `s`, so a line
search on it is a one-dimensional convex problem. -/
def GapBoundConvex : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (f' : E → StrongDual ℝ E)
    (G : ℝ) (x v : E),
    ConvexOn ℝ Set.univ f → ConvexOn ℝ Set.univ (pdBound f f' G x v)

/-- **Proposition 4.1, rate.** Let `C` be compact and convex with diameter `D`, and `f` convex and
`L`-smooth. Take a Frank–Wolfe run with `γ₀ = 1` in which every later step `γ_{t+1}` is the
open-loop step `2/(t+3)`, or minimizes the smoothness bound `(1 - s) G_t + s² L/2 ‖v - x‖²` over
`[0, 1]` (the primal-dual short step), or minimizes the bound `(1 - s) G_t - s f'(x)(v - x) - f(x) +
f(x + s(v - x))` over `[0, 1]` (line search on the primal-dual gap); the rule may change between
iterations. Then `G_t ≤ 2 L D²/(t + 2)` for all `t`. The paper proves `4 L D²/(t + 2)` for the two
new rules. -/
def PrimalDualRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → IsSmooth f L →
    IsFWRun C (fderiv ℝ f) x v γ → γ 0 = 1 →
    (∀ t : ℕ,
      γ (t + 1) = 2 / ((t : ℝ) + 3) ∨
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        pdSmoothBound L (pdGap f (fderiv ℝ f) x v γ t) (x (t + 1)) (v (t + 1)) (γ (t + 1)) ≤
          pdSmoothBound L (pdGap f (fderiv ℝ f) x v γ t) (x (t + 1)) (v (t + 1)) s) ∨
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        pdBound f (fderiv ℝ f) (pdGap f (fderiv ℝ f) x v γ t) (x (t + 1)) (v (t + 1))
            (γ (t + 1)) ≤
          pdBound f (fderiv ℝ f) (pdGap f (fderiv ℝ f) x v γ t) (x (t + 1)) (v (t + 1)) s)) →
    ∀ t : ℕ, pdGap f (fderiv ℝ f) x v γ t ≤ 2 * L * Metric.diam C ^ 2 / ((t : ℝ) + 2)

/-- **Proposition 4.1, primal-dual short step.** With `L > 0`, `γ₀ = 1` and the primal-dual short
step `γ_{t+1} = min {1, G_t / (L ‖v_{t+1} - x_{t+1}‖²)}` (and `1` when `v_{t+1} = x_{t+1}`), the
primal-dual gap satisfies `G_t ≤ 2 L D²/(t + 2)`. -/
def PrimalDualShortStepRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → IsSmooth f L → 0 < L →
    IsFWRun C (fderiv ℝ f) x v γ → γ 0 = 1 →
    (∀ t : ℕ, γ (t + 1) = pdShortStep L (pdGap f (fderiv ℝ f) x v γ t) (x (t + 1)) (v (t + 1))) →
    ∀ t : ℕ, pdGap f (fderiv ℝ f) x v γ t ≤ 2 * L * Metric.diam C ^ 2 / ((t : ℝ) + 2)

end Lemmata.FrankWolfeBSS
