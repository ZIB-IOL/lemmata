module

public import Lemmata.FrankWolfe.Statement

@[expose] public section

/-!
# The Frank–Wolfe algorithm: a short introduction — statements

The results of *The Frank–Wolfe algorithm: a short introduction* (arXiv:2311.05313) that this
entry adds to the core (`Lemmata.FrankWolfe`), in the paper's numbering. Lemmas 4.1 and 4.3 and
Theorem 4.4 are the core's statements `GapInequalities`, `ProgressLemma` and `StandardRate`.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

universe u

/-- **Lemma 4.2** (first-order optimality). For a convex differentiable `f` on a compact convex
`C`, a point `x⋆ ∈ C` is a minimizer if and only if `f'(x⋆)(x⋆ - v) ≤ 0` for all `v ∈ C`; at a
minimizer the Frank–Wolfe gap is `0`. -/
def FirstOrderOptimality : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → Differentiable ℝ f → ∀ xStar ∈ C,
      (xStar ∈ minimizers C f ↔ ∀ v ∈ C, fderiv ℝ f xStar (xStar - v) ≤ 0) ∧
      (xStar ∈ minimizers C f → fwGap C (fderiv ℝ f) xStar = 0)

/-- **Proposition 4.6** (a lower bound for any step sizes). For step sizes `γ_τ ∈ [0, 1]`,
`f(x_t) - f(x⋆) ≥ ∏_{τ=1}^{t-1} (1 - γ_τ) · f'(x⋆)(x₁ - x⋆)` for every `t ≥ 1`. -/
def FixedLowerBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (lmo : StrongDual ℝ E → E) (f : E → ℝ) (L : NNReal),
    StandingAssumptions C lmo f L →
    ∀ step : ℕ → E → ℝ, (∀ t, ∀ x ∈ C, step t x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ t : ℕ, 1 ≤ t →
      (∏ τ ∈ Finset.Ico 1 t, (1 - step τ (fwIterates lmo (fderiv ℝ f) step x₀ τ))) *
          fderiv ℝ f xStar (fwIterates lmo (fderiv ℝ f) step x₀ 1 - xStar) ≤
        f (fwIterates lmo (fderiv ℝ f) step x₀ t) - f xStar

/-- **Proposition 4.6** for the open-loop rule `γ_t = 2/(t+2)`:
`f(x_t) - f(x⋆) ≥ 2/(t(t+1)) · f'(x⋆)(x₁ - x⋆)` for every `t ≥ 1`. -/
def FixedLowerBoundOpenLoop : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (lmo : StrongDual ℝ E → E) (f : E → ℝ) (L : NNReal),
    StandingAssumptions C lmo f L →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ t : ℕ, 1 ≤ t →
      2 / ((t : ℝ) * (t + 1)) *
          fderiv ℝ f xStar (fwIterates lmo (fderiv ℝ f) (openLoopStep 2) x₀ 1 - xStar) ≤
        f (fwIterates lmo (fderiv ℝ f) (openLoopStep 2) x₀ t) - f xStar

/-- **Theorem 4.7** (nonconvex objectives). For an `L`-smooth, not necessarily convex `f` and the
constant step size `γ = 1/√(T+1)`, some iterate `x_t` with `t ≤ T` has Frank–Wolfe gap at most
`max {2 h₀, L D²} / √(T+1)`, where `h₀ = f(x₀) - f(x⋆)`. -/
def NonconvexRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (lmo : StrongDual ℝ E → E) (f : E → ℝ) (L : NNReal),
    IsCompact C → Convex ℝ C → IsLMO C lmo → IsSmooth f L →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ T : ℕ, ∃ t ≤ T,
      fwGap C (fderiv ℝ f) (fwIterates lmo (fderiv ℝ f) (fun _ _ => 1 / Real.sqrt (T + 1)) x₀ t) ≤
        max (2 * (f x₀ - f xStar)) (L * Metric.diam C ^ 2) / Real.sqrt (T + 1)

end Lemmata.FrankWolfeIntro
