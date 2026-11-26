module

public import Mathlib.Analysis.Normed.Lp.PiLp
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

/-- **Theorem 4.5** (Frank–Wolfe gap convergence). With the open-loop step sizes `2/(t+2)`, for
every `t ≥ 1` some iterate `x_τ` with `τ ≤ t` has Frank–Wolfe gap at most `6.75 L D² / (t + 2)`. -/
def GapRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (lmo : StrongDual ℝ E → E) (f : E → ℝ) (L : NNReal),
    StandingAssumptions C lmo f L →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ t : ℕ, 1 ≤ t → ∃ τ ≤ t,
      fwGap C (fderiv ℝ f) (fwIterates lmo (fderiv ℝ f) (openLoopStep 2) x₀ τ) ≤
        27 / 4 * L * Metric.diam C ^ 2 / (t + 2)

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

/-- **Lemma 4.11** (smoothness implies the adaptive test). If `f` is `L`-smooth and `x⁺` is the
short step from `x` toward `v` for the constant `L`, with `f'(x)(x - v) ≥ 0`, then the test of the
adaptive step-size strategy holds: `f'(x⁺)(x - v) ≥ 0`. -/
def SmoothImpliesAdaptiveTest : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal),
    IsSmooth f L → 0 < L → ∀ x v : E, 0 ≤ fderiv ℝ f x (x - v) →
      0 ≤ fderiv ℝ f (x + min (fderiv ℝ f x (x - v) / (L * ‖v - x‖ ^ 2)) 1 • (v - x)) (x - v)

/-- **Lemma 4.9** (smoothness revisited). For a convex `L`-smooth `f` with `L > 0`,
`(f'(y) - f'(x))(y - x)² / (2 L ‖y - x‖²) ≤ f y - f x - f'(x)(y - x)`. The paper assumes smoothness
and convexity only on a neighbourhood of the feasible region; here they hold on the whole space. -/
def SmoothnessRevisited : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal),
    ConvexOn ℝ Set.univ f → IsSmooth f L → 0 < L → ∀ x y : E,
      ((fderiv ℝ f y - fderiv ℝ f x) (y - x)) ^ 2 / (2 * L * ‖y - x‖ ^ 2) ≤
        f y - f x - fderiv ℝ f x (y - x)

/-- **Lemma 4.10** (primal progress from the adaptive test). Let `f` be convex and `L`-smooth, let
`γ = min {g/(M d²), 1}` with `g = f'(x)(x - v) ≥ 0`, `d = ‖v - x‖ > 0` and `M > 0`, let
`x⁺ = x + γ(v - x)`
and `a = f'(x⁺)(x - v) ≥ 0`. If `g/(M d²) ≤ 1`, then `f(x) - f(x⁺) ≥ (g² + a²)/(2 max{L, M} d²)`; if
`γ = 1` and `M ≥ L`, then `f(x) - f(x⁺) ≥ g/2 + a²/(2g)`. -/
def AdaptiveProgress : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L M : NNReal),
    ConvexOn ℝ Set.univ f → IsSmooth f L → 0 < L → 0 < M → ∀ (x v : E) (γ : ℝ),
      0 < ‖v - x‖ → 0 ≤ fderiv ℝ f x (x - v) →
      γ = min (fderiv ℝ f x (x - v) / (M * ‖v - x‖ ^ 2)) 1 →
      0 ≤ fderiv ℝ f (x + γ • (v - x)) (x - v) →
      (fderiv ℝ f x (x - v) / (M * ‖v - x‖ ^ 2) ≤ 1 →
        ((fderiv ℝ f x (x - v)) ^ 2 + (fderiv ℝ f (x + γ • (v - x)) (x - v)) ^ 2) /
            (2 * max L M * ‖v - x‖ ^ 2) ≤ f x - f (x + γ • (v - x))) ∧
      (γ = 1 → L ≤ M →
        fderiv ℝ f x (x - v) / 2 + (fderiv ℝ f (x + γ • (v - x)) (x - v)) ^ 2 /
            (2 * fderiv ℝ f x (x - v)) ≤ f x - f (x + γ • (v - x)))

/-- **Theorem 5.1** (approximate Carathéodory). Let `2 ≤ p < ∞` and let `V` be a compact set in
`ℓ_p^n`, with `ℓ_p`-diameter `D`. For every `x*` in the convex hull of `V` and every `ε > 0` there
are a set `S ⊆ V` of at most `⌈4 (p - 1) D² / ε²⌉ + 2` points and a point `x` in the convex hull
of `S` with
`‖x - x*‖_p ≤ ε`. The bound does not depend on the dimension `n`. -/
def ApproximateCaratheodory : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ V : Set (PiLp p (fun _ : Fin n => ℝ)), IsCompact V →
      ∀ xStar ∈ convexHull ℝ V, ∀ ε : ℝ, 0 < ε →
        ∃ S : Finset (PiLp p (fun _ : Fin n => ℝ)), (↑S : Set (PiLp p (fun _ : Fin n => ℝ))) ⊆ V ∧
          S.card ≤ ⌈4 * (p.toReal - 1) * Metric.diam V ^ 2 / ε ^ 2⌉₊ + 2 ∧
          ∃ x ∈ convexHull ℝ (↑S : Set (PiLp p (fun _ : Fin n => ℝ))), ‖x - xStar‖ ≤ ε

end Lemmata.FrankWolfeIntro
