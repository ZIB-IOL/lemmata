module

public import Lemmata.CGBasics.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

universe u

/-- The short step for the smoothness estimate `M`: `min {f'(x)(x - v)/(M ‖x - v‖²), 1}`. -/
noncomputable def adaStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (M : ℝ) (x v : E) : ℝ :=
  min (fderiv ℝ f x (x - v) / (M * ‖x - v‖ ^ 2)) 1

/-- The sufficient decrease test of Algorithm 3.4: the short step `γ` for the estimate `M`
satisfies `f(x + γ (v - x)) - f(x) ≤ γ f'(x)(v - x) + γ² M/2 ‖x - v‖²`. -/
def SufficientDecrease {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (M : ℝ) (x v : E) : Prop :=
  f (x + adaStep f M x v • (v - x)) - f x ≤
    adaStep f M x v * fderiv ℝ f x (v - x) + adaStep f M x v ^ 2 * M / 2 * ‖x - v‖ ^ 2

/-- **Smoothness passes the test.** If `f` is `L`-smooth and `M ≥ L`, the sufficient decrease
test holds at every `x` toward every `v`. -/
def SmoothPassesTest : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal) (M : ℝ),
    IsSmooth f L → (L : ℝ) ≤ M → ∀ x v : E, SufficientDecrease f M x v

/-- **Algorithm 3.4 terminates.** For an `L`-smooth `f`, a first estimate `M₀ = η L̃ > 0` and a
backtracking factor `τ > 1`, there is a first `k` for which `M₀ τ^k` passes the test; it satisfies
`k ≤ ⌈log_τ (L/M₀)⌉₊`, and the returned estimate is at most `max {M₀, τ L}`. -/
def AdaptiveStepTerminates : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal) (M₀ τ : ℝ)
    (x v : E), IsSmooth f L → 0 < M₀ → 1 < τ →
    ∃ k : ℕ, SufficientDecrease f (M₀ * τ ^ k) x v ∧
      (∀ j < k, ¬ SufficientDecrease f (M₀ * τ ^ j) x v) ∧
      k ≤ ⌈Real.logb τ (L / M₀)⌉₊ ∧ M₀ * τ ^ k ≤ max M₀ (τ * L)

/-- **Adaptive vanilla Frank–Wolfe** (Algorithm 3.5). Let `C` be compact and convex with diameter
`D`, and `f` convex and `L`-smooth with `L ≤ K`. If every step of a Frank–Wolfe run with exact
linear minimization is the short step for an estimate `0 < M_t ≤ K` that passes the test, then for
`t ≥ 1` the primal gap is at most `2 K D²/(t + 3)` and some Frank–Wolfe gap `g_τ` with `τ ≤ t` is
at most `4 K D²/(t + 3)`. -/
def AdaptiveRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L K : NNReal)
    (x v : ℕ → E) (M : ℕ → ℝ),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → IsSmooth f L → L ≤ K → x 0 ∈ C →
    (∀ t : ℕ, v t ∈ C ∧ (∀ y ∈ C, fderiv ℝ f (x t) (v t) ≤ fderiv ℝ f (x t) y) ∧ 0 < M t ∧
      M t ≤ K ∧ SufficientDecrease f (M t) (x t) (v t) ∧
      x (t + 1) = x t + adaStep f (M t) (x t) (v t) • (v t - x t)) →
    ∀ xStar ∈ minimizers C f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤ 2 * K * Metric.diam C ^ 2 / ((t : ℝ) + 3) ∧
        ∃ τ ≤ t, fderiv ℝ f (x τ) (x τ - v τ) ≤ 4 * K * Metric.diam C ^ 2 / ((t : ℝ) + 3)

end Lemmata.CGImprovements
