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

/-- A run of the parameter-free lazy conditional gradient algorithm (Algorithm 3.7) with accuracy
`K`. In every iteration the weak separation oracle either returns `v ∈ C` with
`f'(x_t)(x_t - v) > φ_t/K`, and the step toward `v` does at least as well as every `s ∈ [0, 1]` in
the smoothness bound, or it certifies `f'(x_t)(x_t - z) ≤ φ_t` for all `z ∈ C`; then the iterate
stays and `φ` is halved. -/
def IsLCGRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (L : NNReal) (K : ℝ) (x : ℕ → E) (φ : ℕ → ℝ) : Prop :=
  x 0 ∈ C ∧ ∀ t : ℕ,
    (∃ v ∈ C, φ t / K < fderiv ℝ f (x t) (x t - v) ∧ ∃ γ ∈ Set.Icc (0 : ℝ) 1,
      x (t + 1) = x t + γ • (v - x t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤
        f (x t) - s * fderiv ℝ f (x t) (x t - v) + s ^ 2 * L / 2 * ‖v - x t‖ ^ 2) ∧
      φ (t + 1) = φ t) ∨
    ((∀ z ∈ C, fderiv ℝ f (x t) (x t - z) ≤ φ t) ∧ x (t + 1) = x t ∧ φ (t + 1) = φ t / 2)

/-- **Theorem 3.15** (lazy conditional gradients). Let `C` be compact and convex with diameter
`D`, `f` convex and `L`-smooth, `K ≥ 1` and `h₀/2 ≤ φ₀ ≤ L D²/2`. Every run of Algorithm 3.7 has
primal gap at most `ε > 0` after `⌈log₂ (φ₀/ε)⌉₊ + ⌈8 K² L D²/ε⌉₊` iterations. -/
def LazyRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (K : ℝ) (x : ℕ → E) (φ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → IsSmooth f L → 1 ≤ K →
    IsLCGRun C f L K x φ → ∀ xStar ∈ minimizers C f,
    (f (x 0) - f xStar) / 2 ≤ φ 0 → φ 0 ≤ L * Metric.diam C ^ 2 / 2 → ∀ ε : ℝ, 0 < ε →
    ∀ t : ℕ, ⌈Real.logb 2 (φ 0 / ε)⌉₊ + ⌈8 * K ^ 2 * L * Metric.diam C ^ 2 / ε⌉₊ ≤ t →
      f (x t) - f xStar ≤ ε

end Lemmata.CGImprovements
