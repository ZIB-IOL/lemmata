module

public import Lemmata.CGBasics.Statement
public import Lemmata.AwayStepFW.Statement

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

open Classical in
/-- A run of the lazy away-step Frank–Wolfe algorithm (Algorithm 3.8) on `conv V` with accuracy `K`
and short steps for `L`. In every iteration the weak separation oracle returns an away vertex
`a ∈ S_t` with `f'(x_t)(a - x_t) > φ_t/K`, followed by an away step, or a vertex `v ∈ V` with
`f'(x_t)(x_t - v) > φ_t/K`, followed by a Frank–Wolfe step, and `φ` stays; or it certifies
`f'(x_t)(u - x_t) ≤ φ_t` for all `u ∈ S_t` and `f'(x_t)(x_t - u) ≤ φ_t` for all `u ∈ V`, and then
the iterate stays and `φ` is halved. -/
def IsLazyAFWRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (L K : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (φ : ℕ → ℝ) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ lam 0 = (fun u => if u = x 0 then 1 else 0) ∧ ∀ t : ℕ,
    (∃ a ∈ S t, φ t / K < fderiv ℝ f (x t) (a - x t) ∧ ∃ γ : ℝ,
      γ = min (fderiv ℝ f (x t) (a - x t) / (L * ‖a - x t‖ ^ 2)) (lam t a / (1 - lam t a)) ∧
      x (t + 1) = x t - γ • (a - x t) ∧
      lam (t + 1) = (fun u => (1 + γ) * lam t u - if u = a then γ else 0) ∧
      S (t + 1) = (if γ = lam t a / (1 - lam t a) then (S t).erase a else S t) ∧ φ (t + 1) = φ t) ∨
    (∃ v ∈ V, φ t / K < fderiv ℝ f (x t) (x t - v) ∧ ∃ γ : ℝ,
      γ = min (fderiv ℝ f (x t) (x t - v) / (L * ‖x t - v‖ ^ 2)) 1 ∧
      x (t + 1) = x t - γ • (x t - v) ∧
      lam (t + 1) = (fun u => (1 - γ) * lam t u + if u = v then γ else 0) ∧
      S (t + 1) = (if γ = 1 then {v} else insert v (S t)) ∧ φ (t + 1) = φ t) ∨
    ((∀ u ∈ S t, fderiv ℝ f (x t) (u - x t) ≤ φ t) ∧ (∀ u ∈ V, fderiv ℝ f (x t) (x t - u) ≤ φ t) ∧
      x (t + 1) = x t ∧ S (t + 1) = S t ∧ lam (t + 1) = lam t ∧ φ (t + 1) = φ t / 2)

/-- **Theorem 3.16** (lazy away-step Frank–Wolfe), with a corrected count. Let `f` be convex,
`L`-smooth and `μ`-strongly convex on `conv V`, let `δ > 0` have the scaling property of the
pyramidal width, `K ≥ 1` and `h₀/2 ≤ φ₀ ≤ L D²/2`. Every run of Algorithm 3.8 has primal gap at most
`ε > 0` after `⌈log₂ (φ₀/ε)⌉₊ + 1 + 2 ⌈4 K² L D²/φ₀⌉₊ + 2 ⌈(16 K² L D²/(μ δ²)) ln (h₀/ε)⌉₊`
iterations. -/
def LazyAwayRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (μ δ K : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (φ : ℕ → ℝ),
    0 < (L : ℝ) → 0 < μ → 0 < δ → Lemmata.AwayStepFW.IsScaling V δ → ConvexOn ℝ Set.univ f →
    IsSmooth f L → (∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    1 ≤ K → IsLazyAFWRun V f L K x S lam φ →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f,
    (f (x 0) - f xStar) / 2 ≤ φ 0 → φ 0 ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 →
    ∀ ε : ℝ, 0 < ε → ∀ t : ℕ,
      ⌈Real.logb 2 (φ 0 / ε)⌉₊ + 1 + 2 * ⌈4 * K ^ 2 * L * Metric.diam (↑V : Set E) ^ 2 / φ 0⌉₊ +
        2 * ⌈16 * K ^ 2 * L * Metric.diam (↑V : Set E) ^ 2 / (μ * δ ^ 2) *
          Real.log ((f (x 0) - f xStar) / ε)⌉₊ ≤ t →
      f (x t) - f xStar ≤ ε

/-- **Sharpness** (Hölder error bound). A function `f` is `(c, θ)`-sharp over `C` if
`dist(x, Ω*) ≤ c (f(x) - f(x⋆))^θ` for all `x ∈ C` and minimizers `x⋆`, where `Ω*` is the set of
minimizers of `f` over `C`. -/
def IsSharp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (c θ : ℝ) : Prop :=
  ∀ x ∈ C, ∀ xStar ∈ minimizers C f, Metric.infDist x (minimizers C f) ≤ c * (f x - f xStar) ^ θ

/-- **Lemma 3.31** (primal gap bound from sharpness). Let `C` be compact and `f` convex,
differentiable and `(c, θ)`-sharp over `C`. For every `x ∈ C` with positive primal gap `h` there is
a minimizer `y` with `h^{1-θ}/c ≤ f'(x)(x - y)/‖x - y‖`. -/
def SharpPrimalGap : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (c θ : ℝ),
    IsCompact C → ConvexOn ℝ Set.univ f → Differentiable ℝ f → 0 < c → IsSharp C f c θ →
    ∀ xStar ∈ minimizers C f, ∀ x ∈ C, f xStar < f x →
      ∃ y ∈ minimizers C f, (f x - f xStar) ^ (1 - θ) / c ≤ fderiv ℝ f x (x - y) / ‖x - y‖

/-- **Lemma 3.32** (geometric sharpness). Let `f` be convex, differentiable and `(c, θ)`-sharp over
`conv V`, and let `δ > 0` have the scaling property of the pyramidal width. If `x ∈ conv S` for some
`S ⊆ V`, `a` maximizes `f'(x)` over `S` and `v` minimizes it over `V`, and the primal gap `h` at `x`
is positive, then `h^{1-θ}/c ≤ f'(x)(a - v)/δ`. -/
def GeometricSharpness : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (c θ δ : ℝ), ConvexOn ℝ Set.univ f → Differentiable ℝ f → 0 < c → 0 < δ →
    Lemmata.AwayStepFW.IsScaling V δ → IsSharp (convexHull ℝ (↑V : Set E)) f c θ →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ S ⊆ V,
    ∀ x ∈ convexHull ℝ (↑S : Set E),
    f xStar < f x → ∀ a ∈ S, (∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) →
    ∀ v ∈ V, (∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) →
      (f x - f xStar) ^ (1 - θ) / c ≤ fderiv ℝ f x (a - v) / δ

end Lemmata.CGImprovements
