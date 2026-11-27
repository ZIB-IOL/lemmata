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

/-- **Corollary 3.33** for `θ = 1/2` (away-step Frank–Wolfe under sharpness), with the constant
that the proof gives. If `f` is convex, `L`-smooth and `(c, 1/2)`-sharp over `conv V`, and `δ > 0`
has the scaling property of the pyramidal width, every run of away-step Frank–Wolfe satisfies
`f(x_t) - f(x⋆) ≤ (1 - min {1/2, δ²/(8 c² L D²)})^⌊(t-1)/2⌋ L D²/2` for `t ≥ 1`. -/
def SharpAwayLinear : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (c δ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ),
    0 < (L : ℝ) → 0 < c → 0 < δ → Lemmata.AwayStepFW.IsScaling V δ → ConvexOn ℝ Set.univ f →
    IsSmooth f L → IsSharp (convexHull ℝ (↑V : Set E)) f c (1 / 2) →
    Lemmata.AwayStepFW.IsAFWRun V f L x S lam →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤
        (1 - min (1 / 2) (δ ^ 2 / (8 * c ^ 2 * L * Metric.diam (↑V : Set E) ^ 2))) ^ ((t - 1) / 2) *
          (L * Metric.diam (↑V : Set E) ^ 2 / 2)

/-- **Corollary 3.33** for `θ < 1/2` (away-step Frank–Wolfe under sharpness), with the constant
that the proof gives. Under the assumptions of `SharpAwayLinear` with `(c, θ)`-sharpness for some
`0 ≤ θ < 1/2`, let `K = (4 c² L D²/δ²)^{1/(1-2θ)}` and `t₀ = max {⌊log₂ (L D²/K)⌋ + 1, 1}`, and for
`t ≥ 1` let `T = ⌊(t-1)/2⌋ + 1`. Then `f(x_t) - f(x⋆) ≤ L D²/2^T` if `T < t₀`, and
`f(x_t) - f(x⋆) ≤ K/(1 + (1/2 - θ)(T - t₀))^{1/(1-2θ)}` if `T ≥ t₀`. -/
def SharpAwaySublinear : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (c δ θ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ),
    0 < (L : ℝ) → 0 < c → 0 < δ → 0 ≤ θ → θ < 1 / 2 → Lemmata.AwayStepFW.IsScaling V δ →
    ConvexOn ℝ Set.univ f → IsSmooth f L → IsSharp (convexHull ℝ (↑V : Set E)) f c θ →
    Lemmata.AwayStepFW.IsAFWRun V f L x S lam →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f,
      let K := (4 * c ^ 2 * L * Metric.diam (↑V : Set E) ^ 2 / δ ^ 2) ^ (1 / (1 - 2 * θ))
      let t₀ : ℤ := max (⌊Real.logb 2 (L * Metric.diam (↑V : Set E) ^ 2 / K)⌋ + 1) 1
      ∀ t : ℕ, 1 ≤ t →
        (((t - 1) / 2 + 1 : ℕ) < t₀ →
          f (x t) - f xStar ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 ^ ((t - 1) / 2 + 1)) ∧
        (t₀ ≤ ((t - 1) / 2 + 1 : ℕ) → f (x t) - f xStar ≤
          K / (1 + (1 / 2 - θ) * ((((t - 1) / 2 + 1 : ℕ) : ℝ) - t₀)) ^ (1 / (1 - 2 * θ)))

/-- **Lemma 3.35**, first half (sharp functions are gradient dominated). Let `C` be compact and `f`
convex, differentiable and `(c, θ)`-sharp over `C` with `θ < 1`. Then
`(f(x) - f(x⋆))^{1-θ}/c ≤ ‖f'(x)‖` for every `x ∈ C`. -/
def SharpGradientDominated : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (c θ : ℝ),
    IsCompact C → ConvexOn ℝ Set.univ f → Differentiable ℝ f → 0 < c → θ < 1 →
    IsSharp C f c θ → ∀ xStar ∈ minimizers C f, ∀ x ∈ C,
      (f x - f xStar) ^ (1 - θ) / c ≤ ‖fderiv ℝ f x‖

/-- A run of Frank–Wolfe with the nearest extreme point oracle (Algorithm 3.12) on `conv V` in a
real inner product space: with `γ_t = 2/(t + 2)`, the vertex `v_t ∈ V` minimizes
`f'(x_t)(v) + L γ_t ‖x_t - v‖²/2` over `V`, and `x_{t+1} = x_t + γ_t (v_t - x_t)`. -/
def IsNEPRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V : Finset E)
    (f : E → ℝ) (L : ℝ) (x v : ℕ → E) : Prop :=
  x 0 ∈ V ∧ ∀ t : ℕ, v t ∈ V ∧
    (∀ u ∈ V, fderiv ℝ f (x t) (v t) + L * (2 / ((t : ℝ) + 2)) * ‖x t - v t‖ ^ 2 / 2 ≤
      fderiv ℝ f (x t) u + L * (2 / ((t : ℝ) + 2)) * ‖x t - u‖ ^ 2 / 2) ∧
    x (t + 1) = x t + (2 / ((t : ℝ) + 2)) • (v t - x t)

/-- **Theorem 3.36** (Frank–Wolfe with the nearest extreme point oracle). In a real inner product
space, let `f` be convex, `L`-smooth and `(c, θ)`-sharp over `conv V` with `0 < θ ≤ 1/2`, and let
`S⋆ ⊆ V` be a set of vertices whose convex hull contains all minimizers; let `D` and `D₀` be the
diameters of `V` and `S⋆`. Every run of Algorithm 3.12 satisfies, for `t ≥ 1`,
`f(x_t) - f(x⋆) ≤ L D²/(t(t+1)) + 2 L D₀²/(t+2) + 2^{2θ+1} L^{2θ+1} c² D^{4θ}/(t(t+1)) · R_t` with
`R_t = (t+2)^{1-2θ}/(1-2θ)` for `θ < 1/2` and `R_t = ln (t+2)` for `θ = 1/2`. -/
def NEPRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V Sstar : Finset E) (f : E → ℝ)
    (L : NNReal) (c θ : ℝ) (x v : ℕ → E),
    ConvexOn ℝ Set.univ f → IsSmooth f L → 0 < c → 0 < θ → θ ≤ 1 / 2 →
    IsSharp (convexHull ℝ (↑V : Set E)) f c θ → Sstar ⊆ V →
    minimizers (convexHull ℝ (↑V : Set E)) f ⊆ convexHull ℝ (↑Sstar : Set E) →
    IsNEPRun V f L x v → ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xStar ≤ L * Metric.diam (↑V : Set E) ^ 2 / (t * (t + 1)) +
        2 * L * Metric.diam (↑Sstar : Set E) ^ 2 / (t + 2) +
        2 ^ (2 * θ + 1) * (L : ℝ) ^ (2 * θ + 1) * c ^ 2 * Metric.diam (↑V : Set E) ^ (4 * θ) /
          (t * (t + 1)) *
          (if θ < 1 / 2 then ((t : ℝ) + 2) ^ (1 - 2 * θ) / (1 - 2 * θ) else Real.log ((t : ℝ) + 2))

open Classical in
/-- A run of blended conditional gradients (Algorithm 3.44) on `conv V` with accuracy `K`, short
steps for `L` and a simplex descent oracle (Oracle 3.43) with constant `L_S`. If some `a, s ∈ S_t`
have `f'(x_t)(a - s) ≥ φ_t`, the oracle returns `x_{t+1} ∈ conv S_{t+1}` with `S_{t+1} ⊆ S_t`, and
either drops a vertex without increasing `f`, or decreases `f` by at least
`max_{u, w ∈ S_t} f'(x_t)(u - w)²/(L_S |S_t|)`. Otherwise the weak separation oracle either returns
`v ∈ V` with `f'(x_t)(x_t - v) > φ_t/K`, followed by a Frank–Wolfe step toward `v` that does at
least as well as every `s ∈ [0, 1]` in the smoothness bound, or certifies `f'(x_t)(x_t - z) ≤ φ_t`
for all `z ∈ V`, and then `φ` is halved. -/
def IsBCGRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (L LS K : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (φ : ℕ → ℝ) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ ∀ t : ℕ, S t ⊆ V ∧ x t ∈ convexHull ℝ (↑(S t) : Set E) ∧
    (((∃ a ∈ S t, ∃ s ∈ S t, φ t ≤ fderiv ℝ f (x t) (a - s)) ∧ S (t + 1) ⊆ S t ∧
      ((f (x (t + 1)) ≤ f (x t) ∧ S (t + 1) ≠ S t) ∨
        ∀ u ∈ S t, ∀ w ∈ S t,
          fderiv ℝ f (x t) (u - w) ^ 2 ≤ LS * (S t).card * (f (x t) - f (x (t + 1)))) ∧
      φ (t + 1) = φ t) ∨
    ((∀ a ∈ S t, ∀ s ∈ S t, fderiv ℝ f (x t) (a - s) < φ t) ∧
      ((∃ v ∈ V, φ t / K < fderiv ℝ f (x t) (x t - v) ∧ ∃ γ ∈ Set.Icc (0 : ℝ) 1,
        x (t + 1) = x t + γ • (v - x t) ∧
        (∀ σ ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤
          f (x t) - σ * fderiv ℝ f (x t) (x t - v) + σ ^ 2 * L / 2 * ‖v - x t‖ ^ 2) ∧
        S (t + 1) = (if γ = 1 then {v} else insert v (S t)) ∧ φ (t + 1) = φ t) ∨
      ((∀ z ∈ V, fderiv ℝ f (x t) (x t - z) ≤ φ t) ∧ x (t + 1) = x t ∧ S (t + 1) = S t ∧
        φ (t + 1) = φ t / 2))))

/-- **Theorem 3.42** (blended conditional gradients), convex case with explicit constants. Let `f`
be convex and `L`-smooth on `conv V` with diameter `D`, `K ≥ 1`, `L_S > 0`, `h₀/2 ≤ φ₀ ≤ L D²/2`,
and let all active sets have at most `k` vertices. With `Q = max {8 K² L D², 4 L_S k}`, every run of
Algorithm 3.44 has primal gap at most `ε > 0` after `⌈log₂ (φ₀/ε)⌉₊ + 1 + 2 ⌈Q/ε⌉₊` iterations. -/
def BCGRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (LS K : ℝ) (k : ℕ) (x : ℕ → E) (S : ℕ → Finset E) (φ : ℕ → ℝ),
    ConvexOn ℝ Set.univ f → IsSmooth f L → 1 ≤ K → 0 < LS → IsBCGRun V f L LS K x S φ →
    (∀ t, (S t).card ≤ k) → ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f,
    (f (x 0) - f xStar) / 2 ≤ φ 0 → φ 0 ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 →
    ∀ ε : ℝ, 0 < ε → ∀ t : ℕ,
      ⌈Real.logb 2 (φ 0 / ε)⌉₊ + 1 +
          2 * ⌈max (8 * K ^ 2 * L * Metric.diam (↑V : Set E) ^ 2) (4 * LS * k) / ε⌉₊ ≤ t →
        f (x t) - f xStar ≤ ε

/-- **Theorem 3.42**, strongly convex case with explicit constants. Under the assumptions of
`BCGRate`, let `f` moreover be `μ`-strongly convex on `conv V` and let `δ > 0` have the scaling
property of the pyramidal width. With `Q = max {8 K² L D², 4 L_S k}`, every run of Algorithm 3.44
has primal gap at most `ε > 0` after
`⌈log₂ (φ₀/ε)⌉₊ + 1 + 2 ⌈Q/(2 φ₀)⌉₊ + 2 ⌈(2 Q/(μ δ²)) ln (h₀/ε)⌉₊` iterations. -/
def BCGLinearRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (μ δ LS K : ℝ) (k : ℕ) (x : ℕ → E) (S : ℕ → Finset E) (φ : ℕ → ℝ),
    0 < μ → 0 < δ → Lemmata.AwayStepFW.IsScaling V δ → ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    1 ≤ K → 0 < LS → IsBCGRun V f L LS K x S φ → (∀ t, (S t).card ≤ k) →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f,
    (f (x 0) - f xStar) / 2 ≤ φ 0 → φ 0 ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 →
    ∀ ε : ℝ, 0 < ε → ∀ t : ℕ,
      ⌈Real.logb 2 (φ 0 / ε)⌉₊ + 1 +
          2 * ⌈max (8 * K ^ 2 * L * Metric.diam (↑V : Set E) ^ 2) (4 * LS * k) / (2 * φ 0)⌉₊ +
          2 * ⌈2 * max (8 * K ^ 2 * L * Metric.diam (↑V : Set E) ^ 2) (4 * LS * k) /
              (μ * δ ^ 2) *
            Real.log ((f (x 0) - f xStar) / ε)⌉₊ ≤ t →
        f (x t) - f xStar ≤ ε

/-- **Lemma 3.45** (simplex descent). Let `h` be `L`-smooth on `ℝᵏ`, let
`d = ∇h(λ) - (⟨∇h(λ), 1⟩/k) 1` be the projection of the gradient onto the directions of the
probability simplex, let `γ ≥ 0`, and let `λ'` minimize `h` on the segment `[λ, λ - γ d]`. Then
either `h(λ - γ d) ≤ h(λ)`, or `h(λ) - h(λ') ≥ ⟨∇h(λ), e_i - e_j⟩²/(4L)` for all `i, j`. The book
takes `λ ∈ Δ_k` and `γ` maximal with `λ - γ d ≥ 0`; neither is needed. -/
def SimplexDescent : Prop :=
  ∀ (k : ℕ) (h : EuclideanSpace ℝ (Fin k) → ℝ) (L : NNReal) (lam d lam' : EuclideanSpace ℝ (Fin k))
    (γ : ℝ), IsSmooth h L → 0 ≤ γ →
    (∀ i, d i = fderiv ℝ h lam (EuclideanSpace.single i 1) -
      (∑ j, fderiv ℝ h lam (EuclideanSpace.single j 1)) / k) →
    lam' ∈ segment ℝ lam (lam - γ • d) → (∀ y ∈ segment ℝ lam (lam - γ • d), h lam' ≤ h y) →
    h (lam - γ • d) ≤ h lam ∨
      ∀ i j : Fin k, (fderiv ℝ h lam (EuclideanSpace.single i 1) -
        fderiv ℝ h lam (EuclideanSpace.single j 1)) ^ 2 / (4 * L) ≤ h lam - h lam'

end Lemmata.CGImprovements
