module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Lemmata.AwayStepFW.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWSelfConcordant

open Lemmata.FrankWolfe

universe u

/-- A run of **monotonic Frank–Wolfe** (Algorithm 1) on `C` for `f` with domain `D`: it starts at
`x₀ ∈ C ∩ D`, every `v_t ∈ C` is a Frank–Wolfe vertex for `f'(x_t)`, and the candidate
`x_t + (2/(t + 2))(v_t - x_t)` is accepted if it lies in `D` and does not increase `f`; otherwise
`x_{t+1} = x_t`. -/
def IsMFWRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E) (f : E → ℝ)
    (x v : ℕ → E) : Prop :=
  x 0 ∈ C ∧ x 0 ∈ D ∧ ∀ t : ℕ, v t ∈ C ∧ (∀ y ∈ C, fderiv ℝ f (x t) (v t) ≤ fderiv ℝ f (x t) y) ∧
    ((x t + (2 / ((t : ℝ) + 2)) • (v t - x t) ∈ D ∧
        f (x t + (2 / ((t : ℝ) + 2)) • (v t - x t)) ≤ f (x t)) →
      x (t + 1) = x t + (2 / ((t : ℝ) + 2)) • (v t - x t)) ∧
    (¬ (x t + (2 / ((t : ℝ) + 2)) • (v t - x t) ∈ D ∧
        f (x t + (2 / ((t : ℝ) + 2)) • (v t - x t)) ≤ f (x t)) → x (t + 1) = x t)

/-- The **local descent property** along Frank–Wolfe segments from the sublevel set of `x₀`: for
every `y ∈ C ∩ D` with `f(y) ≤ f(x₀)`, every `w ∈ C` and every `γ ∈ [0, γ̄]`, the point
`y + γ(w - y)` lies in `D` and `f(y + γ(w - y)) ≤ f(y) + γ f'(y)(w - y) + γ² K`. For an
`(M, ν)`-generalized self-concordant `f`, Proposition 2.1, Remark 2.2 and Lemma 2.3 give it with
`K = L D² ω_ν(1/2)` and `γ̄ = 2/(T_ν + 2)`. -/
def HasLocalDescent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E)
    (f : E → ℝ) (x₀ : E) (γbar K : ℝ) : Prop :=
  ∀ y ∈ C, y ∈ D → f y ≤ f x₀ → ∀ w ∈ C, ∀ γ ∈ Set.Icc (0 : ℝ) γbar,
    y + γ • (w - y) ∈ D ∧ f (y + γ • (w - y)) ≤ f y + γ * fderiv ℝ f y (w - y) + γ ^ 2 * K

/-- **Theorem 2.4** (primal gap of monotonic Frank–Wolfe). Let `C` and `D` be convex, `f` convex
and differentiable on `C ∩ D` with a minimizer `x⋆` there, and let `f` have the local descent
property with step bound `2/(T + 2)` and constant `K ≥ 0`. Every run of monotonic Frank–Wolfe
satisfies `f(x_t) - f(x⋆) ≤ 4 (T + 1)/(t + 1) max {f(x₀) - f(x⋆), K}` for all `t ≥ T`. -/
def MonotonicRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E) (f : E → ℝ)
    (x v : ℕ → E) (xStar : E) (K : ℝ) (T : ℕ),
    Convex ℝ C → Convex ℝ D → ConvexOn ℝ (C ∩ D) f → (∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) →
    xStar ∈ minimizers (C ∩ D) f → IsMFWRun C D f x v → 0 ≤ K →
    HasLocalDescent C D f (x 0) (2 / ((T : ℝ) + 2)) K →
    ∀ t : ℕ, T ≤ t →
      f (x t) - f xStar ≤ 4 * ((T : ℝ) + 1) / ((t : ℝ) + 1) * max (f (x 0) - f xStar) K

/-- **Theorem 2.6** (Frank–Wolfe gap of monotonic Frank–Wolfe). Under the assumptions of
`MonotonicRate` with `T ≥ 1`, for every `N ≥ T + 6` some iteration `1 ≤ t ≤ N` has Frank–Wolfe gap
`g_t = f'(x_t)(x_t - v_t)` at most
`18 N/(N - T) ((T + 1)/(2T + N - 3) + (2N - 2T + 3)/(2T + N)²) max {f(x₀) - f(x⋆), K}`. -/
def MonotonicGapRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E) (f : E → ℝ)
    (x v : ℕ → E) (xStar : E) (K : ℝ) (T : ℕ),
    Convex ℝ C → Convex ℝ D → ConvexOn ℝ (C ∩ D) f → (∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) →
    xStar ∈ minimizers (C ∩ D) f → IsMFWRun C D f x v → 0 ≤ K →
    HasLocalDescent C D f (x 0) (2 / ((T : ℝ) + 2)) K → 1 ≤ T →
    ∀ N : ℕ, T + 6 ≤ N →
      ∃ t, 1 ≤ t ∧ t ≤ N ∧ fderiv ℝ f (x t) (x t - v t) ≤
        18 * (N : ℝ) / ((N : ℝ) - T) * (((T : ℝ) + 1) / (2 * (T : ℝ) + N - 3) +
          (2 * (N : ℝ) - 2 * T + 3) / (2 * (T : ℝ) + N) ^ 2) * max (f (x 0) - f xStar) K

/-- A run of **Frank–Wolfe with backtracking** (Algorithm 2 with the line search of Algorithm 3) on
`C` for `f` with domain `D`: every `v_t ∈ C` is a Frank–Wolfe vertex, and the line search returns a
smoothness estimate `0 < L_t ≤ L̃` and the step `γ_t = min {1, g_t/(L_t ‖v_t - x_t‖²)}` with
`x_{t+1} = x_t + γ_t (v_t - x_t) ∈ D` and the sufficient decrease
`f(x_{t+1}) ≤ f(x_t) - γ_t g_t + L_t γ_t²/2 ‖v_t - x_t‖²`, where `g_t = f'(x_t)(x_t - v_t)`. -/
def IsBFWRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E) (f : E → ℝ)
    (Lmax : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ) : Prop :=
  x 0 ∈ C ∧ x 0 ∈ D ∧ ∀ t : ℕ, v t ∈ C ∧ (∀ y ∈ C, fderiv ℝ f (x t) (v t) ≤ fderiv ℝ f (x t) y) ∧
    x (t + 1) = x t + γ t • (v t - x t) ∧ x (t + 1) ∈ D ∧
    ∃ L : ℝ, 0 < L ∧ L ≤ Lmax ∧
      γ t = min 1 (fderiv ℝ f (x t) (x t - v t) / (L * ‖v t - x t‖ ^ 2)) ∧
      f (x (t + 1)) ≤ f (x t) - γ t * fderiv ℝ f (x t) (x t - v t) +
        L * γ t ^ 2 / 2 * ‖v t - x t‖ ^ 2

/-- **Theorem 2.11** (minimizer in the interior). Let `C` be compact and convex with diameter `D`,
`f` convex and differentiable on `C ∩ dom f` with a minimizer `x⋆` there, `μ`-strongly convex on
the sublevel set of `x₀` (for pairs of points in it), and let the closed ball of radius `r > 0`
around `x⋆` lie in `C`. Every run of Frank–Wolfe with backtracking and estimates at most `L̃`
satisfies `f(x_t) - f(x⋆) ≤ (1 - min {1, μ r²/(L̃ D²)}/2)^t (f(x₀) - f(x⋆))`. -/
def InteriorLinearRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E) (f : E → ℝ)
    (Lmax μ r : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ) (xStar : E),
    IsCompact C → Convex ℝ C → ConvexOn ℝ (C ∩ D) f → (∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) →
    xStar ∈ minimizers (C ∩ D) f → 0 < Lmax → 0 < μ → 0 < r → Metric.closedBall xStar r ⊆ C →
    (∀ y ∈ C ∩ D, f y ≤ f (x 0) → ∀ z ∈ C ∩ D, f z ≤ f (x 0) →
      f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z) →
    IsBFWRun C D f Lmax x v γ →
    ∀ t : ℕ, f (x t) - f xStar ≤
      (1 - 1 / 2 * min 1 (μ * r ^ 2 / (Lmax * Metric.diam C ^ 2))) ^ t * (f (x 0) - f xStar)

/-- **Theorem 2.15** (uniformly convex sets, gradients bounded away from zero). Let `C` be compact,
convex and `(κ, q)`-uniformly convex with `q ≥ 2`, and `f` convex and differentiable on `C ∩ dom f`
with a minimizer `x⋆` there and `‖f'(y)‖ ≥ c > 0` on `C ∩ dom f`. Every run of Frank–Wolfe with
backtracking and estimates at most `L̃` satisfies, with `h_t = f(x_t) - f(x⋆)`:
for `q = 2`, `h_t ≤ (1 - min {1, κ c/L̃}/2)^t h₀`; for `q > 2`, with
`τ = (L̃^q/(κ c)²)^{1/(q-2)}` and `t₀ = max {⌊log_{1/2}(τ/h₀)⌋ + 2, 1}`,
`h_t ≤ h₀ (1/2)^{t-1}` for `1 ≤ t < t₀` and `h_t ≤ τ/(1 + (q-2)(t - t₀)/(2q))^{q/(q-2)}` for
`t ≥ t₀`. -/
def UniformlyConvexGradientRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E) (f : E → ℝ)
    (Lmax κ q c : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ) (xStar : E),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C κ q → 0 < κ → 2 ≤ q →
    ConvexOn ℝ (C ∩ D) f → (∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) →
    xStar ∈ minimizers (C ∩ D) f → 0 < Lmax → 0 < c → (∀ y ∈ C ∩ D, c ≤ ‖fderiv ℝ f y‖) →
    IsBFWRun C D f Lmax x v γ →
    (q = 2 → ∀ t : ℕ, f (x t) - f xStar ≤
      (1 - 1 / 2 * min 1 (κ * c / Lmax)) ^ t * (f (x 0) - f xStar)) ∧
    (2 < q →
      let τ := (Lmax ^ q / (κ * c) ^ 2) ^ (1 / (q - 2))
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) (τ / (f (x 0) - f xStar))⌋ + 2) 1
      ∀ t : ℕ, 1 ≤ t →
        ((t : ℤ) < t₀ → f (x t) - f xStar ≤ (f (x 0) - f xStar) * (1 / 2) ^ (t - 1)) ∧
        (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
          τ / (1 + (q - 2) / (2 * q) * ((t : ℝ) - (t₀ : ℝ))) ^ (q / (q - 2))))

/-- **Theorem 2.16** (uniformly convex sets, local strong convexity). Let `C` be compact, convex
and `(κ, q)`-uniformly convex with `q ≥ 2`, and `f` convex and differentiable on `C ∩ dom f` with
a minimizer `x⋆` there and `μ`-strongly convex on the sublevel set of `x₀`. Every run of
Frank–Wolfe with backtracking and estimates at most `L̃` satisfies, with
`τ = (L̃^q/(κ² μ))^{1/(q-1)}` and `t₀ = max {⌊log_{1/2}(τ/h₀)⌋ + 2, 1}`,
`h_t ≤ h₀ (1/2)^{t-1}` for `1 ≤ t < t₀` and `h_t ≤ τ/(1 + (q-1)(t - t₀)/(2q))^{q/(q-1)}` for
`t ≥ t₀`. -/
def UniformlyConvexStrongRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C D : Set E) (f : E → ℝ)
    (Lmax κ q μ : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ) (xStar : E),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C κ q → 0 < κ → 2 ≤ q →
    ConvexOn ℝ (C ∩ D) f → (∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) →
    xStar ∈ minimizers (C ∩ D) f → 0 < Lmax → 0 < μ →
    (∀ y ∈ C ∩ D, f y ≤ f (x 0) → ∀ z ∈ C ∩ D, f z ≤ f (x 0) →
      f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z) →
    IsBFWRun C D f Lmax x v γ →
    let τ := (Lmax ^ q / (κ ^ 2 * μ)) ^ (1 / (q - 1))
    let t₀ : ℤ := max (⌊Real.logb (1 / 2) (τ / (f (x 0) - f xStar))⌋ + 2) 1
    ∀ t : ℕ, 1 ≤ t →
      ((t : ℤ) < t₀ → f (x t) - f xStar ≤ (f (x 0) - f xStar) * (1 / 2) ^ (t - 1)) ∧
      (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
        τ / (1 + (q - 1) / (2 * q) * ((t : ℝ) - (t₀ : ℝ))) ^ (q / (q - 1)))

open Classical in
/-- A run of **away-step Frank–Wolfe with backtracking** (Algorithm 4) on `conv V` for `f` with
domain `D`: it starts at a vertex in `D` with active set `{x₀}` and weight `1`, and every step is
an away-step Frank–Wolfe step (`AwayStepFW.IsAFWStep`, with any Frank–Wolfe vertex and any away
vertex) whose smoothness estimate `L_t ∈ (0, L̃]` comes from the line search: the new iterate lies
in `D` and satisfies the sufficient decrease condition. -/
def IsBAFWRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (D : Set E)
    (f : E → ℝ) (Lmax : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) : Prop :=
  x 0 ∈ V ∧ x 0 ∈ D ∧ S 0 = {x 0} ∧ lam 0 = (fun w => if w = x 0 then 1 else 0) ∧
    ∀ t : ℕ, ∃ L : ℝ, 0 < L ∧ L ≤ Lmax ∧
      ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
      ∃ a ∈ S t, (∀ w ∈ S t, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) a) ∧
        AwayStepFW.IsAFWStep L (fderiv ℝ f (x t)) (x t) (S t) (lam t) v a (x (t + 1)) (S (t + 1))
          (lam (t + 1)) ∧
        x (t + 1) ∈ D ∧
        f (x (t + 1)) ≤ f (x t) + fderiv ℝ f (x t) (x (t + 1) - x t) +
          L / 2 * ‖x (t + 1) - x t‖ ^ 2

/-- **Theorem 3.2** (away-step Frank–Wolfe). Let `x⋆` minimize `f` on `conv V ∩ dom f`, let `f` be
`μ`-strongly convex on the sublevel set of `x₀` (for pairs of points in it), and let `δ > 0` have
the scaling property of the pyramidal width of `conv V`, whose diameter is `D`. Every run of
away-step Frank–Wolfe with backtracking and estimates at most `L̃` satisfies
`f(x_t) - f(x⋆) ≤ (1 - min {1/2, μ δ²/(4 L̃ D²)})^⌈(t-1)/2⌉ (f(x₀) - f(x⋆))`. -/
def AwayLinearRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (D : Set E) (f : E → ℝ)
    (Lmax μ δ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (xStar : E),
    xStar ∈ minimizers (convexHull ℝ (↑V : Set E) ∩ D) f → 0 < Lmax → 0 < μ → 0 < δ →
    AwayStepFW.IsScaling V δ →
    (∀ y ∈ convexHull ℝ (↑V : Set E) ∩ D, f y ≤ f (x 0) →
      ∀ z ∈ convexHull ℝ (↑V : Set E) ∩ D, f z ≤ f (x 0) →
        f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z) →
    IsBAFWRun V D f Lmax x S lam →
    ∀ t : ℕ, f (x t) - f xStar ≤
      (1 - min (1 / 2) (μ * δ ^ 2 / (4 * Lmax * Metric.diam (↑V : Set E) ^ 2))) ^
        ⌈((t : ℝ) - 1) / 2⌉₊ * (f (x 0) - f xStar)

end Lemmata.FWSelfConcordant
