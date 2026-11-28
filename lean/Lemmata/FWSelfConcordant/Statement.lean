module

public import Lemmata.FrankWolfe.Statement

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

end Lemmata.FWSelfConcordant
