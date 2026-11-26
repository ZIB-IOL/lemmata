module

public import Lemmata.FrankWolfe.Defs

@[expose] public section

/-!
# Frank–Wolfe runs and the primal-dual gap

A Frank–Wolfe run is given by its iterates `x`, oracle answers `v` and step sizes `γ`, as sequences
satisfying the algorithm's rules, so that every tie-breaking rule of the oracle and every step-size
rule (including rules that depend on the whole history) is covered.

The primal-dual gap of Martínez-Rubio and Pokutta is `G_t = f(x_{t+1}) - L_t`, where the lower bound
`L_t` on the optimal value is the weighted average of the Frank–Wolfe lower bounds
`f(x_ℓ) - g_ℓ`, `g_ℓ = f'(x_ℓ)(x_ℓ - v_ℓ)`, with weights `a_ℓ / A_t` and `γ_t = a_t / A_t`.
-/

namespace Lemmata.FrankWolfeBSS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Frank–Wolfe run on `C` for the derivative `f'`: `x₀ ∈ C`, every `v t` minimizes `f'(x t)` over
`C`, every step size lies in `[0, 1]`, and `x (t + 1) = x t + γ t • (v t - x t)`. -/
def IsFWRun (C : Set E) (f' : E → StrongDual ℝ E) (x v : ℕ → E) (γ : ℕ → ℝ) : Prop :=
  x 0 ∈ C ∧ ∀ t, v t ∈ C ∧ (∀ y ∈ C, f' (x t) (v t) ≤ f' (x t) y) ∧ γ t ∈ Set.Icc (0 : ℝ) 1 ∧
    x (t + 1) = x t + γ t • (v t - x t)

/-- The lower bounds `L_t` of the primal-dual analysis: `L₀ = f(x₀) - g₀` and
`L_{t+1} = (1 - γ_{t+1}) L_t + γ_{t+1} (f(x_{t+1}) - g_{t+1})`, with the Frank–Wolfe gaps
`g_t = f'(x_t)(x_t - v_t)`. -/
noncomputable def pdLower (f : E → ℝ) (f' : E → StrongDual ℝ E) (x v : ℕ → E) (γ : ℕ → ℝ) :
    ℕ → ℝ
  | 0 => f (x 0) - f' (x 0) (x 0 - v 0)
  | t + 1 => (1 - γ (t + 1)) * pdLower f f' x v γ t +
      γ (t + 1) * (f (x (t + 1)) - f' (x (t + 1)) (x (t + 1) - v (t + 1)))

/-- The primal-dual gap `G_t = f(x_{t+1}) - L_t`. -/
noncomputable def pdGap (f : E → ℝ) (f' : E → StrongDual ℝ E) (x v : ℕ → E) (γ : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  f (x (t + 1)) - pdLower f f' x v γ t

/-- The bound `(1 - s) G - s f'(x)(v - x) - f(x) + f(x + s (v - x))` on the next primal-dual gap,
as a function of the step size `s`, before smoothness is used. -/
noncomputable def pdBound (f : E → ℝ) (f' : E → StrongDual ℝ E) (G : ℝ) (x v : E) (s : ℝ) : ℝ :=
  (1 - s) * G - s * f' x (v - x) - f x + f (x + s • (v - x))

/-- The bound `(1 - s) G + s² L/2 ‖v - x‖²` on the next primal-dual gap given by smoothness. -/
noncomputable def pdSmoothBound (L G : ℝ) (x v : E) (s : ℝ) : ℝ :=
  (1 - s) * G + s ^ 2 * (L / 2) * ‖v - x‖ ^ 2

open Classical in
/-- The primal-dual short step `min {1, G / (L ‖v - x‖²)}`, and `1` when `v = x`: the minimizer of
`pdSmoothBound L G x v` over `[0, 1]` when `G ≥ 0` and `L > 0`. -/
noncomputable def pdShortStep (L G : ℝ) (x v : E) : ℝ :=
  if v = x then 1 else min 1 (G / (L * ‖v - x‖ ^ 2))

/-- The averaged derivative of heavy-ball Frank–Wolfe: `ḡ₀ = f'(x₀)` and
`ḡ_{t+1} = (1 - γ_{t+1}) ḡ_t + γ_{t+1} f'(x_{t+1})`, that is `(1/A_t) ∑_{ℓ ≤ t} a_ℓ f'(x_ℓ)`. -/
noncomputable def hbDir (f' : E → StrongDual ℝ E) (x : ℕ → E) (γ : ℕ → ℝ) : ℕ → StrongDual ℝ E
  | 0 => f' (x 0)
  | t + 1 => (1 - γ (t + 1)) • hbDir f' x γ t + γ (t + 1) • f' (x (t + 1))

/-- The averaged constant term of heavy-ball Frank–Wolfe: `c₀ = f(x₀) - f'(x₀)(x₀)` and
`c_{t+1} = (1 - γ_{t+1}) c_t + γ_{t+1} (f(x_{t+1}) - f'(x_{t+1})(x_{t+1}))`, so that
`c_t + ḡ_t(y)` is the average of the linear models `f(x_ℓ) + f'(x_ℓ)(y - x_ℓ)`. -/
noncomputable def hbConst (f : E → ℝ) (f' : E → StrongDual ℝ E) (x : ℕ → E) (γ : ℕ → ℝ) :
    ℕ → ℝ
  | 0 => f (x 0) - f' (x 0) (x 0)
  | t + 1 => (1 - γ (t + 1)) * hbConst f f' x γ t +
      γ (t + 1) * (f (x (t + 1)) - f' (x (t + 1)) (x (t + 1)))

/-- A heavy-ball Frank–Wolfe run on `C`: as a Frank–Wolfe run, except that every `v t` minimizes
the averaged derivative `hbDir f' x γ t` over `C`. -/
def IsHBRun (C : Set E) (f' : E → StrongDual ℝ E) (x v : ℕ → E) (γ : ℕ → ℝ) : Prop :=
  x 0 ∈ C ∧ ∀ t, v t ∈ C ∧ (∀ y ∈ C, hbDir f' x γ t (v t) ≤ hbDir f' x γ t y) ∧
    γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t)

/-- The primal-dual gap of heavy-ball Frank–Wolfe: `G_t = f(x_{t+1}) - L_t` with the lower bound
`L_t = c_t + ḡ_t(v_t) = min_{y ∈ C} (c_t + ḡ_t(y))`. -/
noncomputable def hbGap (f : E → ℝ) (f' : E → StrongDual ℝ E) (x v : ℕ → E) (γ : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  f (x (t + 1)) - (hbConst f f' x γ t + hbDir f' x γ t (v t))

end Lemmata.FrankWolfeBSS
