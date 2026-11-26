module

public import Lemmata.FrankWolfe.Defs
public import Lemmata.FrankWolfe.Polytope.Defs

@[expose] public section

/-!
# Pyramidal width

The polytope is `P = conv V` for a finite set `V` in a real normed space. For a set `S ⊆ V`, a point
`x ∈ conv S` and a direction `ψ`, the *away vertex* `a ∈ S` maximizes `ψ` over `S` and the
*Frank–Wolfe vertex* `v ∈ V` minimizes `ψ` over `V`. The scaling property with constant `δ` asks
`ψ(a - v) ≥ δ ψ(x - y) / ‖x - y‖` for every `y ∈ P`; the pyramidal width is the largest such `δ`.
-/

namespace Lemmata.AwayStepFW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scaling property of `conv V` with constant `δ`, in the division-free form
`δ ψ(x - y) ≤ ψ(a - v) ‖x - y‖`. -/
def IsScaling (V : Finset E) (δ : ℝ) : Prop :=
  ∀ S ⊆ V, ∀ x ∈ convexHull ℝ (↑S : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
    ∀ ψ : StrongDual ℝ E, ∀ a ∈ S, (∀ w ∈ S, ψ w ≤ ψ a) → ∀ v ∈ V, (∀ w ∈ V, ψ v ≤ ψ w) →
      δ * ψ (x - y) ≤ ψ (a - v) * ‖x - y‖

/-- The pyramidal width of `conv V`: the supremum of the constants `δ ≥ 0` with the scaling
property (`0` if they are unbounded, which happens only for a single point). -/
noncomputable def pyramidalWidth (V : Finset E) : ℝ :=
  sSup {δ : ℝ | 0 ≤ δ ∧ IsScaling V δ}

open Classical in
/-- One step of away-step Frank–Wolfe (Algorithm 2.2 of the book) from the state `(x, S, λ)`, with
Frank–Wolfe vertex `v ∈ V` and away vertex `a ∈ S` for `g = f'(x)`, and smoothness constant `L`:
the Frank–Wolfe step when `g(x - v) ≥ g(a - x)`, otherwise the away step, each with the short step
clipped at its maximal step size; the weights and the active set are updated as in the book. -/
def IsAFWStep (L : ℝ) (g : StrongDual ℝ E) (x : E) (S : Finset E) (lam : E → ℝ) (v a : E)
    (x' : E) (S' : Finset E) (lam' : E → ℝ) : Prop :=
  if g (a - x) ≤ g (x - v) then
    let γ := min (g (x - v) / (L * ‖x - v‖ ^ 2)) 1
    x' = x - γ • (x - v) ∧ lam' = (fun w => (1 - γ) * lam w + if w = v then γ else 0) ∧
      S' = if γ = 1 then {v} else insert v S
  else
    let γmax := lam a / (1 - lam a)
    let γ := min (g (a - x) / (L * ‖a - x‖ ^ 2)) γmax
    x' = x - γ • (a - x) ∧ lam' = (fun w => (1 + γ) * lam w - if w = a then γ else 0) ∧
      S' = if γ = γmax then S.erase a else S

open Classical in
/-- A run of away-step Frank–Wolfe on `conv V` for `f` with smoothness constant `L`: it starts at a
vertex with active set `{x₀}` and weight `1`, and every step is an away-step Frank–Wolfe step with
some Frank–Wolfe vertex (a minimizer of `f'(x_t)` over `V`) and some away vertex (a maximizer of
`f'(x_t)` over `S_t`); every tie-breaking rule is allowed. -/
def IsAFWRun (V : Finset E) (f : E → ℝ) (L : ℝ) (x : ℕ → E) (S : ℕ → Finset E)
    (lam : ℕ → E → ℝ) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ lam 0 = (fun w => if w = x 0 then 1 else 0) ∧
    ∀ t, ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
      ∃ a ∈ S t, (∀ w ∈ S t, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) a) ∧
        IsAFWStep L (fderiv ℝ f (x t)) (x t) (S t) (lam t) v a (x (t + 1)) (S (t + 1)) (lam (t + 1))

/-- A run of fully-corrective Frank–Wolfe on `conv V`: it starts at a vertex with active set `{x₀}`;
every iterate minimizes `f` over the convex hull of its active set `S_t ⊆ V`, and the next iterate
is at least as good as every point of the segment from `x_t` to a Frank–Wolfe vertex (as is the
minimizer over the convex hull of `S_t ∪ {v_t}` of the book's algorithm). -/
def IsFCFWRun (V : Finset E) (f : E → ℝ) (x : ℕ → E) (S : ℕ → Finset E) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ ∀ t, S t ⊆ V ∧ x t ∈ convexHull ℝ (↑(S t) : Set E) ∧
    (∀ y ∈ convexHull ℝ (↑(S t) : Set E), f (x t) ≤ f y) ∧
    ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤ f (x t + γ • (v - x t))

open Lemmata.FrankWolfe in
open Classical in
/-- The facial distance of `conv V`: the infimum of `‖p - q‖` over proper exposed faces `F`, points
`p ∈ conv F` and `q ∈ conv (V \ F)`. -/
noncomputable def facialDistance (V : Finset E) : ℝ :=
  sInf {r : ℝ | ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
    ∃ p ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E),
      ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), r = ‖p - q‖}

open Classical in
/-- One step of pairwise Frank–Wolfe (Algorithm 3.1 of the book): move the weight
`γ = min {g(a - v) / (L ‖a - v‖²), λ_a}` from the away vertex `a` to the Frank–Wolfe vertex `v`,
and drop `a` from the active set when its weight is used up. -/
def IsPFWStep (L : ℝ) (g : StrongDual ℝ E) (x : E) (S : Finset E) (lam : E → ℝ) (v a : E)
    (x' : E) (S' : Finset E) (lam' : E → ℝ) : Prop :=
  let γ := min (g (a - v) / (L * ‖a - v‖ ^ 2)) (lam a)
  x' = x - γ • (a - v) ∧
    lam' = (fun w => lam w - (if w = a then γ else 0) + (if w = v then γ else 0)) ∧
    S' = if γ = lam a then (insert v S).erase a else insert v S

open Classical in
/-- A run of pairwise Frank–Wolfe on `conv V`: it starts at a vertex with active set `{x₀}` and
weight `1`, and every step is a pairwise step with some Frank–Wolfe vertex and some away vertex. -/
def IsPFWRun (V : Finset E) (f : E → ℝ) (L : ℝ) (x : ℕ → E) (S : ℕ → Finset E)
    (lam : ℕ → E → ℝ) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ lam 0 = (fun w => if w = x 0 then 1 else 0) ∧
    ∀ t, ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
      ∃ a ∈ S t, (∀ w ∈ S t, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) a) ∧
        IsPFWStep L (fderiv ℝ f (x t)) (x t) (S t) (lam t) v a (x (t + 1)) (S (t + 1)) (lam (t + 1))

end Lemmata.AwayStepFW
