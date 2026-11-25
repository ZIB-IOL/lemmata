module

public import Lemmata.FrankWolfeLDS.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Real

@[expose] public section

/-!
# The paper's results, as statements without proofs

One proposition per result of *Frank–Wolfe Beyond 1/t Convergence* (arXiv:2604.28006, numbering
of the arXiv version and of the NeurIPS 2026 camera-ready), about the objects of `Defs.lean`.
`Main.lean` proves each of them; nothing here depends on a proof.

Conventions shared by all statements:

* `E` is a real Hilbert space; the paper works in `ℝ^d`.
* `StandingAssumptions C lmo f L`: `C` is compact and convex with linear minimization oracle
  `lmo`, and `f` is convex, differentiable and `L`-smooth with `L > 0`.
* The oracle `lmo` and the line-search rule `σ` are arbitrary: the statements hold for every
  rule for breaking ties between minimizers.
* `xStar` is a minimizer, so `f (x t) - f xStar` is the primal gap `F_t = f(x_t) - f^⋆`, and
  `o(1/t)` is expressed as `(t + 2) F_t → 0`.
* The iterates of the three step-size rules from `x₀` are `fwIterates lmo f openLoopStep x₀`
  (open loop `2/(t+2)`), `fwIterates lmo f (shortStep lmo f L) x₀` (short step) and
  `fwIterates lmo f (fun _ => σ) x₀` (exact line search with rule `σ`).
-/

namespace Lemmata.FrankWolfeLDS

open Filter Topology
open scoped Gradient InnerProductSpace

universe u

/-- **Proposition 2.2** (`O(1/t)` convergence). With open-loop steps, short steps and exact line
search alike, `F_t ≤ 2 L D² / (t + 2)` for every `t ≥ 1`, where `D` is the diameter of `C`. -/
def StandardRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f σ →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ t : ℕ, 1 ≤ t →
      f (fwIterates lmo f openLoopStep x₀ t) - f xStar ≤ 2 * L * Metric.diam C ^ 2 / (t + 2) ∧
      f (fwIterates lmo f (shortStep lmo f L) x₀ t) - f xStar ≤
        2 * L * Metric.diam C ^ 2 / (t + 2) ∧
      f (fwIterates lmo f (fun _ => σ) x₀ t) - f xStar ≤ 2 * L * Metric.diam C ^ 2 / (t + 2)

/-- **Proposition 3.4** (uniform convexity implies local dual sharpness). If `C` is compact and
`(α, q)`-uniformly convex, then every oracle for `C` satisfies local dual sharpness around every
nonempty `M ⊆ C` with constants `(α/2, q)`. -/
def UniformlyConvexImpliesLDS : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (lmo : E → E) (α q : ℝ), IsCompact C → IsLinearMinimizationOracle C lmo →
    0 < α → 2 ≤ q → IsUniformlyConvexSet C α q →
    ∀ M ⊆ C, M.Nonempty → LocalDualSharpness C lmo M (α / 2) q

/-- **Theorem 3.5** (short steps or exact line search, conditional form). Under local dual
sharpness around a nonempty `M ⊆ C`, if the iterates approach points `p t ∈ M` with value
`f xStar` and zero gradient, then `(t + 2) (f (x t) - f xStar) → 0`. -/
def ConditionalShortStepLineSearch : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f σ →
    ∀ (M : Set E) (A q : ℝ), M ⊆ C → M.Nonempty → 0 < A → 2 ≤ q →
    LocalDualSharpness C lmo M A q →
    ∀ (xStar : E) (p : ℕ → E), xStar ∈ C → (∀ t, p t ∈ M) → (∀ t, f (p t) = f xStar) →
    (∀ t, ∇ f (p t) = 0) →
    ∀ x₀ ∈ C, ∀ x : ℕ → E,
      x = fwIterates lmo f (shortStep lmo f L) x₀ ∨ x = fwIterates lmo f (fun _ => σ) x₀ →
      Tendsto (fun t => ‖x t - p t‖) atTop (𝓝 0) →
      Tendsto (fun t : ℕ => ((t : ℝ) + 2) * (f (x t) - f xStar)) atTop (𝓝 0)

/-- **Theorem 3.6** (zero-gradient minimizer). Under local dual sharpness around the minimizer
set, if some minimizer has zero gradient, then short steps and exact line search converge with
`F_t = o(1/t)`. -/
def ZeroGradientMinimizer : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f σ →
    ∀ A q : ℝ, 0 < A → 2 ≤ q → LocalDualSharpness C lmo (minimizers C f) A q →
    ∀ xStar ∈ minimizers C f, ∇ f xStar = 0 →
    ∀ x₀ ∈ C, ∀ x : ℕ → E,
      x = fwIterates lmo f (shortStep lmo f L) x₀ ∨ x = fwIterates lmo f (fun _ => σ) x₀ →
      Tendsto (fun t : ℕ => ((t : ℝ) + 2) * (f (x t) - f xStar)) atTop (𝓝 0)

/-- **Proposition 3.7** (gradient bounded away from zero). Under local dual sharpness around the
minimizer set, if `G ≤ ‖∇ f x‖` on `C` for some `G > 0`, then short steps and exact line search
converge linearly for `q = 2`, with rate `1 - κ`, `κ = min {1, A G / L} / 2`, and with the
polynomial rate `K / (t - t₀ + 1)^{q/(q-2)}` for `q > 2`. -/
def GradientBoundedBelow : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f σ →
    ∀ A q G : ℝ, 0 < A → 2 ≤ q → LocalDualSharpness C lmo (minimizers C f) A q →
    0 < G → (∀ x ∈ C, G ≤ ‖∇ f x‖) →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ x : ℕ → E,
      x = fwIterates lmo f (shortStep lmo f L) x₀ ∨ x = fwIterates lmo f (fun _ => σ) x₀ →
      (q = 2 → ∃ t₀ : ℕ, ∀ t ≥ t₀,
        f (x t) - f xStar ≤ (1 - min 1 (A * G / L) / 2) ^ (t - t₀) * (f (x t₀) - f xStar)) ∧
      (2 < q → ∃ t₀ : ℕ, ∃ K > 0, ∀ t ≥ t₀,
        f (x t) - f xStar ≤ K / ((t - t₀ + 1 : ℕ) : ℝ) ^ (q / (q - 2)))

/-- **Corollary 3.8** (beyond `1/t`). Under local dual sharpness around the minimizer set, short
steps and exact line search converge with `F_t = o(1/t)` for every smooth convex objective. -/
def BeyondOneOverT : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f σ →
    ∀ A q : ℝ, 0 < A → 2 ≤ q → LocalDualSharpness C lmo (minimizers C f) A q →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C, ∀ x : ℕ → E,
      x = fwIterates lmo f (shortStep lmo f L) x₀ ∨ x = fwIterates lmo f (fun _ => σ) x₀ →
      Tendsto (fun t : ℕ => ((t : ℝ) + 2) * (f (x t) - f xStar)) atTop (𝓝 0)

/-- **Theorem 3.9** (open loop, conditional form). Under local dual sharpness around a nonempty
`M ⊆ C`, if the open-loop iterates approach points `p t ∈ M` with the optimal value, then
`(t + 2) F_t → 0`. -/
def ConditionalOpenLoop : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ (M : Set E) (A q : ℝ), M ⊆ C → M.Nonempty → 0 < A → 2 ≤ q →
    LocalDualSharpness C lmo M A q →
    ∀ xStar ∈ minimizers C f, ∀ p : ℕ → E, (∀ t, p t ∈ M) → (∀ t, f (p t) = f xStar) →
    ∀ x₀ ∈ C,
      Tendsto (fun t => ‖fwIterates lmo f openLoopStep x₀ t - p t‖) atTop (𝓝 0) →
      Tendsto (fun t : ℕ => ((t : ℝ) + 2) * (f (fwIterates lmo f openLoopStep x₀ t) - f xStar))
        atTop (𝓝 0)

/-- **Theorem 3.10** (open loop). Under local dual sharpness around the minimizer set, the
open-loop step sizes `2/(t+2)` give `F_t = o(1/t)`. -/
def OpenLoopRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ A q : ℝ, 0 < A → 2 ≤ q → LocalDualSharpness C lmo (minimizers C f) A q →
    ∀ xStar ∈ minimizers C f, ∀ x₀ ∈ C,
      Tendsto (fun t : ℕ => ((t : ℝ) + 2) * (f (fwIterates lmo f openLoopStep x₀ t) - f xStar))
        atTop (𝓝 0)

/-- **Theorem 4.2** (quantitative rate under a local Hölder error bound). Under local dual
sharpness with constants `(A, q)` and a local Hölder error bound of order `r ≥ 2` around the
minimizer set, all three step-size rules satisfy `F_t ≤ K / (t - t₀ + 1)^{rq/(rq-2)}` from some
`t₀` on. -/
def HolderErrorBoundRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (lmo : E → E) (f : E → ℝ) (L : NNReal), StandingAssumptions C lmo f L →
    ∀ σ : E → ℝ, IsExactLineSearch lmo f σ →
    ∀ A q B r : ℝ, 0 < A → 2 ≤ q → 0 < B → 2 ≤ r →
    LocalDualSharpness C lmo (minimizers C f) A q →
    ∀ xStar ∈ minimizers C f, LocalHolderErrorBound C f (minimizers C f) (f xStar) B r →
    ∀ x₀ ∈ C, ∀ x : ℕ → E,
      x = fwIterates lmo f openLoopStep x₀ ∨ x = fwIterates lmo f (shortStep lmo f L) x₀ ∨
        x = fwIterates lmo f (fun _ => σ) x₀ →
      ∃ t₀ : ℕ, ∃ K > 0, ∀ t ≥ t₀,
        f (x t) - f xStar ≤ K / ((t - t₀ + 1 : ℕ) : ℝ) ^ (r * q / (r * q - 2))

/-- **Lemma A.1** (uniformly convex gap bound). If `C` is `(α, q)`-uniformly convex, `x ∈ C`
and `s` minimizes `⟪g, ·⟫` over `C`, then `α/2 ‖g‖ ‖x - s‖^q ≤ ⟪g, x - s⟫`. -/
def UniformlyConvexGap : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (α q : ℝ), 0 < α → 2 ≤ q → IsUniformlyConvexSet C α q →
    ∀ g x s : E, x ∈ C → s ∈ C → (∀ y ∈ C, ⟪g, s⟫_ℝ ≤ ⟪g, y⟫_ℝ) →
      α / 2 * ‖g‖ * ‖x - s‖ ^ q ≤ ⟪g, x - s⟫_ℝ

/-- **Proposition A.2** (a uniformly convex patch with residual gap). Let `C` be compact. Suppose
that near `M` the region `C` lies in an `(α, q)`-uniformly convex set `K`, and that for every direction the
selected atom either supports `K` or leaves a gap of at least `β ‖g‖`. Then the oracle
satisfies local dual sharpness around `M` with constants
`(min {α/2, β / max {1, diam(C)^q}}, q)`. -/
def PatchCriterion : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (lmo : E → E), IsCompact C → IsLinearMinimizationOracle C lmo →
    ∀ (M K : Set E) (α q ρ β : ℝ), M ⊆ C → 0 < α → 2 ≤ q → IsUniformlyConvexSet K α q →
    0 < ρ → 0 < β →
    (∀ x ∈ C, Metric.infDist x M < ρ → x ∈ K ∧ ∀ g : E,
      (lmo g ∈ K ∧ ∀ y ∈ K, 0 ≤ ⟪g, y - lmo g⟫_ℝ) ∨ β * ‖g‖ ≤ ⟪g, x - lmo g⟫_ℝ) →
    LocalDualSharpness C lmo M (min (α / 2) (β / max 1 (Metric.diam C ^ q))) q

end Lemmata.FrankWolfeLDS
