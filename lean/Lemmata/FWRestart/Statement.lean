module

public import Lemmata.FWUniformlyConvex.Statement
public import Lemmata.AwayStepFW.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe Lemmata.CGBasics Lemmata.AwayStepFW

universe u

/-- **Lemma 2.3** (the strong Wolfe gap). Let `S ⊆ V` be finite, `x = ∑_{y ∈ S} λ_y y` a convex
combination with positive weights (a proper support of `x`), `f` convex over `conv V` and
differentiable at its points, `a ∈ S` a maximizer of `f'(x)` over `S` and `v ∈ V` a minimizer of
`f'(x)` over `V`, so that `w(x, S) = f'(x)(a - v)` is the strong Wolfe gap. Then
`f(x) - f(x⋆) ≤ w(x, S)` for every minimizer `x⋆` over `conv V`, and `w(x, S) = 0` if and only if
`x` minimizes `f` over `conv V`. -/
def StrongWolfeGap : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V S : Finset E) (f : E → ℝ)
    (lam : E → ℝ) (x a v : E), S ⊆ V → (∀ y ∈ S, 0 < lam y) → ∑ y ∈ S, lam y = 1 →
    x = ∑ y ∈ S, lam y • y → ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    a ∈ S → (∀ y ∈ S, fderiv ℝ f x y ≤ fderiv ℝ f x a) →
    v ∈ V → (∀ y ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
    (∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, f x - f xStar ≤ fderiv ℝ f x (a - v)) ∧
    (fderiv ℝ f x (a - v) = 0 ↔ x ∈ minimizers (convexHull ℝ (↑V : Set E)) f)

/-- **Lemma 3.6** (Hölderian error bounds give a strong Wolfe primal bound). Let `f` be convex over
`conv V`, differentiable at its points, with a `(θ, c)`-Hölderian error bound,
`dist(x, X⋆) ≤ c (f(x) - f⋆)^θ` with `c > 0` and `θ ∈ [0, 1/2]`, and let `δ > 0` have the scaling
property of `conv V` (for instance the pyramidal width). For `x ∈ conv S` with `S ⊆ V`, an away
vertex `a ∈ S` and a Frank–Wolfe vertex `v ∈ V`,
`f(x) - f⋆ ≤ (c/δ)^{1/(1-θ)} f'(x)(a - v)^{1/(1-θ)}`: the `1/(1-θ)`-strong Wolfe primal bound. -/
def HEBStrongWolfeBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V S : Finset E) (f : E → ℝ)
    (c θ δ : ℝ) (x a v xStar : E), ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f →
    (∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y) →
    IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f c θ → 0 < c → θ ∈ Set.Icc (0 : ℝ) (1 / 2) →
    0 < δ → IsScaling V δ → xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f → S ⊆ V →
    x ∈ convexHull ℝ (↑S : Set E) → a ∈ S → (∀ y ∈ S, fderiv ℝ f x y ≤ fderiv ℝ f x a) →
    v ∈ V → (∀ y ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
      f x - f xStar ≤ (c / δ) ^ (1 / (1 - θ)) * fderiv ℝ f x (a - v) ^ (1 / (1 - θ))

/-- **Theorem 7.3** (vanilla Frank–Wolfe over strongly convex sets). Let `C` be compact, convex and
`α`-strongly convex (`(α, 2)`-uniformly convex) with diameter `D > 0`, and `f` convex and `L`-smooth
with a `(θ, c)`-Hölderian error bound on `C`, `c > 0`, `θ ∈ (0, 1/2]`. With `K = (Lc/α)^{1/(1-θ)}`
and `t₀ = max {⌊log_{1/2} (2K/(L D²))⌋ + 2, 1}`, every short-step run satisfies
`f(x_t) - f⋆ ≤ (L D²/2) 2^{1-t}` for `1 ≤ t < t₀` and
`f(x_t) - f⋆ ≤ K/(1 + (1 - θ)(t - t₀)/2)^{1/(1-θ)}` for `t ≥ t₀`: the rate `O(t^{-1/(1-θ)})`. -/
def StronglyConvexSetRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (α c θ : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α 2 → 0 < α → 0 < (L : ℝ) →
    0 < Metric.diam C → ConvexOn ℝ Set.univ f → IsSmooth f L → IsHolderErrorBound C f c θ →
    0 < c → θ ∈ Set.Ioc (0 : ℝ) (1 / 2) → IsShortStepRun C f L x v γ →
    ∀ xStar ∈ minimizers C f,
      let K := ((L : ℝ) * (c / α)) ^ (1 / (1 - θ))
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) (2 * K / (L * Metric.diam C ^ 2))⌋ + 2) 1
      ∀ t : ℕ, 1 ≤ t →
        ((t : ℤ) < t₀ → f (x t) - f xStar ≤ L * Metric.diam C ^ 2 / 2 * (1 / 2) ^ (t - 1)) ∧
        (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
          K / (1 + (1 - θ) / 2 * ((t : ℝ) - t₀)) ^ (1 / (1 - θ)))

section Algorithms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A weighted active set of `x`: `S ⊆ V` with nonnegative weights that vanish outside `S`, sum to
`1` and represent `x`. -/
def IsWeightedState (V : Finset E) (x : E) (S : Finset E) (lam : E → ℝ) : Prop :=
  S ⊆ V ∧ (∀ w, 0 ≤ lam w) ∧ (∀ w ∉ S, lam w = 0) ∧ ∑ w ∈ S, lam w = 1 ∧
    x = ∑ w ∈ S, lam w • w

/-- `w` is the strong Wolfe gap of `x` with active set `S`: `w = f'(x)(a - v)` for a Frank–Wolfe
vertex `v ∈ V` and an away vertex `a ∈ S`. -/
def IsStrongWolfeGapAt (V : Finset E) (f : E → ℝ) (x : E) (S : Finset E) (w : ℝ) : Prop :=
  ∃ v ∈ V, (∀ y ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x y) ∧
    ∃ a ∈ S, (∀ y ∈ S, fderiv ℝ f x y ≤ fderiv ℝ f x a) ∧ w = fderiv ℝ f x (a - v)

open Classical in
/-- One step of fractional away-step Frank–Wolfe (Algorithm 1) from the state `(x, S, λ)` with
Frank–Wolfe vertex `v`, away vertex `a` and threshold `G`: the Frank–Wolfe step when
`f'(x)(x - v) > G`, otherwise the away step, each with exact line search over `[0, η_max]`
(`η_max = 1`, respectively `λ_a/(1 - λ_a)`); the weights and the active set are updated as in
away-step Frank–Wolfe. -/
def IsFAFWStep (f : E → ℝ) (G : ℝ) (x : E) (S : Finset E) (lam : E → ℝ) (v a : E) (x' : E)
    (S' : Finset E) (lam' : E → ℝ) : Prop :=
  if G < fderiv ℝ f x (x - v) then
    ∃ η ∈ Set.Icc (0 : ℝ) 1, (∀ s ∈ Set.Icc (0 : ℝ) 1, f (x - η • (x - v)) ≤ f (x - s • (x - v))) ∧
      x' = x - η • (x - v) ∧ lam' = (fun w => (1 - η) * lam w + if w = v then η else 0) ∧
      S' = if η = 1 then {v} else insert v S
  else
    ∃ η ∈ Set.Icc (0 : ℝ) (lam a / (1 - lam a)),
      (∀ s ∈ Set.Icc (0 : ℝ) (lam a / (1 - lam a)), f (x - η • (a - x)) ≤ f (x - s • (a - x))) ∧
      x' = x - η • (a - x) ∧ lam' = (fun w => (1 + η) * lam w - if w = a then η else 0) ∧
      S' = if η = lam a / (1 - lam a) then S.erase a else S

/-- Iteration `t` of fractional away-step Frank–Wolfe with stopping level `ε`: the strong Wolfe gap
`f'(x_t)(a - v)` of a Frank–Wolfe vertex `v` and an away vertex `a` exceeds `ε`, so the algorithm
has not stopped, and the step from `t` to `t + 1` is a fractional away-step Frank–Wolfe step with
threshold `ε/2`. -/
def IsFAFWIter (V : Finset E) (f : E → ℝ) (ε : ℝ) (x : ℕ → E) (S : ℕ → Finset E)
    (lam : ℕ → E → ℝ) (t : ℕ) : Prop :=
  ∃ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
    ∃ a ∈ S t, (∀ w ∈ S t, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) a) ∧
      ε < fderiv ℝ f (x t) (a - v) ∧
      IsFAFWStep f (ε / 2) (x t) (S t) (lam t) v a (x (t + 1)) (S (t + 1)) (lam (t + 1))

/-- The first `T` iterations of fractional away-step Frank–Wolfe (Algorithm 1) with schedule
parameter `γ` and reference gap `w₀` (the strong Wolfe gap of the initial state), started from a
weighted active set: the algorithm has not stopped before iteration `T`. -/
def IsFAFWRun (V : Finset E) (f : E → ℝ) (γ w₀ : ℝ) (x : ℕ → E) (S : ℕ → Finset E)
    (lam : ℕ → E → ℝ) (T : ℕ) : Prop :=
  IsWeightedState V (x 0) (S 0) (lam 0) ∧ ∀ t < T, IsFAFWIter V f (Real.exp (-γ) * w₀) x S lam t

/-- Scheduled restarts of fractional away-step Frank–Wolfe with constant parameter `γ`
(Algorithm 2): restart times `τ₀ = 0 ≤ τ₁ ≤ ⋯` with strong Wolfe gaps `W_k` at `τ_k`; on
`[τ_k, τ_{k+1})` the iterations are those of Algorithm 1 started at `τ_k`, with stopping level
`e^{-γ} W_k`, and at `τ_{k+1}` it has stopped: `W_{k+1} ≤ e^{-γ} W_k`. -/
def IsRestartRun (V : Finset E) (f : E → ℝ) (γ : ℝ) (x : ℕ → E) (S : ℕ → Finset E)
    (lam : ℕ → E → ℝ) (τ : ℕ → ℕ) (W : ℕ → ℝ) : Prop :=
  IsWeightedState V (x 0) (S 0) (lam 0) ∧ τ 0 = 0 ∧
    ∀ k, τ k ≤ τ (k + 1) ∧ IsStrongWolfeGapAt V f (x (τ k)) (S (τ k)) (W k) ∧
      W (k + 1) ≤ Real.exp (-γ) * W k ∧
      ∀ t, τ k ≤ t → t < τ (k + 1) → IsFAFWIter V f (Real.exp (-γ) * W k) x S lam t

end Algorithms

/-- **Proposition 4.1** (complexity of fractional away-step Frank–Wolfe). Let `f` be convex and
`L`-smooth, `D` a bound on the diameter of `conv V`, and `w₀ > 0` with the burn-in condition
`e^{-γ} w₀/2 ≤ L D²` and the strong Wolfe primal bound `f(x₀) - f⋆ ≤ μ w₀^r` at the initial point.
If fractional away-step Frank–Wolfe has not stopped before iteration `T`, then
`T ≤ |S₀| - |S_T| + 16 e^{2γ} L D² μ w₀^{r-2}`. -/
def FractionalComplexity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (D γ w₀ μ r : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (T : ℕ),
    ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D) →
    0 < w₀ → Real.exp (-γ) * w₀ / 2 ≤ L * D ^ 2 → IsFAFWRun V f γ w₀ x S lam T →
    (∀ y ∈ convexHull ℝ (↑V : Set E), f (x 0) - f y ≤ μ * w₀ ^ r) →
      (T : ℝ) ≤ (S 0).card - (S T).card + 16 * Real.exp (2 * γ) * (L * D ^ 2) * μ * w₀ ^ (r - 2)

/-- **Proposition 4.2** (burn-in phase). Let `f` be convex and `L`-smooth with `L > 0`, `D > 0` a
bound on the diameter of `conv V`, `γ > 0`, and consider scheduled restarts with `W₀ > 0`. Within
`N = ⌊log (W₀/(2 L D²))/γ⌋₊` restarts, the burn-in condition `e^{-γ} W_k/2 ≤ L D²` of
Proposition 4.1 holds, after `τ_k ≤ |S₀| - |S_{τ_k}| + 8 e^γ k` iterations. -/
def BurnIn : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (D γ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (τ : ℕ → ℕ) (W : ℕ → ℝ),
    ConvexOn ℝ Set.univ f → IsSmooth f L → 0 < (L : ℝ) → 0 < D →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D) →
    0 < γ → IsRestartRun V f γ x S lam τ W → 0 < W 0 →
    ∃ k ≤ ⌊Real.log (W 0 / (2 * (L * D ^ 2))) / γ⌋₊,
      Real.exp (-γ) * W k / 2 ≤ L * D ^ 2 ∧
        (τ k : ℝ) ≤ (S 0).card - (S (τ k)).card + 8 * Real.exp γ * k

/-- **Theorem 5.1** (rate of scheduled restarts). Let `f` be convex and `L`-smooth with a
`(θ, c)`-Hölderian error bound on `conv V`, `θ ∈ [0, 1/2]`, let `δ > 0` have the scaling property,
`D` a bound on the diameter of `conv V` and `γ > 0`, and consider scheduled restarts with the
burn-in condition `e^{-γ} W₀/2 ≤ L D²`. With `r = 1/(1 - θ)`, `K = 16 e^{2γ} L D² (c/δ)^r` and
`T̃ = max {0, τ_R - (|S₀| - |S_{τ_R}|)}` after `R` restarts,
`f(x_{τ_R}) - f⋆ ≤ W₀/(1 + T̃ C_γ)^{1/(2-r)}` with `C_γ = (e^{γ(2-r)} - 1)/(K W₀^{r-2})` when
`θ < 1/2`, and `f(x_{τ_R}) - f⋆ ≤ W₀ e^{-γ T̃/K}` when `θ = 1/2`. -/
def RestartRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (D c θ δ γ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (τ : ℕ → ℕ) (W : ℕ → ℝ)
    (xStar : E), ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D) →
    IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f c θ → 0 < c → θ ∈ Set.Icc (0 : ℝ) (1 / 2) →
    0 < δ → IsScaling V δ → xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f → 0 < γ →
    IsRestartRun V f γ x S lam τ W → Real.exp (-γ) * W 0 / 2 ≤ L * D ^ 2 →
    ∀ R : ℕ,
      let r := 1 / (1 - θ)
      let K := 16 * Real.exp (2 * γ) * (L * D ^ 2) * (c / δ) ^ r
      let T := max 0 ((τ R : ℝ) - ((S 0).card - (S (τ R)).card))
      (θ < 1 / 2 → f (x (τ R)) - f xStar ≤
        W 0 / (1 + T * ((Real.exp (γ * (2 - r)) - 1) / (K * W 0 ^ (r - 2)))) ^ (1 / (2 - r))) ∧
      (θ = 1 / 2 → f (x (τ R)) - f xStar ≤ W 0 * Real.exp (-(γ * T / K)))

section Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `f` has Hölder curvature at most `C` with exponent `s` over `conv V`:
`f(x + η(u - v)) ≤ f(x) + η f'(x)(u - v) + C η^s/s` for `x, u, v ∈ conv V` and `η ∈ [0, 1]`. For an
`(L, s)`-Hölder smooth `f` this holds with `C = L D^s`, `D` the diameter of `conv V`. -/
def IsHolderCurvature (V : Finset E) (f : E → ℝ) (C s : ℝ) : Prop :=
  ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ u ∈ convexHull ℝ (↑V : Set E),
    ∀ v ∈ convexHull ℝ (↑V : Set E), ∀ η ∈ Set.Icc (0 : ℝ) 1,
      f (x + η • (u - v)) ≤ f x + η * fderiv ℝ f x (u - v) + C * η ^ s / s

end Holder

/-- **Proposition 6.1** (complexity under Hölder smoothness). Let `f` be convex and differentiable
with Hölder curvature at most `C` and exponent `s > 1` over `conv V`, and let `w₀ > 0` satisfy
`e^{-γ} w₀/2 ≤ C` and the strong Wolfe primal bound `f(x₀) - f⋆ ≤ μ w₀^r`. If fractional away-step
Frank–Wolfe has not stopped before iteration `T`, then
`T ≤ |S₀| - |S_T| + 2^{1+s/(s-1)} s/(s-1) e^{sγ/(s-1)} μ C^{1/(s-1)} w₀^{r-s/(s-1)}`. -/
def HolderComplexity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (C s γ w₀ μ r : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (T : ℕ),
    ConvexOn ℝ Set.univ f → Differentiable ℝ f → IsHolderCurvature V f C s → 1 < s →
    0 < w₀ → Real.exp (-γ) * w₀ / 2 ≤ C → IsFAFWRun V f γ w₀ x S lam T →
    (∀ y ∈ convexHull ℝ (↑V : Set E), f (x 0) - f y ≤ μ * w₀ ^ r) →
      (T : ℝ) ≤ (S 0).card - (S T).card + 2 ^ (1 + s / (s - 1)) * (s / (s - 1)) *
        Real.exp (s / (s - 1) * γ) * μ * C ^ (1 / (s - 1)) * w₀ ^ (r - s / (s - 1))

/-- **Proposition 6.3** (burn-in phase under Hölder smoothness). Let `f` be convex and
differentiable with Hölder curvature at most `C > 0` and exponent `s > 1` over `conv V`, let
`γ > 0`, and consider scheduled restarts with `W₀ > 0`. Within `N = ⌊log (W₀/(2C))/γ⌋₊` restarts the
burn-in condition `e^{-γ} W_k/2 ≤ C` holds, after `τ_k ≤ |S₀| - |S_{τ_k}| + 4 s/(s-1) e^γ k`
iterations. -/
def HolderBurnIn : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (C s γ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (τ : ℕ → ℕ) (W : ℕ → ℝ),
    ConvexOn ℝ Set.univ f → Differentiable ℝ f → IsHolderCurvature V f C s → 1 < s → 0 < C →
    0 < γ → IsRestartRun V f γ x S lam τ W → 0 < W 0 →
    ∃ k ≤ ⌊Real.log (W 0 / (2 * C)) / γ⌋₊,
      Real.exp (-γ) * W k / 2 ≤ C ∧
        (τ k : ℝ) ≤ (S 0).card - (S (τ k)).card + 4 * (s / (s - 1)) * Real.exp γ * k

/-- **Theorem 6.2** (rate of scheduled restarts under Hölder smoothness). Let `f` be convex and
differentiable with Hölder curvature at most `C` and exponent `s > 1` over `conv V` and a
`(θ, c)`-Hölderian error bound, `θ ∈ [0, 1/2]`, with `r = 1/(1 - θ) < s/(s - 1)`; let `δ > 0` have
the scaling property, `γ > 0`, and assume the burn-in condition `e^{-γ} W₀/2 ≤ C`. With
`τ = s/(s - 1) - r`, `K = 2^{1+s/(s-1)} s/(s-1) (c/δ)^r C^{1/(s-1)} e^{sγ/(s-1)}` and
`T̃ = max {0, τ_R - (|S₀| - |S_{τ_R}|)}` after `R` restarts,
`f(x_{τ_R}) - f⋆ ≤ W₀/(1 + T̃ C_γ)^{1/τ}` with `C_γ = (e^{γτ} - 1)/(K W₀^{r-s/(s-1)})`. -/
def HolderRestartRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (C s c θ δ γ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (τ : ℕ → ℕ) (W : ℕ → ℝ)
    (xStar : E), ConvexOn ℝ Set.univ f → Differentiable ℝ f → IsHolderCurvature V f C s → 1 < s →
    IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f c θ → 0 < c → θ ∈ Set.Icc (0 : ℝ) (1 / 2) →
    1 / (1 - θ) < s / (s - 1) → 0 < δ → IsScaling V δ →
    xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f → 0 < γ → IsRestartRun V f γ x S lam τ W →
    Real.exp (-γ) * W 0 / 2 ≤ C →
    ∀ R : ℕ,
      let r := 1 / (1 - θ)
      let K := 2 ^ (1 + s / (s - 1)) * (s / (s - 1)) * (c / δ) ^ r * C ^ (1 / (s - 1)) *
        Real.exp (s / (s - 1) * γ)
      let T := max 0 ((τ R : ℝ) - ((S 0).card - (S (τ R)).card))
      f (x (τ R)) - f xStar ≤ W 0 / (1 + T * ((Real.exp (γ * (s / (s - 1) - r)) - 1) /
        (K * W 0 ^ (r - s / (s - 1))))) ^ (1 / (s / (s - 1) - r))

/-- **Proposition 5.3** (robustness in `γ`, the cases `r = 1` and `r = 2`). Write
`C_γ = (e^{γ(2-r)} - 1)/(e^{2γ} K₀ W₀^{r-2})` for the constant of Theorem 5.1 with
`K₀ = 16 L D² (c/δ)^r`. For `r = 1`, the bound `W₀/(1 + T C_{1/2})` of the restart scheme with
`γ = 1/2` is at most `e/(4(√e - 1)) ≈ 1.05` times the bound `W₀/(1 + T C_γ)` for every `γ > 0`. For
`r = 2`, the bound `W₀ e^{-γ T/(e^{2γ} K₀)}` is smallest for `γ = 1/2`. -/
def RobustGamma : Prop :=
  ∀ (K₀ W₀ T γ : ℝ), 0 < K₀ → 0 < W₀ → 0 ≤ T → 0 < γ →
    W₀ / (1 + T * ((Real.exp (1 / 2) - 1) / (Real.exp (2 * (1 / 2)) * K₀ * W₀ ^ ((1 : ℝ) - 2)))) ≤
        Real.exp 1 / (4 * (Real.sqrt (Real.exp 1) - 1)) *
          (W₀ / (1 + T * ((Real.exp γ - 1) / (Real.exp (2 * γ) * K₀ * W₀ ^ ((1 : ℝ) - 2))))) ∧
      W₀ * Real.exp (-(1 / 2 * T / (Real.exp (2 * (1 / 2)) * K₀))) ≤
        W₀ * Real.exp (-(γ * T / (Real.exp (2 * γ) * K₀)))

section Fractional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iteration `t` of fractional Frank–Wolfe (Algorithm 3) over `C` with stopping level `ε`: the
Frank–Wolfe gap `f'(x_t)(x_t - v)` of a Frank–Wolfe vertex `v ∈ C` exceeds `ε`, so the algorithm
has not stopped, and the step goes towards `v` with exact line search over `[0, 1]`. -/
def IsFFWIter (C : Set E) (f : E → ℝ) (ε : ℝ) (x : ℕ → E) (t : ℕ) : Prop :=
  ∃ v ∈ C, (∀ w ∈ C, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) ∧
    ε < fderiv ℝ f (x t) (x t - v) ∧ ∃ η ∈ Set.Icc (0 : ℝ) 1,
      (∀ s ∈ Set.Icc (0 : ℝ) 1, f (x t - η • (x t - v)) ≤ f (x t - s • (x t - v))) ∧
        x (t + 1) = x t - η • (x t - v)

/-- `g` is the Frank–Wolfe gap of `x` over `C`: `g = f'(x)(x - v)` for a Frank–Wolfe vertex
`v ∈ C`. -/
def IsFWGapAt (C : Set E) (f : E → ℝ) (x : E) (g : ℝ) : Prop :=
  ∃ v ∈ C, (∀ w ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x w) ∧ g = fderiv ℝ f x (x - v)

/-- Scheduled restarts of fractional Frank–Wolfe with parameter `γ` (Algorithm 2 with Algorithm 3
inside): restart times `τ₀ = 0 ≤ τ₁ ≤ ⋯` with Frank–Wolfe gaps `G_k` at `τ_k`; on `[τ_k, τ_{k+1})`
the iterations are those of Algorithm 3 with stopping level `e^{-γ} G_k`, and at `τ_{k+1}` it has
stopped: `G_{k+1} ≤ e^{-γ} G_k`. -/
def IsFFWRestartRun (C : Set E) (f : E → ℝ) (γ : ℝ) (x : ℕ → E) (τ : ℕ → ℕ) (G : ℕ → ℝ) :
    Prop :=
  x 0 ∈ C ∧ τ 0 = 0 ∧
    ∀ k, τ k ≤ τ (k + 1) ∧ IsFWGapAt C f (x (τ k)) (G k) ∧ G (k + 1) ≤ Real.exp (-γ) * G k ∧
      ∀ t, τ k ≤ t → t < τ (k + 1) → IsFFWIter C f (Real.exp (-γ) * G k) x t

end Fractional

/-- **Lemma 7.1** (scaling of the Frank–Wolfe gap near an interior optimum). If the closed ball of
radius `z > 0` around `x⋆` lies in `C`, `‖x - x⋆‖ ≤ z/2` and `v ∈ C` minimizes `f'(x)` over `C`,
then the Frank–Wolfe gap satisfies `f'(x)(x - v) ≥ (z/2) ‖f'(x)‖`. -/
def InteriorFWScaling : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (z : ℝ)
    (x xStar v : E), 0 < z → Metric.closedBall xStar z ⊆ C → ‖x - xStar‖ ≤ z / 2 → v ∈ C →
    (∀ w ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x w) → z / 2 * ‖fderiv ℝ f x‖ ≤ fderiv ℝ f x (x - v)

/-- **Proposition 7.2** (scheduled restarts of fractional Frank–Wolfe). Let `C` be compact and
convex with diameter at most `D`, let `f` be convex and `L`-smooth with a `(θ, c)`-Hölderian error
bound on `C`, `θ ∈ [0, 1/2]`, and let the balls of radius `z > 0` around the minimizers, within the
affine hull of `C`, lie in `C`. Let `γ > 0` and assume `e^{-γ} G₀ ≤ L D²`. With `r = 1/(1 - θ)` and
`K = 2 e^{2γ} L D² (c/z)^r`, after `R` restarts and `T = τ_R` iterations,
`f(x_T) - f⋆ ≤ G₀/(1 + T C_γ)^{1/(2-r)}` with `C_γ = (e^{γ(2-r)} - 1)/(K G₀^{r-2})` when
`θ < 1/2`, and `f(x_T) - f⋆ ≤ G₀ e^{-γ T/K}` when `θ = 1/2`. -/
def FractionalFWRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (D c θ z γ : ℝ) (x : ℕ → E) (τ : ℕ → ℕ) (G : ℕ → ℝ) (xStar : E),
    IsCompact C → Convex ℝ C → ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ y ∈ C, ∀ w ∈ C, ‖y - w‖ ≤ D) → IsHolderErrorBound C f c θ → 0 < c →
    θ ∈ Set.Icc (0 : ℝ) (1 / 2) → 0 < z →
    (∀ y ∈ minimizers C f, ∀ w ∈ affineSpan ℝ C, ‖w - y‖ ≤ z → w ∈ C) →
    xStar ∈ minimizers C f → 0 < γ → IsFFWRestartRun C f γ x τ G →
    Real.exp (-γ) * G 0 ≤ L * D ^ 2 →
    ∀ R : ℕ,
      let r := 1 / (1 - θ)
      let K := 2 * Real.exp (2 * γ) * (L * D ^ 2) * (c / z) ^ r
      (θ < 1 / 2 → f (x (τ R)) - f xStar ≤
        G 0 / (1 + (τ R : ℝ) * ((Real.exp (γ * (2 - r)) - 1) / (K * G 0 ^ (r - 2)))) ^
          (1 / (2 - r))) ∧
      (θ = 1 / 2 → f (x (τ R)) - f xStar ≤ G 0 * Real.exp (-(γ * τ R / K)))

/-- **Lemma A.1** (one run with a large `γ`). As long as fractional away-step Frank–Wolfe takes
Frank–Wolfe steps, that is, the Frank–Wolfe gap exceeds `e^{-γ} w₀/2`, it converges like
Frank–Wolfe: `f(x_t) - f(y) ≤ 2 L D²/t` for `1 ≤ t ≤ T` and every `y ∈ conv V`. -/
def OneShotRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ) (L : NNReal)
    (D γ w₀ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (T : ℕ),
    ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D) →
    IsFAFWRun V f γ w₀ x S lam T →
    (∀ t < T, ∀ v ∈ V, (∀ w ∈ V, fderiv ℝ f (x t) v ≤ fderiv ℝ f (x t) w) →
      Real.exp (-γ) * w₀ / 2 < fderiv ℝ f (x t) (x t - v)) →
    ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ t : ℕ, 1 ≤ t → t ≤ T →
      f (x t) - f y ≤ 2 * (L * D ^ 2) / t

/-- **Lemma B.1** (a recurrence and its sublinear rate, corrected). Let `h ≥ 0` satisfy
`h_{t+1} ≤ h_t max {1/2, 1 - M h_t^β}` with `M > 0` and `β ∈ (0, 1]`. If `k ≥ 1/(2^β - 1)`,
`C' ≥ 1/(2^β - 1)`, `h₀ k^{1/β} ≤ C` and `2 (C'/M)^{1/β} ≤ C`, then `h_t ≤ C/(t + k)^{1/β}` for
all `t ≥ 0`. -/
def RecurrenceRate : Prop :=
  ∀ (h : ℕ → ℝ) (M β k C' C : ℝ), (∀ t, 0 ≤ h t) → 0 < M → 0 < β → β ≤ 1 →
    (∀ t, h (t + 1) ≤ h t * max (1 / 2) (1 - M * h t ^ β)) → 1 / (2 ^ β - 1) ≤ k →
    1 / (2 ^ β - 1) ≤ C' → h 0 * k ^ (1 / β) ≤ C → 2 * (C' / M) ^ (1 / β) ≤ C →
    ∀ t : ℕ, h t ≤ C / ((t : ℝ) + k) ^ (1 / β)

end Lemmata.FWRestart
