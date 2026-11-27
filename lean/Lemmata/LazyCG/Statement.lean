module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.LazyCG

open Lemmata.FrankWolfe

universe u

/-- `f` has **curvature** at most `C` on `P`: for `x, v ∈ P` and `γ ∈ [0, 1]`,
`f(x + γ(v - x)) ≤ f(x) + γ f'(x)(v - x) + C γ²/2`. -/
def HasCurvature {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Set E) (f : E → ℝ)
    (C : ℝ) : Prop :=
  ∀ x ∈ P, ∀ v ∈ P, ∀ γ ∈ Set.Icc (0 : ℝ) 1,
    f (x + γ • (v - x)) ≤ f x + γ * fderiv ℝ f x (v - x) + C / 2 * γ ^ 2

/-- **Oracle 1** (the weak separation oracle `LPsep_P(c, x, Φ, K)`). A valid answer is either a
point `y ∈ V` with `c(x - y) > Φ/K`, or `none` (false), certifying `c(x - z) ≤ Φ` for all `z ∈ P`.
Here `V` holds the points the oracle may return, such as the vertices of `P = conv V`. -/
def IsWeakSepAnswer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V P : Set E)
    (c : StrongDual ℝ E) (x : E) (Φ K : ℝ) : Option E → Prop
  | some y => y ∈ V ∧ Φ / K < c (x - y)
  | none => ∀ z ∈ P, c (x - z) ≤ Φ

/-- The possible answers of **Algorithm 2**, the weak separation oracle built on a linear
optimization oracle with a cache: a cached point `y` with `c(x - y) > Φ/K` if there is one;
otherwise, with the answer `y₀` of the linear optimization oracle, `y₀` if `c(x - y₀) > Φ/K`, and
`none` if not. -/
def IsLPSepViaLP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (cache : Set E)
    (c : StrongDual ℝ E) (x : E) (Φ K : ℝ) (y₀ : E) (ans : Option E) : Prop :=
  (∃ y ∈ cache, Φ / K < c (x - y) ∧ ans = some y) ∨
    ((∀ y ∈ cache, c (x - y) ≤ Φ / K) ∧
      ((Φ / K < c (x - y₀) ∧ ans = some y₀) ∨ (c (x - y₀) ≤ Φ / K ∧ ans = none)))

/-- **Algorithm 2 is correct**, with a linear optimization oracle that minimizes `c` (line 4 of
the paper maximizes). If the cache lies in `V`, `y₀ ∈ V` minimizes `c` over `V`, `K ≥ 1` and
`Φ ≥ 0`, every answer of Algorithm 2 is a valid answer of Oracle 1 for `P = conv V`. -/
def LPSepViaLPCorrect : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V cache : Set E) (c : StrongDual ℝ E)
    (x : E) (Φ K : ℝ) (y₀ : E) (ans : Option E),
    cache ⊆ V → y₀ ∈ V → (∀ v ∈ V, c y₀ ≤ c v) → 1 ≤ K → 0 ≤ Φ →
    IsLPSepViaLP cache c x Φ K y₀ ans → IsWeakSepAnswer V (convexHull ℝ V) c x Φ K ans

/-- A run of the **lazy conditional gradient algorithm** (Algorithm 3) on `P` with curvature
parameter `C`, accuracy `K` and step sizes `γ`, indexed from `x₁` as in the paper. For `t ≥ 1`,
`Φ_t = (Φ_{t-1} + C γ_t²/2)/(1 + γ_t/K)`, and the weak separation oracle for `f'(x_t)`, `x_t` and
`Φ_t` either returns `v_t ∈ P` with `f'(x_t)(x_t - v_t) > Φ_t/K`, and then
`x_{t+1} = (1 - γ_t) x_t + γ_t v_t`, or certifies `f'(x_t)(x_t - z) ≤ Φ_t` for all `z ∈ P`, and
then `x_{t+1} = x_t`. -/
def IsLCGRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Set E) (f : E → ℝ)
    (C K : ℝ) (γ : ℕ → ℝ) (x : ℕ → E) (Φ : ℕ → ℝ) : Prop :=
  x 1 ∈ P ∧ ∀ t, 1 ≤ t →
    Φ t = (Φ (t - 1) + C / 2 * γ t ^ 2) / (1 + γ t / K) ∧
    ((∃ v ∈ P, Φ t / K < fderiv ℝ f (x t) (x t - v) ∧
        x (t + 1) = (1 - γ t) • x t + γ t • v) ∨
      ((∀ z ∈ P, fderiv ℝ f (x t) (x t - z) ≤ Φ t) ∧ x (t + 1) = x t))

/-- **Theorem 3.1** (lazy conditional gradients). Let `P` be convex and `f` convex and
differentiable with curvature `C` on `P`, let `K ≥ 1`, `γ_t = 2(K² + 1)/(K(t + K² + 2))` and
`f(x₁) - f(x⋆) ≤ Φ₀`. Every run of Algorithm 3 satisfies
`f(x_t) - f(x⋆) ≤ 2 max {C, Φ₀} (K² + 1)/(t + K² + 2)` for `t ≥ 1`. -/
def LCGRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Set E) (f : E → ℝ) (C K : ℝ)
    (x : ℕ → E) (Φ : ℕ → ℝ),
    Convex ℝ P → ConvexOn ℝ Set.univ f → Differentiable ℝ f → HasCurvature P f C → 1 ≤ K →
    IsLCGRun P f C K (fun t => 2 * (K ^ 2 + 1) / (K * ((t : ℝ) + K ^ 2 + 2))) x Φ →
    ∀ xStar ∈ minimizers P f, f (x 1) - f xStar ≤ Φ 0 →
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤ 2 * max C (Φ 0) * (K ^ 2 + 1) / ((t : ℝ) + K ^ 2 + 2)

/-- A run of the **parameter-free lazy conditional gradient algorithm** (Algorithm 7) on `P` with
accuracy `K`, indexed from `x₁`. For `t ≥ 1` the weak separation oracle for `f'(x_t)`, `x_t` and
`Φ_{t-1}` either returns `v_t ∈ P` with `f'(x_t)(x_t - v_t) > Φ_{t-1}/K`, followed by a line
search step on the segment `[x_t, v_t]` and `Φ_t = Φ_{t-1}`, or certifies
`f'(x_t)(x_t - z) ≤ Φ_{t-1}` for all `z ∈ P`, and then `x_{t+1} = x_t` and `Φ_t = Φ_{t-1}/2`. -/
def IsParamFreeLCGRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Set E)
    (f : E → ℝ) (K : ℝ) (x : ℕ → E) (Φ : ℕ → ℝ) : Prop :=
  x 1 ∈ P ∧ ∀ t, 1 ≤ t →
    (∃ v ∈ P, Φ (t - 1) / K < fderiv ℝ f (x t) (x t - v) ∧ ∃ γ ∈ Set.Icc (0 : ℝ) 1,
      x (t + 1) = x t + γ • (v - x t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, f (x (t + 1)) ≤ f (x t + s • (v - x t))) ∧ Φ t = Φ (t - 1)) ∨
    ((∀ z ∈ P, fderiv ℝ f (x t) (x t - z) ≤ Φ (t - 1)) ∧ x (t + 1) = x t ∧ Φ t = Φ (t - 1) / 2)

/-- **Theorem 4.2** (parameter-free lazy conditional gradients). Let `P` be convex and `f` convex
and differentiable with curvature `C > 0` on `P`, let `K ≥ 1` and `f(x₁) - f(x⋆) ≤ 2 Φ₀`. For
`ε > 0`, every run of Algorithm 7 satisfies `f(x_{N+1}) - f(x⋆) ≤ ε` as soon as
`N ≥ ⌈log₂ (Φ₀/ε)⌉₊ + 1 + 4 K ⌈log₂ (Φ₀/(K C))⌉₊ + 16 K² C/ε`. -/
def ParamFreeRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Set E) (f : E → ℝ) (C K : ℝ)
    (x : ℕ → E) (Φ : ℕ → ℝ),
    Convex ℝ P → ConvexOn ℝ Set.univ f → Differentiable ℝ f → HasCurvature P f C → 0 < C →
    1 ≤ K → IsParamFreeLCGRun P f K x Φ →
    ∀ xStar ∈ minimizers P f, f (x 1) - f xStar ≤ 2 * Φ 0 →
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      (⌈Real.logb 2 (Φ 0 / ε)⌉₊ : ℝ) + 1 + 4 * K * ⌈Real.logb 2 (Φ 0 / (K * C))⌉₊ +
          16 * K ^ 2 * C / ε ≤ N →
        f (x (N + 1)) - f xStar ≤ ε

open Classical in
/-- **Corollary 4.3** (few negative answers). Let `f` be convex and differentiable and
`f(x₁) - f(x⋆) ≤ 2 Φ₀`. If a run of Algorithm 7 still has `f(x_{N+1}) - f(x⋆) > ε > 0`, at most
`⌈log₂ (Φ₀/ε)⌉₊` of the iterations `1, …, N` received a negative answer, i.e. halved `Φ`; so at
most `⌈log₂ (Φ₀/ε)⌉₊ + 1` negative answers occur before the primal gap is at most `ε`. -/
def ParamFreeNegatives : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Set E) (f : E → ℝ) (K : ℝ)
    (x : ℕ → E) (Φ : ℕ → ℝ),
    ConvexOn ℝ Set.univ f → Differentiable ℝ f → IsParamFreeLCGRun P f K x Φ →
    ∀ xStar ∈ minimizers P f, f (x 1) - f xStar ≤ 2 * Φ 0 →
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ε < f (x (N + 1)) - f xStar →
      ((Finset.Icc 1 N).filter (fun t => Φ t ≠ Φ (t - 1))).card ≤ ⌈Real.logb 2 (Φ 0 / ε)⌉₊

end Lemmata.LazyCG
