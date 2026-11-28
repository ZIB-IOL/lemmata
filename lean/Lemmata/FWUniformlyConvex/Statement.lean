module

public import Lemmata.CGBasics.Statement
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWUniformlyConvex

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

/-- **Local uniform convexity** at `x⋆` (the hypothesis of Lemma 2.4): for all `x ∈ C`,
`η ∈ [0, 1]` and unit vectors `z`, the point `η x⋆ + (1 - η) x + η (1 - η) α ‖x⋆ - x‖^q z` lies in
`C`. -/
def IsLocallyUniformlyConvexAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (α q : ℝ) (xStar : E) : Prop :=
  ∀ x ∈ C, ∀ η ∈ Set.Icc (0 : ℝ) 1, ∀ z : E, ‖z‖ = 1 →
    η • xStar + (1 - η) • x + (η * (1 - η) * α * ‖xStar - x‖ ^ q) • z ∈ C

/-- The **local scaling inequality** at `x⋆` (equation (8)):
`α/2 ‖f'(x⋆)‖ ‖x⋆ - x‖^q ≤ f'(x⋆)(x - x⋆)` for all `x ∈ C`. -/
def IsLocalScaling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (α q : ℝ) (xStar : E) : Prop :=
  ∀ x ∈ C, α / 2 * ‖fderiv ℝ f xStar‖ * ‖xStar - x‖ ^ q ≤ fderiv ℝ f xStar (x - xStar)

/-- **Lemma 2.4** (local uniform convexity gives the local scaling inequality). If `x⋆ ∈ C`
satisfies the first-order optimality condition `f'(x⋆)(x - x⋆) ≥ 0` for `x ∈ C`, and `C` is locally
`(α, q)`-uniformly convex at `x⋆`, then the local scaling inequality holds at `x⋆`. -/
def LocalScalingOfLocallyUC : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (α q : ℝ)
    (xStar : E), xStar ∈ C → (∀ x ∈ C, 0 ≤ fderiv ℝ f xStar (x - xStar)) →
    IsLocallyUniformlyConvexAt C α q xStar → IsLocalScaling C f α q xStar

/-- **Corollary 2.8** (a uniformly convex superset). If `C ⊆ Γ` for an `(α, q)`-uniformly convex
set `Γ`, and `x⋆ ∈ C` satisfies `f'(x⋆)(y - x⋆) ≥ 0` for all `y ∈ Γ` (that is, `-∇f(x⋆)` lies in
the normal cone of `Γ` at `x⋆`), then the local scaling inequality holds at `x⋆` for `C`. -/
def LocalScalingOfSuperset : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C Γ : Set E) (f : E → ℝ) (α q : ℝ)
    (xStar : E), C ⊆ Γ → IsUniformlyConvexSet Γ α q → xStar ∈ C →
    (∀ y ∈ Γ, 0 ≤ fderiv ℝ f xStar (y - xStar)) → IsLocalScaling C f α q xStar

/-- **Lemma 2.9** (scaling under a Hölderian error bound). Let `C` be `(α, q)`-uniformly convex
with `α > 0`, `f` convex over `C` and differentiable at its points with a minimizer `x⋆` and a
`(μ, θ)`-Hölderian error bound, `μ > 0`, `θ ∈ [0, 1/2]`. For `x ∈ C` and a Frank–Wolfe vertex `v`,
`(α/μ) ‖x - v‖^q (f(x) - f(x⋆))^{1-θ} ≤ f'(x)(x - v)`. -/
def HEBScaling : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (α q μ θ : ℝ) (xStar x v : E), IsUniformlyConvexSet C α q → 0 < α → ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → IsHolderErrorBound C f μ θ → 0 < μ →
    θ ∈ Set.Icc (0 : ℝ) (1 / 2) → xStar ∈ minimizers C f → x ∈ C → v ∈ C →
    (∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
      α / μ * ‖x - v‖ ^ q * (f x - f xStar) ^ (1 - θ) ≤ fderiv ℝ f x (x - v)

/-- **Theorem 2.10** (rates under a Hölderian error bound). Let `C` be compact, convex and
`(α, q)`-uniformly convex with `q ≥ 2` and diameter `D > 0`, and `f` convex and `L`-smooth with a
`(μ, θ)`-Hölderian error bound on `C`, `μ > 0`, `θ ∈ (0, 1/2]`. With `a = 1 - 2θ/q`,
`K = (L (μ/α)^{2/q})^{1/a}` and `t₀ = max {⌊log_{1/2} (2K/(L D²))⌋ + 2, 1}`, every short-step run
satisfies `f(x_t) - f(x⋆) ≤ (L D²/2) 2^{1-t}` for `1 ≤ t < t₀` and
`f(x_t) - f(x⋆) ≤ K/(1 + a (t - t₀)/2)^{1/a}` for `t ≥ t₀`: the rate `O(t^{-1/(1-2θ/q)})`. -/
def HEBRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (α q μ θ : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ),
    IsCompact C → Convex ℝ C → IsUniformlyConvexSet C α q → 2 ≤ q → 0 < α → 0 < (L : ℝ) →
    0 < Metric.diam C → ConvexOn ℝ Set.univ f → IsSmooth f L → IsHolderErrorBound C f μ θ →
    0 < μ → θ ∈ Set.Ioc (0 : ℝ) (1 / 2) → IsShortStepRun C f L x v γ →
    ∀ xStar ∈ minimizers C f,
      let a := 1 - 2 * θ / q
      let K := ((L : ℝ) * (μ / α) ^ (2 / q)) ^ (1 / a)
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) (2 * K / (L * Metric.diam C ^ 2))⌋ + 2) 1
      ∀ t : ℕ, 1 ≤ t →
        ((t : ℤ) < t₀ → f (x t) - f xStar ≤ L * Metric.diam C ^ 2 / 2 * (1 / 2) ^ (t - 1)) ∧
        (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤ K / (1 + a / 2 * ((t : ℝ) - t₀)) ^ (1 / a))

/-- **Lemma 3.2** (stability of linear maximizers). Let `C` be `(α, q)`-uniformly convex with
`α > 0` and `q ≥ 2`, let `φ₁, φ₂` be continuous linear functionals that are not both zero, and let
`v₁, v₂ ∈ C` maximize `φ₁` and `φ₂` over `C`. Then
`φ₁(v₁ - v₂) ≤ (1/α)^{1/(q-1)} ‖φ₁ - φ₂‖^{1 + 1/(q-1)}/max {‖φ₁‖, ‖φ₂‖}^{1/(q-1)}`. -/
def MaximizerStability : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (α q : ℝ)
    (φ₁ φ₂ : StrongDual ℝ E) (v₁ v₂ : E), IsUniformlyConvexSet C α q → 0 < α → 2 ≤ q →
    0 < max ‖φ₁‖ ‖φ₂‖ → v₁ ∈ C → (∀ y ∈ C, φ₁ y ≤ φ₁ v₁) → v₂ ∈ C → (∀ y ∈ C, φ₂ y ≤ φ₂ v₂) →
      φ₁ (v₁ - v₂) ≤ (1 / α) ^ (1 / (q - 1)) * ‖φ₁ - φ₂‖ ^ (1 + 1 / (q - 1)) /
        (max ‖φ₁‖ ‖φ₂‖) ^ (1 / (q - 1))

/-- **Follow the leader** for online linear optimization over `C` with losses `c_1, c_2, …`: for
`t ≥ 1`, the action `x_t ∈ C` minimizes the sum `c_1 + ⋯ + c_{t-1}` of the losses observed before
time `t` over `C`, with any tie-breaking. -/
def IsFTL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (c : ℕ → StrongDual ℝ E) (x : ℕ → E) : Prop :=
  ∀ t : ℕ, 1 ≤ t → x t ∈ C ∧
    ∀ y ∈ C, (∑ τ ∈ Finset.Ico 1 t, c τ) (x t) ≤ (∑ τ ∈ Finset.Ico 1 t, c τ) y

/-- **Theorem 3.1** (regret of follow the leader over uniformly convex sets). Let `C` be
`(α, q)`-uniformly convex with `α > 0` and `q ≥ 2`, let the losses satisfy `‖c_t‖ ≤ M`, and let
their averages `(c_1 + ⋯ + c_t)/t` have norm at least `L > 0` for `1 ≤ t ≤ T`. Every run of follow
the leader has regret `∑_{t ≤ T} c_t(x_t - u)` against every `u ∈ C` at most
`2M (2M/(α L))^{1/(q-1)} ((q-1)/(q-2)) T^{1-1/(q-1)}` for `q > 2` and `(4M²/(α L))(1 + log T)` for
`q = 2`. -/
def FTLRegret : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (α q M L : ℝ)
    (c : ℕ → StrongDual ℝ E) (x : ℕ → E) (T : ℕ), IsUniformlyConvexSet C α q → 0 < α →
    2 ≤ q → 0 < L → (∀ t, ‖c t‖ ≤ M) →
    (∀ t, 1 ≤ t → t ≤ T → L ≤ ‖(1 / (t : ℝ)) • ∑ τ ∈ Finset.Icc 1 t, c τ‖) → IsFTL C c x →
    ∀ u ∈ C,
      (2 < q → ∑ t ∈ Finset.Icc 1 T, c t (x t - u) ≤
        2 * M * (2 * M / (α * L)) ^ (1 / (q - 1)) * ((q - 1) / (q - 2)) *
          (T : ℝ) ^ (1 - 1 / (q - 1))) ∧
      (q = 2 → ∑ t ∈ Finset.Icc 1 T, c t (x t - u) ≤ 4 * M ^ 2 / (α * L) * (1 + Real.log T))

/-- **Lemma 2.7** (distance to the Frank–Wolfe vertex). Let `C` be convex, `f` convex over `C`
and differentiable at its points with `L`-Lipschitz derivative on `C` and `‖f'(y)‖ ≥ c > 0` on
`C`, and let the local scaling inequality hold at `x⋆ ∈ C` with `α > 0` and `q ≥ 2`. For `x ∈ C`
with `f(x) - f(x⋆) ≤ 1` and a Frank–Wolfe vertex `v` of `x`,
`‖x - v‖ ≤ H (f(x) - f(x⋆))^{1/(q(q-1))}` with
`H = 2 max {(2L/(cα))^{1/(q-1)} (2/(cα))^{1/(q(q-1))}, (2/(cα))^{1/q}}`. -/
def FWVertexDistance : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (L c α q : ℝ) (xStar x v : E), ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) →
    0 ≤ L → (∀ y ∈ C, ∀ z ∈ C, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) → 0 < c →
    (∀ y ∈ C, c ≤ ‖fderiv ℝ f y‖) → 0 < α → 2 ≤ q → xStar ∈ C → IsLocalScaling C f α q xStar →
    x ∈ C → f x - f xStar ≤ 1 → v ∈ C → (∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) →
      ‖x - v‖ ≤ 2 * max ((2 * L / (c * α)) ^ (1 / (q - 1)) * (2 / (c * α)) ^ (1 / (q * (q - 1))))
        ((2 / (c * α)) ^ (1 / q)) * (f x - f xStar) ^ (1 / (q * (q - 1)))

/-- **Theorem 2.5** (rates under the local scaling inequality), corrected. Let `C` be compact and
convex, `f` convex and `L`-smooth with `L > 0` and `‖f'(y)‖ ≥ c > 0` on `C`, and let the local
scaling inequality hold at a minimizer `x⋆` with `α > 0` and `q ≥ 2`. Let `H` be the constant of
Lemma 2.7 and `a = 1 - 2/(q(q-1))`. Every short-step run with `f(x_S) - f(x⋆) ≤ 1` satisfies
`h_{t+1} ≤ h_t max {1/2, 1 - h_t^a/(2LH²)}` for `t ≥ S`, where `h_t = f(x_t) - f(x⋆)`. Hence for
`q = 2` (`a = 0`) the convergence is linear with factor `max {1/2, 1 - 1/(2LH²)}` from `S` on, and
for `q > 2`, with `K = (LH²)^{1/a}` and `t₀ = max {⌊log_{1/2} K⌋ + 2, 1}`,
`h_{S+T-1} ≤ 2^{1-T}` for `1 ≤ T < t₀` and `h_{S+T-1} ≤ K/(1 + a(T - t₀)/2)^{1/a}` for `T ≥ t₀`:
the rate `O(t^{-1/(1-2/(q(q-1)))})`. -/
def LocalScalingRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (L : NNReal)
    (c α q : ℝ) (x v : ℕ → E) (γ : ℕ → ℝ) (xStar : E) (S : ℕ),
    IsCompact C → Convex ℝ C → 0 < (L : ℝ) → ConvexOn ℝ Set.univ f → IsSmooth f L → 0 < c →
    (∀ y ∈ C, c ≤ ‖fderiv ℝ f y‖) → 0 < α → 2 ≤ q → xStar ∈ minimizers C f →
    IsLocalScaling C f α q xStar → IsShortStepRun C f L x v γ → f (x S) - f xStar ≤ 1 →
    let H := 2 * max ((2 * L / (c * α)) ^ (1 / (q - 1)) * (2 / (c * α)) ^ (1 / (q * (q - 1))))
      ((2 / (c * α)) ^ (1 / q))
    let a := 1 - 2 / (q * (q - 1))
    (∀ t : ℕ, S ≤ t → f (x (t + 1)) - f xStar ≤
      (f (x t) - f xStar) * max (1 / 2) (1 - (f (x t) - f xStar) ^ a / (2 * L * H ^ 2))) ∧
    (q = 2 → ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max (1 / 2) (1 - 1 / (2 * L * H ^ 2)) ^ (t - S) * (f (x S) - f xStar)) ∧
    (2 < q →
      let K := ((L : ℝ) * H ^ 2) ^ (1 / a)
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) K⌋ + 2) 1
      ∀ T : ℕ, 1 ≤ T →
        ((T : ℤ) < t₀ → f (x (S + T - 1)) - f xStar ≤ (1 / 2) ^ (T - 1)) ∧
        (t₀ ≤ (T : ℤ) → f (x (S + T - 1)) - f xStar ≤ K / (1 + a / 2 * ((T : ℝ) - t₀)) ^ (1 / a)))

/-- The **modulus of convexity** of a real normed space (Definition 4.1): `δ(ε)` is the infimum of
`1 - ‖(x + y)/2‖` over `x, y` in the closed unit ball with `‖x - y‖ ≥ ε`. -/
noncomputable def modulusOfConvexity (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ ε ≤ ‖x - y‖ ∧ r = 1 - ‖(1 / 2 : ℝ) • (x + y)‖}

/-- **Lemma 4.2** (unit balls of uniformly convex spaces). If the modulus of convexity of `E`
satisfies `δ(ε) ≥ α ε^q` for `ε ∈ [0, 2]` with `α ≥ 0`, the closed unit ball is
`(α, q)`-uniformly convex. If the closed unit ball is `(α, q)`-uniformly convex, the closed ball of
radius `r > 0` is `(α/r^{q-1}, q)`-uniformly convex. -/
def UniformlyConvexBall : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (α q : ℝ),
    (0 ≤ α → (∀ ε ∈ Set.Icc (0 : ℝ) 2, α * ε ^ q ≤ modulusOfConvexity E ε) →
      IsUniformlyConvexSet (Metric.closedBall (0 : E) 1) α q) ∧
    ∀ r : ℝ, 0 < r → IsUniformlyConvexSet (Metric.closedBall (0 : E) 1) α q →
      IsUniformlyConvexSet (Metric.closedBall (0 : E) r) (α / r ^ (q - 1)) q

/-- **No super-quadratic uniform convexity with smoothness.** On a real normed space with a nonzero
vector, no `L`-smooth function is `(μ, r)`-uniformly convex,
`f(y) ≥ f(x) + f'(x)(y - x) + (μ/2)‖x - y‖^r` for all `x, y`, with `μ > 0` and `r > 2`; so the
exponent in Lemma D.2 is `2`. -/
def SmoothUniformlyConvexExponent : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal) (μ r : ℝ),
    (∃ e : E, e ≠ 0) → IsSmooth f L → 0 < μ →
    (∀ x y, f x + fderiv ℝ f x (y - x) + μ / 2 * ‖x - y‖ ^ r ≤ f y) → r ≤ 2

/-- **Lemma D.2** (sublevel sets of uniformly convex functions), corrected. Let `f ≥ 0` be
`L`-smooth with `L > 0` and `(μ, r)`-uniformly convex on `E`, with `μ > 0` and `r ≥ 2`. For
`w > 0`, the sublevel set `{f ≤ w}` is `(μ/(2√(2wL)), r)`-uniformly convex. -/
def SublevelUniformlyConvex : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (L : NNReal) (μ r w : ℝ),
    (∀ x, 0 ≤ f x) → IsSmooth f L → 0 < (L : ℝ) → 0 < μ → 2 ≤ r →
    (∀ x y, f x + fderiv ℝ f x (y - x) + μ / 2 * ‖x - y‖ ^ r ≤ f y) → 0 < w →
    IsUniformlyConvexSet {x | f x ≤ w} (μ / (2 * Real.sqrt (2 * w * L))) r

/-- **Lemma D.3** (norm balls), corrected. If `x ↦ ‖x‖²` is `(μ, s)`-uniformly convex,
`‖y‖² ≥ ‖x‖² + φ_x(y - x) + (μ/2)‖x - y‖^s` for all `x, y` with `φ_x` its derivative, with `μ > 0`
and `s ≥ 2`, then the closed ball of radius `ρ > 0` is `(μ/(4ρ), s)`-uniformly convex. -/
def NormBallUniformlyConvex : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ s ρ : ℝ), 0 < μ → 2 ≤ s → 0 < ρ →
    (∀ x y : E, ‖x‖ ^ 2 + fderiv ℝ (fun v : E => ‖v‖ ^ 2) x (y - x) + μ / 2 * ‖x - y‖ ^ s ≤
      ‖y‖ ^ 2) →
    IsUniformlyConvexSet (Metric.closedBall (0 : E) ρ) (μ / (4 * ρ)) s

/-- **The constants of Lemmas D.2 and D.3 as printed are too large.** The closed Euclidean unit disk
is not `(1, 2)`-uniformly convex, although Lemma D.2 for `f = ‖x‖²/2` with `μ = L = 1` and
`w = 1/2`, and Lemma D.3 for the Euclidean norm with `μ = 2` and `ρ = 1`, claim it is. -/
def EuclideanDiskNotUC : Prop :=
  ¬ IsUniformlyConvexSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) 1 2

end Lemmata.FWUniformlyConvex
