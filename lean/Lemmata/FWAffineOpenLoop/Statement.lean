module

public import Lemmata.FWOpenLoop.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FrankWolfe Lemmata.FWOpenLoop

universe u

/-- The Bregman divergence `D_f(y, x) = f(y) - f(x) - f'(x)(y - x)`. -/
noncomputable def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (y x : E) : ℝ :=
  f y - f x - fderiv ℝ f x (y - x)

/-- The **strong `(M, r)`-growth property** of `(C, f)`: for every `x ∈ C`, every Frank–Wolfe
vertex `v ∈ argmin_{y ∈ C} f'(x)(y)` and every `η ∈ [0, 1]`,
`D_f(x + η(v - x), x) ≤ (M η²/2) g(x)^r`, where `g(x) = f'(x)(x - v)` is the Frank–Wolfe gap. -/
def IsStrongGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M r : ℝ) : Prop :=
  ∀ x ∈ C, ∀ v ∈ C, (∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) → ∀ η ∈ Set.Icc (0 : ℝ) 1,
    bregman f (x + η • (v - x)) x ≤ M * η ^ 2 / 2 * fderiv ℝ f x (x - v) ^ r

/-- The **best duality gap** `min_{k ≤ t} (f(x_t) - f(x_k) + g_k)` of a run, where
`g_k = f'(x_k)(x_k - v_k)` is the Frank–Wolfe gap of iteration `k`. -/
noncomputable def pdGap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (x v : ℕ → E) (t : ℕ) : ℝ :=
  (Finset.range (t + 1)).inf' Finset.nonempty_range_add_one
    fun k => f (x t) - f (x k) + fderiv ℝ f (x k) (x k - v k)

/-- The smallest Frank–Wolfe gap `min_{k ≤ t} g_k` among the first `t + 1` iterations. -/
noncomputable def minGap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (x v : ℕ → E) (t : ℕ) : ℝ :=
  (Finset.range (t + 1)).inf' Finset.nonempty_range_add_one fun k => fderiv ℝ f (x k) (x k - v k)

/-- The **weak `(M, r)`-growth property** of `(C, f)`: for every `x ∈ C`, every Frank–Wolfe vertex
`v`, every minimizer `x⋆` and every `η ∈ [0, 1]`,
`D_f(x + η(v - x), x) (f(x) - f(x⋆))^{1-r} ≤ (M η²/2) g(x)`. -/
def IsWeakGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M r : ℝ) : Prop :=
  ∀ x ∈ C, ∀ v ∈ C, (∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) → ∀ xStar ∈ minimizers C f,
    ∀ η ∈ Set.Icc (0 : ℝ) 1,
      bregman f (x + η • (v - x)) x * (f x - f xStar) ^ (1 - r) ≤
        M * η ^ 2 / 2 * fderiv ℝ f x (x - v)

/-- The **gaps `(m, r)`-growth property** of `(C, f)`: `m (f(x) - f(x⋆))^{1-r} ≤ g(x)` for every
`x ∈ C`, every Frank–Wolfe vertex `v` and every minimizer `x⋆`. -/
def IsGapsGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (m r : ℝ) : Prop :=
  ∀ x ∈ C, ∀ v ∈ C, (∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) → ∀ xStar ∈ minimizers C f,
    m * (f x - f xStar) ^ (1 - r) ≤ fderiv ℝ f x (x - v)

/-- The **relaxed gaps growth property** of a run from the threshold `S` on: for every `t ≥ S` and
every minimizer `x⋆`, either `f(x_t) - f(x⋆) < δ_t` or `m (f(x_t) - f(x⋆))^{1-r} ≤ g_t`. -/
def IsRelaxedGapsGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (f : E → ℝ) (x v : ℕ → E) (δ : ℕ → ℝ) (m r : ℝ) (S : ℕ) : Prop :=
  ∀ t, S ≤ t → ∀ xStar ∈ minimizers C f,
    f (x t) - f xStar < δ t ∨ m * (f (x t) - f xStar) ^ (1 - r) ≤ fderiv ℝ f (x t) (x t - v t)

/-- **Theorem 3.1** (strong `(M, 0)`-growth). Let `C` be convex and `(C, f)` have the strong
`(M, 0)`-growth property with `M ≥ 0`, and let `ℓ ≥ 2`. Every Frank–Wolfe run with the step sizes
`η_t = ℓ/(t + ℓ)` has best duality gap at most `η_t M` for all `t ≥ 1`. -/
def PDRateStrongZero : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (M : ℝ)
    (ℓ : ℕ) (x v : ℕ → E), Convex ℝ C → 0 ≤ M → 2 ≤ ℓ → IsStrongGrowth C f M 0 →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t) →
    ∀ t : ℕ, 1 ≤ t → pdGap f x v t ≤ eta ℓ t * M

/-- **Lemma 3.3** (telescoping the step sizes). For `ℓ ≥ 1` and `1 ≤ S ≤ t`,
`∏_{i=S}^{t} (1 - η_i) ≤ (η_t/η_{S-1})^ℓ` with `η_t = ℓ/(t + ℓ)`. -/
def ProductBound : Prop :=
  ∀ ℓ S t : ℕ, 1 ≤ ℓ → 1 ≤ S → S ≤ t →
    ∏ i ∈ Finset.Icc S t, (1 - eta ℓ i) ≤ (eta ℓ t / eta ℓ ((S : ℤ) - 1)) ^ ℓ

/-- **Lemma 3.5** (telescoping with a margin). For `ℓ ≥ 1`, `1 ≤ S ≤ t` and `ε ∈ [0, ℓ]`,
`∏_{i=S}^{t} (1 - (1 - ε/ℓ) η_i) ≤ (η_t/η_{S-1})^{ℓ-ε} exp(εℓ/S)`. -/
def ProductBoundEps : Prop :=
  ∀ (ℓ S t : ℕ) (ε : ℝ), 1 ≤ ℓ → 1 ≤ S → S ≤ t → ε ∈ Set.Icc (0 : ℝ) ℓ →
    ∏ i ∈ Finset.Icc S t, (1 - (1 - ε / ℓ) * eta ℓ i) ≤
      (eta ℓ t / eta ℓ ((S : ℤ) - 1)) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / S)

/-- **Theorem 3.2** (strong `(M, 1)`-growth). Let `C` be convex, `f` convex over `C` and
differentiable at its points with a minimizer, `(C, f)` with the strong `(M, 1)`-growth property,
`M > 0`, `ℓ ≥ 1`, and `S = max {1, ⌈ℓM/2 - ℓ⌉}`. Every Frank–Wolfe run with `η_t = ℓ/(t + ℓ)`
satisfies `pd_t ≤ pd_S (η_{t-1}/η_{S-1})^ℓ exp(Mℓ²/(2S))` for `t ≥ S`. Moreover, for
`ε ∈ (0, 1)`, `R₀ = max {S, ⌈ℓM/(2(1 - ε)) - ℓ⌉}` and every `t` with
`e^{1/ℓ} (R₀ + ℓ) ≤ t + ℓ`, the smallest Frank–Wolfe gap so far is at most
`pd_S (η_{t-1}/η_{S-1})^ℓ exp(3 + Mℓ²/(2S))/ε`. -/
def PDRateStrongOne : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (M : ℝ)
    (ℓ : ℕ) (x v : ℕ → E) (xStar : E), ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) →
    xStar ∈ minimizers C f → 0 < M → 1 ≤ ℓ → IsStrongGrowth C f M 1 →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t) →
    let S := max 1 ⌈(ℓ : ℝ) * M / 2 - ℓ⌉₊
    (∀ t : ℕ, S ≤ t → pdGap f x v t ≤ pdGap f x v S *
      (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ * Real.exp (M * ℓ ^ 2 / (2 * S))) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ t : ℕ,
      Real.exp (1 / ℓ) * ((max S ⌈(ℓ : ℝ) * M / (2 * (1 - ε)) - ℓ⌉₊ : ℕ) + ℓ) ≤ t + ℓ →
      minGap f x v t ≤ pdGap f x v S * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ *
        Real.exp (3 + M * ℓ ^ 2 / (2 * S)) / ε)

/-- **Theorem 3.4** (strong `(M, r)`-growth, `r ∈ [0, 1)`). Let `C` be convex, `f` convex over
`C` and differentiable at its points with a minimizer, `(C, f)` with the strong `(M, r)`-growth
property, `M > 0`, `ℓ ≥ 1`, `ε ∈ (0, ℓ)` and `k = min {ℓ - ε, 1/(1 - r)}`. Every Frank–Wolfe run
with `η_t = ℓ/(t + ℓ)` satisfies, for `t ≥ 1`,
`pd_t ≤ exp(εℓ) max {η_{t-1}^{ℓ-ε} pd_1, η_{t-1}^k (ℓM/(2ε))^{1/(1-r)}}`, and, for
`t ≥ ⌈e^{1/k}(1 + ℓ) - ℓ⌉`, the smallest Frank–Wolfe gap so far is at most
`exp(3 + εℓ) η_{t-1}^k max {pd_1, (ℓM/(2ε))^{1/(1-r)}}`. The paper has `M/2` in place of `pd_1`;
under strong `(M, 0)`-growth, `pd_1 ≤ M/2`. -/
def PDRateStrong : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M r ε : ℝ) (ℓ : ℕ) (x v : ℕ → E) (xStar : E), ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f → 0 < M → 1 ≤ ℓ →
    r ∈ Set.Ico (0 : ℝ) 1 → ε ∈ Set.Ioo (0 : ℝ) ℓ → IsStrongGrowth C f M r →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t) →
    let k := min ((ℓ : ℝ) - ε) (1 / (1 - r))
    (∀ t : ℕ, 1 ≤ t → pdGap f x v t ≤ Real.exp (ε * ℓ) *
      max (eta ℓ ((t : ℤ) - 1) ^ ((ℓ : ℝ) - ε) * pdGap f x v 1)
        (eta ℓ ((t : ℤ) - 1) ^ k * (ℓ * M / (2 * ε)) ^ (1 / (1 - r)))) ∧
    (∀ t : ℕ, ⌈Real.exp (1 / k) * (1 + ℓ) - ℓ⌉₊ ≤ t →
      minGap f x v t ≤ Real.exp (3 + ε * ℓ) * eta ℓ ((t : ℤ) - 1) ^ k *
        max (pdGap f x v 1) ((ℓ * M / (2 * ε)) ^ (1 / (1 - r))))

/-- **Theorem 4.1** (strong `(M, 0)`- and weak `(M, r)`-growth). Let `f` be convex over `C` and
differentiable at its points with a minimizer `x⋆`, `(C, f)` with the strong `(M, 0)`- and weak
`(M, r)`-growth properties, `M > 0`, `r ∈ [0, 1)`, `ℓ ≥ 1` and `ε ∈ (0, ℓ)`. Every Frank–Wolfe run
with `η_t = ℓ/(t + ℓ)` satisfies, for all `t ≥ 1`,
`h_t ≤ exp(εℓ) max {η_{t-1}^{ℓ-ε} M/2,
η_{t-1}^{min {ℓ-ε, 1/(1-r), 2}} ((ℓM/(2ε))^{1/(1-r)} + M/2)}`.
Moreover, either `h_t ≤ (η_t ℓM/(2ε))^{1/(1-r)}` for infinitely many `t`, or there is `R ≥ 1` with
`h_t ≤ h_R (η_{t-1}/η_{R-1})^{ℓ-ε} exp(εℓ/R)` for all `t ≥ R + 1`. -/
def WeakRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M r ε : ℝ) (ℓ : ℕ) (x v : ℕ → E) (xStar : E), ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f → 0 < M → 1 ≤ ℓ →
    r ∈ Set.Ico (0 : ℝ) 1 → ε ∈ Set.Ioo (0 : ℝ) ℓ → IsStrongGrowth C f M 0 →
    IsWeakGrowth C f M r → IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t) →
    (∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤ Real.exp (ε * ℓ) *
      max (eta ℓ ((t : ℤ) - 1) ^ ((ℓ : ℝ) - ε) * (M / 2))
        (eta ℓ ((t : ℤ) - 1) ^ (min ((ℓ : ℝ) - ε) (min (1 / (1 - r)) 2)) *
          ((ℓ * M / (2 * ε)) ^ (1 / (1 - r)) + M / 2))) ∧
    ((∀ T : ℕ, ∃ t, T ≤ t ∧ f (x t) - f xStar ≤ (eta ℓ t * ℓ * M / (2 * ε)) ^ (1 / (1 - r))) ∨
      ∃ R : ℕ, 1 ≤ R ∧ ∀ t : ℕ, R + 1 ≤ t → f (x t) - f xStar ≤ (f (x R) - f xStar) *
        (eta ℓ ((t : ℤ) - 1) / eta ℓ ((R : ℤ) - 1)) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / R))

/-- **Lemma 4.2** (the next fast iterate). Under weak `(M, r)`-growth with `ℓ > 1/(1 - r)` and
`ε ∈ (0, ℓ - 1/(1 - r))`, for every `R ≥ 1` some `i` with `R ≤ i ≤ max {R, U}` satisfies
`h_i ≤ (η_i ℓM/(2ε))^{1/(1-r)}`, where
`U = ⌈ℓ (h_R η_R^{ε-ℓ} (2ε/(ℓM))^{1/(1-r)} exp(εℓ/R))^{1/(ℓ-ε-1/(1-r))} - ℓ⌉`. -/
def WeakRestart : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M r ε : ℝ) (ℓ : ℕ) (x v : ℕ → E) (xStar : E), ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f → 0 < M → 1 ≤ ℓ →
    r ∈ Set.Ico (0 : ℝ) 1 → 1 / (1 - r) < ℓ → ε ∈ Set.Ioo (0 : ℝ) (ℓ - 1 / (1 - r)) →
    IsWeakGrowth C f M r → IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t) →
    ∀ R : ℕ, 1 ≤ R →
      ∃ i, R ≤ i ∧ i ≤ max R ⌈ℓ * ((f (x R) - f xStar) * eta ℓ R ^ (ε - ℓ) *
          (2 * ε / (ℓ * M)) ^ (1 / (1 - r)) * Real.exp (ε * ℓ / R)) ^
          (1 / (ℓ - ε - 1 / (1 - r))) - ℓ⌉₊ ∧
        f (x i) - f xStar ≤ (eta ℓ i * ℓ * M / (2 * ε)) ^ (1 / (1 - r))

/-- **Theorem 5.2** (strong `(M, 0)`-growth and relaxed gaps `(m, r)`-growth). Let `f` be convex
over `C` and differentiable at its points with a minimizer `x⋆`, `(C, f)` with the strong
`(M, 0)`-growth property, `M, m > 0`, `r ∈ (0, 1)`, `ℓ ≥ 2`, and let the run satisfy the relaxed
gaps growth property with `δ_t = (η_t M/m)^{1/(1-r)}` from a threshold
`S ≥ max {1, ⌈2^{1/r} ℓM/m^{1/r} - ℓ⌉}` on. Then for all `t ≥ S`,
`h_t ≤ max {h_S (η_{t-1}/η_{S-1})^ℓ, η_{t-1}^{min {ℓ, 1/(1-r), 2}} ((M/m)^{1/(1-r)} + M/2)}`. -/
def RelaxedGapsRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M m r : ℝ) (ℓ S : ℕ) (x v : ℕ → E) (xStar : E), ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f → 0 < M → 0 < m → 2 ≤ ℓ →
    r ∈ Set.Ioo (0 : ℝ) 1 → IsStrongGrowth C f M 0 →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t) →
    max 1 ⌈(2 : ℝ) ^ (1 / r) * ℓ * M / m ^ (1 / r) - ℓ⌉₊ ≤ S →
    IsRelaxedGapsGrowth C f x v (fun t => (eta ℓ t * M / m) ^ (1 / (1 - r))) m r S →
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max ((f (x S) - f xStar) * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ)
        (eta ℓ ((t : ℤ) - 1) ^ (min (ℓ : ℝ) (min (1 / (1 - r)) 2)) *
          ((M / m) ^ (1 / (1 - r)) + M / 2))

/-- **Theorem 5.1** (strong `(M, 0)`-growth and gaps `(m, r)`-growth). Under the gaps
`(m, r)`-growth property, the bound of Theorem 5.2 holds from
`S = max {1, ⌈2^{1/r} ℓM/m^{1/r} - ℓ⌉}` on. -/
def GapsRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M m r : ℝ) (ℓ : ℕ) (x v : ℕ → E) (xStar : E), ConvexOn ℝ C f →
    (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f → 0 < M → 0 < m → 2 ≤ ℓ →
    r ∈ Set.Ioo (0 : ℝ) 1 → IsStrongGrowth C f M 0 → IsGapsGrowth C f m r →
    IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t) →
    let S := max 1 ⌈(2 : ℝ) ^ (1 / r) * ℓ * M / m ^ (1 / r) - ℓ⌉₊
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max ((f (x S) - f xStar) * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ)
        (eta ℓ ((t : ℤ) - 1) ^ (min (ℓ : ℝ) (min (1 / (1 - r)) 2)) *
          ((M / m) ^ (1 / (1 - r)) + M / 2))

end Lemmata.FWAffineOpenLoop
