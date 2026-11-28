module

public import Lemmata.FWAffineOpenLoop.Statement

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWLogAdaptive

open Lemmata.FrankWolfe Lemmata.FWAffineOpenLoop

universe u

/-- The open-loop step sizes `η_t = g(t)/(t + g(t))` for a function `g : ℕ → ℝ`. -/
noncomputable def etaG (g : ℕ → ℝ) (t : ℕ) : ℝ :=
  g t / (t + g t)

/-- **Assumptions A1 and A2** on `g`: `g ≥ 2` is nondecreasing, and `t/g(t) ≤ (t + 1)/g(t + 1)`
for all `t`, which says that the step sizes `η_t` are nonincreasing. -/
def IsAdmissible (g : ℕ → ℝ) : Prop :=
  (∀ t, 2 ≤ g t) ∧ Monotone g ∧ ∀ t : ℕ, (t : ℝ) / g t ≤ ((t : ℝ) + 1) / g (t + 1)

/-- The **log-adaptive** choice `g(t) = 2 + log(t + 1)`, which gives the step sizes
`η_t = (2 + log(t + 1))/(t + 2 + log(t + 1))`. -/
noncomputable def logStep (t : ℕ) : ℝ :=
  2 + Real.log ((t : ℝ) + 1)

/-- The log-adaptive choice satisfies Assumptions A1 and A2. -/
def LogStepAdmissible : Prop :=
  IsAdmissible logStep

/-- **Lemma 3.1** (strengthened cumulative-product bound), for `ε ≤ g(S) - 1`. Let `g ≥ 2` be
nondecreasing. For integers `1 ≤ S ≤ t` and `ε ∈ (0, g(S) - 1]`,
`∏_{i=S}^t (1 - (1 - ε/g(i)) η_i) ≤ (η_t/η_{S-1})^{g(S)-ε}`. -/
def ProductBound : Prop :=
  ∀ (g : ℕ → ℝ) (S t : ℕ) (ε : ℝ), (∀ t, 2 ≤ g t) → Monotone g → 1 ≤ S → S ≤ t → 0 < ε →
    ε ≤ g S - 1 →
    ∏ i ∈ Finset.Icc S t, (1 - (1 - ε / g i) * etaG g i) ≤
      (etaG g t / etaG g (S - 1)) ^ (g S - ε)

/-- **Theorem 3.2** (strong `(M, r)`-growth). Let `f` be convex over `C` and differentiable at its
points with a minimizer `x⋆`, let `g` satisfy Assumptions A1 and A2, let `(C, f)` have the strong
`(M, r)`-growth property with `M > 0` and `r ∈ [0, 1)`, and let `S ≥ 1` and `ε ∈ (0, g(S) - 1]`.
Every Frank–Wolfe run with `η_t = g(t)/(t + g(t))` satisfies, for all `t ≥ S`,
`pd_t ≤ max {pd_S (η_{t-1}/η_{S-1})^{g(S)-ε}, (M g(t-1)/(2ε))^{1/(1-r)} η_{t-1}^k}` with
`k = min {g(S) - ε, 1/(1-r)}`. -/
def StrongRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (g : ℕ → ℝ)
    (M r ε : ℝ) (S : ℕ) (x v : ℕ → E) (xStar : E),
    ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f →
    IsAdmissible g → 0 < M → r ∈ Set.Ico (0 : ℝ) 1 → IsStrongGrowth C f M r →
    1 ≤ S → 0 < ε → ε ≤ g S - 1 → IsFWRun C (fderiv ℝ f) x v (etaG g) →
    ∀ t : ℕ, S ≤ t → pdGap f x v t ≤
      max (pdGap f x v S * (etaG g (t - 1) / etaG g (S - 1)) ^ (g S - ε))
        ((M * g (t - 1) / (2 * ε)) ^ (1 / (1 - r)) *
          etaG g (t - 1) ^ (min (g S - ε) (1 / (1 - r))))

/-- **Theorem 3.2**, the log-adaptive case. For `g(t) = 2 + log(t + 1)`, `ε = 1` and
`S = ⌈exp(1/(1-r))⌉`, every run satisfies, for all `t ≥ S`,
`pd_t ≤ max {pd_S η_{S-1}^{-1/(1-r)}, (M (2 + log t)/2)^{1/(1-r)}} ((2 + log t)/t)^{1/(1-r)}`,
which is `Õ(t^{-1/(1-r)})`. -/
def LogStrongRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M r : ℝ) (x v : ℕ → E) (xStar : E),
    ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f →
    0 < M → r ∈ Set.Ico (0 : ℝ) 1 → IsStrongGrowth C f M r →
    IsFWRun C (fderiv ℝ f) x v (etaG logStep) →
    let S := ⌈Real.exp (1 / (1 - r))⌉₊
    ∀ t : ℕ, S ≤ t → pdGap f x v t ≤
      max (pdGap f x v S / etaG logStep (S - 1) ^ (1 / (1 - r)))
          ((M * (2 + Real.log t) / 2) ^ (1 / (1 - r))) *
        ((2 + Real.log t) / t) ^ (1 / (1 - r))

/-- **Theorem 4.1** (strong `(M, 0)`-growth and weak `(M, r)`-growth). Let `f` be convex over `C`
and differentiable at its points with a minimizer `x⋆`, let `g` satisfy Assumptions A1 and A2, let
`(C, f)` have the strong `(M, 0)`- and weak `(M, r)`-growth properties with `M > 0` and
`r ∈ [0, 1)`, and let `S ≥ 1` and `ε ∈ (0, g(S) - 1]`. Every Frank–Wolfe run with
`η_t = g(t)/(t + g(t))` satisfies, for all `t ≥ S`,
`h_t ≤ max {h_S (η_{t-1}/η_{S-1})^{g(S)-ε}, ((M g(t-1)/(2ε))^{1/(1-r)} + M/2) η_{t-1}^k}` with
`k = min {g(S) - ε, 1/(1-r), 2}`. -/
def WeakRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ) (g : ℕ → ℝ)
    (M r ε : ℝ) (S : ℕ) (x v : ℕ → E) (xStar : E),
    ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f →
    IsAdmissible g → 0 < M → r ∈ Set.Ico (0 : ℝ) 1 → IsStrongGrowth C f M 0 →
    IsWeakGrowth C f M r → 1 ≤ S → 0 < ε → ε ≤ g S - 1 →
    IsFWRun C (fderiv ℝ f) x v (etaG g) →
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max ((f (x S) - f xStar) * (etaG g (t - 1) / etaG g (S - 1)) ^ (g S - ε))
        (((M * g (t - 1) / (2 * ε)) ^ (1 / (1 - r)) + M / 2) *
          etaG g (t - 1) ^ (min (g S - ε) (min (1 / (1 - r)) 2)))

/-- **Theorem 4.1**, the log-adaptive case. For `g(t) = 2 + log(t + 1)`, `ε = 1` and
`S = ⌈exp(1/(1-r))⌉`, every run satisfies, for all `t ≥ S`, with `b = min {1/(1-r), 2}`,
`h_t ≤ max {h_S η_{S-1}^{-b}, (M (2 + log t)/2)^{1/(1-r)} + M/2} ((2 + log t)/t)^b`, which is
`Õ(t^{-1/(1-r)} + t^{-2})`. -/
def LogWeakRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) (f : E → ℝ)
    (M r : ℝ) (x v : ℕ → E) (xStar : E),
    ConvexOn ℝ C f → (∀ y ∈ C, DifferentiableAt ℝ f y) → xStar ∈ minimizers C f →
    0 < M → r ∈ Set.Ico (0 : ℝ) 1 → IsStrongGrowth C f M 0 → IsWeakGrowth C f M r →
    IsFWRun C (fderiv ℝ f) x v (etaG logStep) →
    let S := ⌈Real.exp (1 / (1 - r))⌉₊
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max ((f (x S) - f xStar) / etaG logStep (S - 1) ^ (min (1 / (1 - r)) 2))
          ((M * (2 + Real.log t) / 2) ^ (1 / (1 - r)) + M / 2) *
        ((2 + Real.log t) / t) ^ (min (1 / (1 - r)) 2)

end Lemmata.FWLogAdaptive
