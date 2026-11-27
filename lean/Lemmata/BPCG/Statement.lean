module

public import Lemmata.AwayStepFW.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.BPCG

open Lemmata.FrankWolfe Lemmata.AwayStepFW

universe u

open Classical in
/-- One step of blended pairwise conditional gradients (Algorithm 1) at `x` with active set `S`
and weights `lam`, away vertex `a`, local Frank–Wolfe vertex `s` and Frank–Wolfe vertex `w`. If
`f'(x)(a - s) ≥ f'(x)(x - w)`, the step moves weight `γ` from `a` to `s` with exact line search on
`[0, λ_a]` and drops `a` when its weight is used up; otherwise it is a Frank–Wolfe step toward `w`
with exact line search on `[0, 1]`. -/
def IsBPCGStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E)
    (S : Finset E) (lam : E → ℝ) (a s w x' : E) (S' : Finset E) (lam' : E → ℝ) : Prop :=
  if fderiv ℝ f x (x - w) ≤ fderiv ℝ f x (a - s) then
    ∃ γ ∈ Set.Icc (0 : ℝ) (lam a),
      (∀ σ ∈ Set.Icc (0 : ℝ) (lam a), f (x - γ • (a - s)) ≤ f (x - σ • (a - s))) ∧
      x' = x - γ • (a - s) ∧
      lam' = (fun u => lam u - (if u = a then γ else 0) + (if u = s then γ else 0)) ∧
      S' = if γ = lam a ∧ a ≠ s then S.erase a else S
  else
    ∃ γ ∈ Set.Icc (0 : ℝ) 1,
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, f (x - γ • (x - w)) ≤ f (x - σ • (x - w))) ∧
      x' = x - γ • (x - w) ∧
      lam' = (fun u => (1 - γ) * lam u + (if u = w then γ else 0)) ∧
      S' = if γ = 1 then {w} else insert w S

open Classical in
/-- A run of blended pairwise conditional gradients on `conv V`: it starts at a vertex with active
set `{x₀}` and weight `1`, and every step is a BPCG step for some away vertex and local
Frank–Wolfe vertex of the active set and some Frank–Wolfe vertex of `V`. -/
def IsBPCGRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ lam 0 = (fun u => if u = x 0 then 1 else 0) ∧
    ∀ t, ∃ a ∈ S t, (∀ u ∈ S t, fderiv ℝ f (x t) u ≤ fderiv ℝ f (x t) a) ∧
      ∃ s ∈ S t, (∀ u ∈ S t, fderiv ℝ f (x t) s ≤ fderiv ℝ f (x t) u) ∧
      ∃ w ∈ V, (∀ u ∈ V, fderiv ℝ f (x t) w ≤ fderiv ℝ f (x t) u) ∧
      IsBPCGStep f (x t) (S t) (lam t) a s w (x (t + 1)) (S (t + 1)) (lam (t + 1))

/-- **Convex rate.** For a convex `L`-smooth `f` on `conv V` with diameter `D`, every BPCG run
satisfies `f(x_T) - f(x⋆) ≤ 4 L D²/T` for `T ≥ 1`. -/
def ConvexRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (L : NNReal) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ),
    0 < (L : ℝ) → ConvexOn ℝ Set.univ f → IsSmooth f L → IsBPCGRun V f x S lam →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ T : ℕ, 1 ≤ T →
      f (x T) - f xStar ≤ 4 * L * Metric.diam (↑V : Set E) ^ 2 / T

/-- **Linear rate.** If moreover `f` is `μ`-strongly convex on `conv V` and `δ > 0` has the scaling
property of the pyramidal width, every BPCG run satisfies
`f(x_T) - f(x⋆) ≤ (f(x₀) - f(x⋆)) exp(-c T)` with `c = ½ min {1/2, μ δ²/(4 L D²)}`. -/
def LinearRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (L : NNReal) (μ δ : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ),
    0 < (L : ℝ) → 0 < μ → 0 < δ → IsScaling V δ → ConvexOn ℝ Set.univ f → IsSmooth f L →
    (∀ x ∈ convexHull ℝ (↑V : Set E), ∀ y ∈ convexHull ℝ (↑V : Set E),
      f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) →
    IsBPCGRun V f x S lam →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f, ∀ T : ℕ,
      f (x T) - f xStar ≤ (f (x 0) - f xStar) *
        Real.exp (-(1 / 2 * min (1 / 2) (μ * δ ^ 2 / (4 * L * Metric.diam (↑V : Set E) ^ 2))) * T)

open Classical in
/-- One step of lazified blended pairwise conditional gradients (Algorithm 2 of the paper) with
accuracy `J` and gap estimate `Φ`. If `f'(x)(a - s) ≥ Φ`, the step is the local pairwise step of
BPCG; otherwise, with a Frank–Wolfe vertex `w`, it is a Frank–Wolfe step if
`f'(x)(x - w) ≥ Φ/J`, and a gap step (the iterate stays and `Φ` is halved) if not. -/
def IsLazyBPCGStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E)
    (f : E → ℝ) (J : ℝ) (x : E) (S : Finset E) (lam : E → ℝ) (Φ : ℝ) (a s x' : E)
    (S' : Finset E) (lam' : E → ℝ) (Φ' : ℝ) : Prop :=
  if Φ ≤ fderiv ℝ f x (a - s) then
    (∃ γ ∈ Set.Icc (0 : ℝ) (lam a),
      (∀ σ ∈ Set.Icc (0 : ℝ) (lam a), f (x - γ • (a - s)) ≤ f (x - σ • (a - s))) ∧
      x' = x - γ • (a - s) ∧
      lam' = (fun u => lam u - (if u = a then γ else 0) + (if u = s then γ else 0)) ∧
      S' = if γ = lam a ∧ a ≠ s then S.erase a else S) ∧ Φ' = Φ
  else
    ∃ w ∈ V, (∀ u ∈ V, fderiv ℝ f x w ≤ fderiv ℝ f x u) ∧
      if Φ / J ≤ fderiv ℝ f x (x - w) then
        (∃ γ ∈ Set.Icc (0 : ℝ) 1,
          (∀ σ ∈ Set.Icc (0 : ℝ) 1, f (x - γ • (x - w)) ≤ f (x - σ • (x - w))) ∧
          x' = x - γ • (x - w) ∧
          lam' = (fun u => (1 - γ) * lam u + (if u = w then γ else 0)) ∧
          S' = if γ = 1 then {w} else insert w S) ∧ Φ' = Φ
      else x' = x ∧ S' = S ∧ lam' = lam ∧ Φ' = Φ / 2

open Classical in
/-- A run of lazified BPCG on `conv V`: it starts at a vertex with active set `{x₀}` and weight
`1`, and every step is a lazified BPCG step for some away vertex and local Frank–Wolfe vertex of
the active set. -/
def IsLazyBPCGRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E)
    (f : E → ℝ) (J : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (Φ : ℕ → ℝ) : Prop :=
  x 0 ∈ V ∧ S 0 = {x 0} ∧ lam 0 = (fun u => if u = x 0 then 1 else 0) ∧
    ∀ t, ∃ a ∈ S t, (∀ u ∈ S t, fderiv ℝ f (x t) u ≤ fderiv ℝ f (x t) a) ∧
      ∃ s ∈ S t, (∀ u ∈ S t, fderiv ℝ f (x t) s ≤ fderiv ℝ f (x t) u) ∧
      IsLazyBPCGStep V f J (x t) (S t) (lam t) (Φ t) a s (x (t + 1)) (S (t + 1)) (lam (t + 1))
        (Φ (t + 1))

/-- **Theorem 3.6, case (B)** (lazified BPCG for convex objectives), with explicit constants. Let
`f` be convex and `L`-smooth, `J ≥ 1` and `h₀/2 ≤ Φ₀ ≤ L D²/2`. Every run of lazified BPCG has
primal gap at most `ε > 0` after `⌈log₂ (Φ₀/ε)⌉₊ + 1 + 2 ⌈8 J² L D²/ε⌉₊` iterations. -/
def LazyConvexRate : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Finset E) (f : E → ℝ)
    (L : NNReal) (J : ℝ) (x : ℕ → E) (S : ℕ → Finset E) (lam : ℕ → E → ℝ) (Φ : ℕ → ℝ),
    ConvexOn ℝ Set.univ f → IsSmooth f L → 1 ≤ J → IsLazyBPCGRun V f J x S lam Φ →
    ∀ xStar ∈ minimizers (convexHull ℝ (↑V : Set E)) f,
    (f (x 0) - f xStar) / 2 ≤ Φ 0 → Φ 0 ≤ L * Metric.diam (↑V : Set E) ^ 2 / 2 →
    ∀ ε : ℝ, 0 < ε → ∀ t : ℕ,
      ⌈Real.logb 2 (Φ 0 / ε)⌉₊ + 1 + 2 * ⌈8 * J ^ 2 * L * Metric.diam (↑V : Set E) ^ 2 / ε⌉₊ ≤ t →
        f (x t) - f xStar ≤ ε

end Lemmata.BPCG
