module

public import Lemmata.FrankWolfeLDS.Proof.AnalyticFacts
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# From Mathlib's smoothness and convexity to the predicates of the proofs

The proofs work with an abstract gradient map `f'` and two inequalities,
`IsLipschitzSmoothUpperBound f L f'` and `IsFirstOrderConvex f f'`. The statements assume
instead what the paper does, in Mathlib's terms: `f` is differentiable, convex, and its
gradient `∇ f` is `L`-Lipschitz. This file derives the former from the latter:
the descent lemma (`lipschitzSmooth_of_lipschitzWith`, ported from the `feat/lipschitz-smooth`
branch of the original development) and the first-order characterization of convexity.
-/

namespace Lemmata.FrankWolfeLDS

open scoped Gradient NNReal
open InnerProductSpace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A differentiable function `f : E → ℝ` is `L`-smooth if it satisfies the quadratic
upper bound `f y ≤ f x + ⟨∇f x, y - x⟩ + (L/2) ‖y - x‖²` for all `x y : E`.

Note: the definition is well-formed even without `Differentiable ℝ f`, since `∇ f x`
returns zero at non-differentiable points. The useful content requires differentiability,
which is stated separately in theorems that need it. -/
def LipschitzSmooth (L : ℝ≥0) (f : E → ℝ) : Prop :=
  ∀ x y, f y ≤ f x + ⟪∇ f x, y - x⟫_ℝ + ↑L / 2 * ‖y - x‖ ^ 2

/-- The function `t ↦ f(x + t(y-x))` has derivative `⟨∇f(x + t(y-x)), y-x⟩` at every `t`. -/
theorem hasDerivAt_along_segment
    {f : E → ℝ} (hf : Differentiable ℝ f) (x y : E) (t : ℝ) :
    HasDerivAt (fun s => f (x + s • (y - x))) ⟪∇ f (x + t • (y - x)), y - x⟫_ℝ t := by
  have hpath : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
    have h1 : HasDerivAt (fun s : ℝ => s • (y - x)) (y - x) t := by
      simpa [id, one_smul] using (hasDerivAt_id t).smul_const (y - x)
    have h2 := (hasDerivAt_const t x).add h1
    simp only [zero_add] at h2; exact h2
  have hcomp :=
    (hf (x + t • (y - x))).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hpath
  simp only [toDual_apply_apply] at hcomp
  exact hcomp

/-!
### Core integration argument

Both A→B and C→B reduce to establishing:
1. integrability of `t ↦ ⟨∇f(x + t(y-x)), y-x⟩` on `[0,1]`
2. a pointwise bound `⟨∇f(x + t(y-x)) - ∇f x, y-x⟩ ≤ L·t·‖y-x‖²` on `[0,1]`

The shared FTC + integration machinery lives in `lipschitzSmooth_of_pointwiseBound`.
-/

private lemma lipschitzSmooth_of_pointwiseBound {f : E → ℝ} {L : ℝ≥0}
    (hf : Differentiable ℝ f)
    (hint : ∀ x y : E,
        IntervalIntegrable (fun t => ⟪∇ f (x + t • (y - x)), y - x⟫_ℝ) volume 0 1)
    (hptwise : ∀ x y : E, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ⟪∇ f (x + t • (y - x)) - ∇ f x, y - x⟫_ℝ ≤ ↑L * t * ‖y - x‖ ^ 2) :
    LipschitzSmooth L f := by
  intro x y
  -- FTC: f y - f x = ∫₀¹ ⟪∇f(x + t(y-x)), y-x⟫ dt
  have hftc : f y - f x = ∫ t in (0 : ℝ)..1, ⟪∇ f (x + t • (y - x)), y - x⟫_ℝ := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_along_segment hf x y t) (hint x y)
    simp only [one_smul, zero_smul, add_zero] at heq
    have hy : x + (y - x) = y := by abel
    rw [hy] at heq; linarith
  -- Integrabilities
  have hint2 : IntervalIntegrable (fun t => ↑L * t * ‖y - x‖ ^ 2) volume 0 1 :=
    ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hint3 : IntervalIntegrable
      (fun t => ⟪∇ f (x + t • (y - x)) - ∇ f x, y - x⟫_ℝ) volume 0 1 := by
    have heq : (fun t : ℝ => ⟪∇ f (x + t • (y - x)) - ∇ f x, y - x⟫_ℝ) =
        fun t : ℝ => ⟪∇ f (x + t • (y - x)), y - x⟫_ℝ - ⟪∇ f x, y - x⟫_ℝ := by
      funext t; rw [inner_sub_left]
    rw [heq]; exact (hint x y).sub (continuous_const.intervalIntegrable 0 1)
  -- Integrate the pointwise bound
  have hmono : ∫ t in (0 : ℝ)..1, ⟪∇ f (x + t • (y - x)) - ∇ f x, y - x⟫_ℝ ≤
      ∫ t in (0 : ℝ)..1, ↑L * t * ‖y - x‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) hint3 hint2 (hptwise x y)
  -- ∫₀¹ L·t·‖y-x‖² = L/2·‖y-x‖²
  have hcompute : ∫ t in (0 : ℝ)..1, ↑L * t * ‖y - x‖ ^ 2 = ↑L / 2 * ‖y - x‖ ^ 2 := by
    have h : ∫ t in (0 : ℝ)..1, ↑L * t * ‖y - x‖ ^ 2 =
        ↑L * ‖y - x‖ ^ 2 * ∫ t in (0 : ℝ)..1, t := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; ext t; ring
    rw [h, integral_id]; ring
  -- Second FTC: identify ∫⟨∇f(γt)-∇fx, y-x⟩ = (fy-fx) - ⟨∇fx, y-x⟩
  have hkey : ∫ t in (0 : ℝ)..1, ⟪∇ f (x + t • (y - x)) - ∇ f x, y - x⟫_ℝ =
      (f y - f x) - ⟪∇ f x, y - x⟫_ℝ := by
    let φ : ℝ → ℝ := fun s => f (x + s • (y - x)) - ⟪∇ f x, y - x⟫_ℝ * s
    have hφd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt φ ⟪∇ f (x + t • (y - x)) - ∇ f x, y - x⟫_ℝ t := by
      intro t _
      have hd2 : HasDerivAt (fun s : ℝ => ⟪∇ f x, y - x⟫_ℝ * s) ⟪∇ f x, y - x⟫_ℝ t := by
        have := (hasDerivAt_id t).const_mul ⟪∇ f x, y - x⟫_ℝ
        simp only [mul_one, id] at this; exact this
      have hd3 := (hasDerivAt_along_segment hf x y t).sub hd2
      rwa [← inner_sub_left] at hd3
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hφd hint3
    have hφ1 : φ 1 = f y - ⟪∇ f x, y - x⟫_ℝ := by
      show f (x + 1 • (y - x)) - ⟪∇ f x, y - x⟫_ℝ * 1 = f y - ⟪∇ f x, y - x⟫_ℝ
      simp only [one_smul, mul_one]; congr 1; abel_nf
    have hφ0 : φ 0 = f x := by simp [φ]
    linarith
  -- Conclude: (fy - fx) - ⟨∇fx, y-x⟩ ≤ L/2·‖y-x‖²
  have hfinal : (f y - f x) - ⟪∇ f x, y - x⟫_ℝ ≤ ↑L / 2 * ‖y - x‖ ^ 2 := by
    rw [← hkey]; exact hmono.trans_eq hcompute
  linarith

/-! ### Main theorems -/

/-- **A → B. Descent lemma.** If `f` has an `L`-Lipschitz gradient then `f` is `L`-smooth.
Holds without convexity, via FTC along the segment from `x` to `y`. -/
theorem lipschitzSmooth_of_lipschitzWith
    {f : E → ℝ} {L : ℝ≥0}
    (hf : Differentiable ℝ f) (hL : LipschitzWith L (∇ f)) :
    LipschitzSmooth L f :=
  lipschitzSmooth_of_pointwiseBound hf
    (fun x y => by
      have hγcont : Continuous (fun t : ℝ => x + t • (y - x)) := by fun_prop
      exact ((hL.continuous.comp hγcont).inner continuous_const).intervalIntegrable 0 1)
    (fun x y t ht => by
      have ht0 : 0 ≤ t := ht.1
      have hcs := real_inner_le_norm (∇ f (x + t • (y - x)) - ∇ f x) (y - x)
      have hlip := hL.dist_le_mul (x + t • (y - x)) x
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg ht0] at hlip
      calc ⟪∇ f (x + t • (y - x)) - ∇ f x, y - x⟫_ℝ
          ≤ ‖∇ f (x + t • (y - x)) - ∇ f x‖ * ‖y - x‖ := hcs
        _ ≤ (↑L * (t * ‖y - x‖)) * ‖y - x‖ :=
            mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
        _ = ↑L * t * ‖y - x‖ ^ 2 := by ring)

/-- A differentiable function with `L`-Lipschitz gradient satisfies the quadratic upper bound
with the gradient map `∇ f`. -/
theorem isLipschitzSmoothUpperBound_of_lipschitzWith {f : E → ℝ} {L : ℝ≥0}
    (hf : Differentiable ℝ f) (hL : LipschitzWith L (∇ f)) :
    IsLipschitzSmoothUpperBound f L (∇ f) :=
  lipschitzSmooth_of_lipschitzWith hf hL

/-- A differentiable convex function satisfies the first-order inequality with `∇ f`. -/
theorem isFirstOrderConvex_of_convexOn {f : E → ℝ} (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) :
    IsFirstOrderConvex f (∇ f) :=
  IsFirstOrderConvex.of_convexOn_hasGradientAt hconv fun x => (hf x).hasGradientAt

end Lemmata.FrankWolfeLDS
