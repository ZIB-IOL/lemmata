module

public import Lemmata.FrankWolfeIntro.Proof

@[expose] public section

/-!
# The adaptive step-size test (Lemma 4.11)

The short step for the true smoothness constant `L` passes the test `f'(x⁺)(x - v) ≥ 0`: by the
Lipschitz derivative, `(f'(x⁺) - f'(x))(x⁺ - x) ≤ L ‖x⁺ - x‖²`.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem smooth_implies_adaptive_test : SmoothImpliesAdaptiveTest.{u} := by
  intro E _ _ f L hsm hL x v hg
  set g := fderiv ℝ f x (x - v) with hgdef
  set d := ‖v - x‖ with hd
  set γ := min (g / (L * d ^ 2)) 1 with hγ
  have hL' : (0 : ℝ) < L := hL
  rcases eq_or_lt_of_le (norm_nonneg (v - x)) with hd0 | hd0
  · -- `v = x`
    have hv : v = x := by rw [← sub_eq_zero, ← norm_eq_zero]; exact hd0.symm
    simp [hv]
  have hγ0 : 0 ≤ γ := le_min (by positivity) zero_le_one
  have hγle : γ * (L * d ^ 2) ≤ g := by
    have := min_le_left (g / (L * d ^ 2)) 1
    rw [← hγ] at this
    calc γ * (L * d ^ 2) ≤ g / (L * d ^ 2) * (L * d ^ 2) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = g := div_mul_cancel₀ g (by positivity)
  set y := x + γ • (v - x) with hy
  -- the Lipschitz bound along the step
  have hlip : ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * (γ * d) := by
    have := hsm.2.dist_le_mul y x
    rw [dist_eq_norm, dist_eq_norm, hy, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hγ0] at this
    exact this
  have hop : -(L * (γ * d) * d) ≤ (fderiv ℝ f y - fderiv ℝ f x) (x - v) := by
    have h1 := neg_abs_le ((fderiv ℝ f y - fderiv ℝ f x) (x - v))
    have h2 := (fderiv ℝ f y - fderiv ℝ f x).le_opNorm (x - v)
    rw [norm_sub_rev x v, ← hd, Real.norm_eq_abs] at h2
    have h3 := mul_le_mul_of_nonneg_right hlip (norm_nonneg (v - x))
    rw [← hd] at h3
    linarith
  have happ : (fderiv ℝ f y - fderiv ℝ f x) (x - v) = fderiv ℝ f y (x - v) - g := rfl
  rw [happ] at hop
  -- `f'(y)(x - v) ≥ g - L γ d² ≥ 0`
  nlinarith [hop, hγle]

end Proof

end Lemmata.FrankWolfeIntro
