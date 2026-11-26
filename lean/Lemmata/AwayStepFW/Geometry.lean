module

public import Lemmata.AwayStepFW.Statement
public import Lemmata.CGBasics.Smoothness

@[expose] public section

/-!
# The scaling inequality and geometric strong convexity (Lemmas 2.26 and 2.27)

The scaling condition is closed in `δ`: if `ψ(x - y) > 0`, every admissible `δ` is at most
`ψ(a - v) ‖x - y‖ / ψ(x - y)`, hence so is their supremum. Geometric strong convexity combines the
primal gap bound via strong convexity with the scaling inequality at `y = x⋆`.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isScaling_zero (V : Finset E) : IsScaling V 0 := by
  intro S hS x _ y _ ψ a ha haS v hv hvV
  rw [zero_mul]
  have : ψ v ≤ ψ a := hvV a (hS ha)
  rw [map_sub]
  exact mul_nonneg (by linarith) (norm_nonneg _)

theorem scaling_via_pyramidal_width : ScalingViaPyramidalWidth.{u} := by
  intro E _ _ V S hS x hx y hy ψ a ha haS v hv hvV
  have hne : ({δ : ℝ | 0 ≤ δ ∧ IsScaling V δ}).Nonempty := ⟨0, le_rfl, isScaling_zero V⟩
  have hR : 0 ≤ ψ (a - v) * ‖x - y‖ := by
    have : ψ v ≤ ψ a := hvV a (hS ha)
    rw [map_sub]
    exact mul_nonneg (by linarith) (norm_nonneg _)
  rcases le_or_gt (ψ (x - y)) 0 with hneg | hpos
  · have h0 : 0 ≤ pyramidalWidth V := Real.sSup_nonneg (fun δ hδ => hδ.1)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h0 hneg]
  · have hle : pyramidalWidth V ≤ ψ (a - v) * ‖x - y‖ / ψ (x - y) :=
      csSup_le hne (fun δ hδ => by
        rw [le_div_iff₀ hpos]
        have := hδ.2 S hS x hx y hy ψ a ha haS v hv hvV
        linarith)
    have := mul_le_mul_of_nonneg_right hle hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this

theorem geometric_strong_convexity : GeometricStrongConvexity.{u} := by
  intro E _ _ V f μ δ hμ hδ hsc hstrong xStar hxs S hS x hx a ha haS v hv hvV
  have hxV : x ∈ convexHull ℝ (↑V : Set E) := convexHull_mono (by exact_mod_cast hS) hx
  have hsc1 := (Lemmata.CGBasics.Proof.primal_gap_strong_convexity (convexHull ℝ (↑V : Set E)) f μ
    hμ hstrong xStar hxs x hxV).1
  have hscale := hsc S hS x hx xStar hxs.1 (fderiv ℝ f x) a ha haS v hv hvV
  set A := fderiv ℝ f x (x - xStar) with hA
  set B := fderiv ℝ f x (a - v) with hB
  have hA0 : 0 ≤ A := by
    have h1 := hstrong x hxV xStar hxs.1
    have h2 := hxs.2 x hxV
    have e : fderiv ℝ f x (xStar - x) = -A := by rw [hA, ← map_neg, neg_sub]
    rw [e] at h1
    nlinarith [sq_nonneg ‖xStar - x‖]
  rcases eq_or_lt_of_le (norm_nonneg (x - xStar)) with hd | hd
  · have hx' : x = xStar := by rw [← sub_eq_zero, ← norm_eq_zero]; exact hd.symm
    rw [hx', sub_self]
    positivity
  · set d := ‖x - xStar‖ with hdd
    have hsq : (δ * A) ^ 2 ≤ (B * d) ^ 2 := pow_le_pow_left₀ (by positivity) hscale 2
    have h3 : A ^ 2 / (2 * μ * d ^ 2) ≤ B ^ 2 / (2 * μ * δ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsq]
    linarith

end Proof

end Lemmata.AwayStepFW
