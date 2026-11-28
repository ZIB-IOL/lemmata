module

public import Lemmata.FWUniformlyConvex.Statement
public import Lemmata.CGBasics.Main

@[expose] public section

/-!
# Local scaling inequalities and Hölderian error bounds

Lemma 2.4 and Corollary 2.8 follow the argument of the scaling inequality for uniformly convex
sets (Proposition 2.19 of the basics entry) at the single point `x⋆`, with `η = 1/2`. Lemma 2.9
combines that scaling inequality with the lower bound `h^{1-θ} ≤ μ ‖f'(x)‖`, which the error bound
and convexity give.
-/

namespace Lemmata.FWUniformlyConvex

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `A (-ψ z) ≤ b` for every unit vector `z` and `A > 0`, then `A ‖ψ‖ ≤ b`. -/
theorem norm_bound_of_unit {ψ : StrongDual ℝ E} {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b)
    (hkey : ∀ z : E, ‖z‖ = 1 → A * (-ψ z) ≤ b) : A * ‖ψ‖ ≤ b := by
  have hbound : ‖ψ‖ ≤ b / A := by
    refine ContinuousLinearMap.opNorm_le_bound ψ (div_nonneg hb hA.le) (fun z => ?_)
    rcases eq_or_ne z 0 with hz | hz
    · simp [hz]
    · set u := (‖z‖⁻¹ : ℝ) • z with hu
      have hun : ‖u‖ = 1 := norm_smul_inv_norm hz
      have h1 := hkey u hun
      have h2 := hkey (-u) (by rw [norm_neg, hun])
      rw [map_neg, neg_neg] at h2
      have hψu : |ψ u| ≤ b / A := by
        rw [abs_le]
        constructor
        · rw [neg_le, le_div_iff₀ hA]; linarith
        · rw [le_div_iff₀ hA]; linarith
      have hz' : ψ z = ‖z‖ * ψ u := by
        rw [hu, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),
          one_mul]
      rw [Real.norm_eq_abs, hz', abs_mul, abs_norm, mul_comm]
      exact mul_le_mul_of_nonneg_right hψu (norm_nonneg z)
  calc A * ‖ψ‖ ≤ A * (b / A) := mul_le_mul_of_nonneg_left hbound hA.le
    _ = b := mul_div_cancel₀ _ hA.ne'

/-- **Lemma 2.4.** -/
theorem local_scaling_of_luc {C : Set E} {f : E → ℝ} {α q : ℝ} {xStar : E}
    (hopt : ∀ x ∈ C, 0 ≤ fderiv ℝ f xStar (x - xStar))
    (hluc : IsLocallyUniformlyConvexAt C α q xStar) : IsLocalScaling C f α q xStar := by
  intro x hx
  set ψ := fderiv ℝ f xStar with hψ
  set A := α / 2 * ‖xStar - x‖ ^ q with hA
  have hre : α / 2 * ‖ψ‖ * ‖xStar - x‖ ^ q = A * ‖ψ‖ := by rw [hA]; ring
  rw [hre]
  have hb := hopt x hx
  rcases le_or_gt A 0 with hA0 | hApos
  · nlinarith [norm_nonneg ψ]
  apply norm_bound_of_unit hApos hb
  intro z hz
  have hm := hluc x hx (1 / 2) ⟨by norm_num, by norm_num⟩ z hz
  have h1 := hopt _ hm
  have e : (1 / 2 : ℝ) • xStar + ((1 : ℝ) - 1 / 2) • x +
      (1 / 2 * (1 - 1 / 2) * α * ‖xStar - x‖ ^ q) • z - xStar =
      (1 / 2 : ℝ) • (x - xStar) + (1 / 2 * (1 - 1 / 2) * α * ‖xStar - x‖ ^ q) • z := by module
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  have e2 : A * (-ψ z) = -(2 * (1 / 2 * (1 - 1 / 2) * α * ‖xStar - x‖ ^ q)) * ψ z := by
    rw [hA]; ring
  rw [e2]
  linarith

/-- **Corollary 2.8.** -/
theorem superset_scaling {C Γ : Set E} {f : E → ℝ} {α q : ℝ} {xStar : E}
    (hCΓ : C ⊆ Γ) (hUC : IsUniformlyConvexSet Γ α q) (hxs : xStar ∈ C)
    (hopt : ∀ y ∈ Γ, 0 ≤ fderiv ℝ f xStar (y - xStar)) : IsLocalScaling C f α q xStar := by
  have hluc : IsLocallyUniformlyConvexAt Γ α q xStar := fun x hx η hη z hz =>
    hUC xStar (hCΓ hxs) x hx η hη z hz
  exact fun x hx => local_scaling_of_luc hopt hluc x (hCΓ hx)

/-- The Hölderian error bound and convexity give `h^{1-θ} ≤ μ ‖f'(x)‖`. -/
theorem heb_grad_lower {C : Set E} {f : E → ℝ} {μ θ : ℝ} (hconv : ConvexOn ℝ C f)
    (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y) (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ)
    (hθ : θ < 1) {xStar : E} (hxs : xStar ∈ minimizers C f) {x : E} (hx : x ∈ C) :
    (f x - f xStar) ^ (1 - θ) ≤ μ * ‖fderiv ℝ f x‖ := by
  set h := f x - f xStar with hh
  have hh0 : 0 ≤ h := sub_nonneg.mpr (hxs.2 x hx)
  rcases eq_or_lt_of_le hh0 with hz | hpos
  · rw [← hz, Real.zero_rpow (by linarith)]; positivity
  have hd := heb x hx xStar hxs
  -- `h ≤ ‖f'(x)‖ (μ h^θ + ε)` for every `ε > 0`
  have hkey : ∀ ε > 0, h ≤ ‖fderiv ℝ f x‖ * (μ * h ^ θ + ε) := by
    intro ε hε
    obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff ⟨xStar, hxs⟩).mp
      (lt_of_le_of_lt hd (lt_add_of_pos_right _ hε))
    have hfy : f y = f xStar := le_antisymm (hy.2 xStar hxs.1) (hxs.2 y hy.1)
    have hc := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv hx (hdiff x hx) hy.1
    have h1 : h ≤ fderiv ℝ f x (x - y) := by
      rw [hh, ← hfy, map_sub]
      have : fderiv ℝ f x (y - x) = fderiv ℝ f x y - fderiv ℝ f x x := map_sub _ _ _
      linarith
    have h2 : fderiv ℝ f x (x - y) ≤ ‖fderiv ℝ f x‖ * ‖x - y‖ :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
    have h3 : ‖x - y‖ ≤ μ * h ^ θ + ε := by rw [← dist_eq_norm]; exact hyd.le
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)))
  have hle : h ≤ ‖fderiv ℝ f x‖ * (μ * h ^ θ) := by
    by_contra hlt
    push Not at hlt
    set N := ‖fderiv ℝ f x‖ with hN
    have hN0 : 0 ≤ N := norm_nonneg _
    have := hkey ((h - N * (μ * h ^ θ)) / (2 * (N + 1))) (by
      apply div_pos (by linarith) (by positivity))
    have hcalc : N * (μ * h ^ θ + (h - N * (μ * h ^ θ)) / (2 * (N + 1))) <
        h := by
      have e : N * ((h - N * (μ * h ^ θ)) / (2 * (N + 1))) ≤ (h - N * (μ * h ^ θ)) / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith
    linarith
  have hθpos : 0 < h ^ θ := Real.rpow_pos_of_pos hpos θ
  have e : h ^ (1 - θ) = h / h ^ θ := by
    rw [Real.rpow_sub hpos, Real.rpow_one]
  rw [e, div_le_iff₀ hθpos]
  linarith

/-- **Lemma 2.9.** -/
theorem heb_scaling_bound {C : Set E} {f : E → ℝ} {α q μ θ : ℝ} {xStar x v : E}
    (hUC : IsUniformlyConvexSet C α q) (hα : 0 < α) (hconv : ConvexOn ℝ C f)
    (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y) (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hxs : xStar ∈ minimizers C f) (hx : x ∈ C) (hv : v ∈ C)
    (hvmin : ∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) :
    α / μ * ‖x - v‖ ^ q * (f x - f xStar) ^ (1 - θ) ≤ fderiv ℝ f x (x - v) := by
  have hsc := Lemmata.CGBasics.Proof.uniformly_convex_scaling C α q hUC (fderiv ℝ f x) v hv
    hvmin x hx
  have hg := heb_grad_lower hconv hdiff heb hμ (by linarith [hθ.2]) hxs hx
  have hn : 0 ≤ ‖x - v‖ ^ q := Real.rpow_nonneg (norm_nonneg _) q
  calc α / μ * ‖x - v‖ ^ q * (f x - f xStar) ^ (1 - θ) ≤
        α / μ * ‖x - v‖ ^ q * (μ * ‖fderiv ℝ f x‖) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
    _ = α * ‖fderiv ℝ f x‖ * ‖x - v‖ ^ q := by field_simp
    _ ≤ fderiv ℝ f x (x - v) := hsc

namespace Proof

theorem local_scaling_of_locally_uc : LocalScalingOfLocallyUC.{u} := by
  intro E _ _ C f α q xStar _ hopt hluc
  exact local_scaling_of_luc hopt hluc

theorem local_scaling_of_superset : LocalScalingOfSuperset.{u} := by
  intro E _ _ C Γ f α q xStar hCΓ hUC hxs hopt
  exact superset_scaling hCΓ hUC hxs hopt

theorem heb_scaling : HEBScaling.{u} := by
  intro E _ _ C f α q μ θ xStar x v hUC hα hconv hdiff heb hμ hθ hxs hx hv hvmin
  exact heb_scaling_bound hUC hα hconv hdiff heb hμ hθ hxs hx hv hvmin

end Proof

end Lemmata.FWUniformlyConvex
