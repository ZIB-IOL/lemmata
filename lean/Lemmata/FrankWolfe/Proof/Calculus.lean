module

public import Lemmata.FrankWolfe.Defs
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Slope

@[expose] public section

/-!
# Calculus facts for the Frank–Wolfe core

First-order convexity and the descent lemma in a real normed space, with derivatives
`fderiv ℝ f : E → StrongDual ℝ E`.
-/

namespace Lemmata.FrankWolfe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of `t ↦ f (x + t • (y - x))` at `t`. -/
theorem hasDerivAt_segment {f : E → ℝ} (hf : Differentiable ℝ f) (x y : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • (y - x))) (fderiv ℝ f (x + t • (y - x)) (y - x)) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
    simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  exact (hf (x + t • (y - x))).hasFDerivAt.comp_hasDerivAt t hline

/-- First-order convexity: a differentiable convex function lies above its tangent planes. -/
theorem add_fderiv_le_of_convexOn {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hf : Differentiable ℝ f) (x y : E) : f x + fderiv ℝ f x (y - x) ≤ f y := by
  let g : ℝ → ℝ := fun s => f (AffineMap.lineMap x y s)
  have hg : ConvexOn ℝ Set.univ g := by
    have h := hconv.comp_affineMap (AffineMap.lineMap x y)
    rw [Set.preimage_univ] at h
    exact h
  have hd : HasDerivAt g (fderiv ℝ f x (y - x)) 0 := by
    have hline : HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ) :=
      AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ))
    have hfx : HasFDerivAt f (fderiv ℝ f x) (AffineMap.lineMap x y (0 : ℝ)) := by
      simpa using (hf x).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hfx hline
  have hslope := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) one_pos hd
  have : slope g 0 1 = f y - f x := by simp [g, slope]
  linarith

/-- The descent lemma: an `L`-smooth function lies below its quadratic upper model. -/
theorem IsSmooth.le_quadratic {f : E → ℝ} {L : NNReal} (h : IsSmooth f L) (x y : E) :
    f y ≤ f x + fderiv ℝ f x (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x
  let φ : ℝ → ℝ := fun t => f (x + t • d) - f x - t * fderiv ℝ f x d - L / 2 * t ^ 2 * ‖d‖ ^ 2
  have hφ' : ∀ t, HasDerivAt φ (fderiv ℝ f (x + t • d) d - fderiv ℝ f x d - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := hasDerivAt_segment h.1 x y t
    have h2 : HasDerivAt (fun t : ℝ => t * fderiv ℝ f x d) (fderiv ℝ f x d) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ f x d)
    have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul ((L : ℝ) / 2)).mul_const (‖d‖ ^ 2)
      convert this using 1; push_cast; ring
    exact ((h1.sub_const (f x)).sub h2).sub h3
  have hanti : AntitoneOn φ (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun t _ => (hφ' t).continuousAt.continuousWithinAt)
      (fun t _ => (hφ' t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hφ' t).deriv]
    have hlip : ‖fderiv ℝ f (x + t • d) - fderiv ℝ f x‖ ≤ L * ‖(x + t • d) - x‖ := by
      have := h.2.dist_le_mul (x + t • d) x
      rwa [dist_eq_norm, dist_eq_norm] at this
    have hnorm : ‖(x + t • d) - x‖ = t * ‖d‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt ht)]
    rw [hnorm] at hlip
    have happ : fderiv ℝ f (x + t • d) d - fderiv ℝ f x d ≤
        ‖fderiv ℝ f (x + t • d) - fderiv ℝ f x‖ * ‖d‖ := by
      have h1 := le_abs_self ((fderiv ℝ f (x + t • d) - fderiv ℝ f x) d)
      have h2 := (fderiv ℝ f (x + t • d) - fderiv ℝ f x).le_opNorm d
      have h3 : (fderiv ℝ f (x + t • d) - fderiv ℝ f x) d =
          fderiv ℝ f (x + t • d) d - fderiv ℝ f x d := rfl
      rw [h3] at h1 h2
      exact h1.trans (by simpa [Real.norm_eq_abs] using h2)
    have hd0 : 0 ≤ ‖d‖ := norm_nonneg d
    have key : ‖fderiv ℝ f (x + t • d) - fderiv ℝ f x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_right hlip hd0
    nlinarith [key, happ]
  have h01 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  simp only [φ, zero_smul, add_zero, sub_self, zero_mul, one_smul, one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_pow] at h01
  have : x + d = y := by simp [d]
  rw [this] at h01
  linarith

/-- Primal progress from smoothness, for a step of length `γ` from `x` toward `v`. -/
theorem IsSmooth.progress {f : E → ℝ} {L : NNReal} (h : IsSmooth f L) (x v : E) (γ : ℝ) :
    f (x + γ • (v - x)) ≤ f x - γ * fderiv ℝ f x (x - v) + γ ^ 2 * L / 2 * ‖v - x‖ ^ 2 := by
  have := h.le_quadratic x (x + γ • (v - x))
  rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs] at this
  have hneg : fderiv ℝ f x (v - x) = -fderiv ℝ f x (x - v) := by
    rw [← map_neg, neg_sub]
  rw [hneg] at this
  linarith

end Lemmata.FrankWolfe
