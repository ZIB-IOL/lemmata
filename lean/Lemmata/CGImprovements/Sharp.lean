module

public import Lemmata.CGImprovements.LazyAway

@[expose] public section

/-!
# Sharpness (Lemmas 3.31 and 3.32)

The minimizers form a compact set, so every `x` has a nearest minimizer `y`; sharpness bounds
`‖x - y‖` by `c h^θ`, and convexity gives `h ≤ f'(x)(x - y)`.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem sharp_primal_gap : SharpPrimalGap.{u} := by
  intro E _ _ C f c θ hC hconv hdiff hc hsharp xStar hxs x hx hlt
  have hΩc : IsCompact (minimizers C f) := by
    have e : minimizers C f = C ∩ f ⁻¹' Set.Iic (f xStar) := by
      ext y
      constructor
      · rintro ⟨hy, hmin⟩; exact ⟨hy, by simpa using hmin xStar hxs.1⟩
      · rintro ⟨hy, hle⟩
        exact ⟨hy, fun z hz => le_trans (by simpa using hle) (hxs.2 z hz)⟩
    rw [e]
    exact hC.inter_right (isClosed_Iic.preimage hdiff.continuous)
  obtain ⟨y, hy, hdist⟩ := hΩc.exists_infDist_eq_dist ⟨xStar, hxs⟩ x
  refine ⟨y, hy, ?_⟩
  have hpos : 0 < f x - f xStar := by linarith
  have hfy : f y = f xStar := le_antisymm (hy.2 xStar hxs.1) (hxs.2 y hy.1)
  have hxy : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun e => by
    rw [e] at hlt; linarith))
  have hconvex := add_fderiv_le_of_convexOn hconv hdiff x y
  have hg : f x - f xStar ≤ fderiv ℝ f x (x - y) := by
    rw [map_sub] at hconvex ⊢; linarith
  have hd : ‖x - y‖ ≤ c * (f x - f xStar) ^ θ := by
    rw [← dist_eq_norm, ← hdist]; exact hsharp x hx xStar hxs
  have e : (f x - f xStar) ^ (1 - θ) * (f x - f xStar) ^ θ = f x - f xStar := by
    rw [← Real.rpow_add hpos]; simp
  have h1 : (f x - f xStar) ^ (1 - θ) / c ≤ (f x - f xStar) / ‖x - y‖ := by
    rw [div_le_div_iff₀ hc hxy]
    calc (f x - f xStar) ^ (1 - θ) * ‖x - y‖ ≤
          (f x - f xStar) ^ (1 - θ) * (c * (f x - f xStar) ^ θ) :=
          mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hpos.le _)
      _ = (f x - f xStar) * c := by rw [mul_left_comm, e, mul_comm]
  exact h1.trans (div_le_div_of_nonneg_right hg hxy.le)

theorem geometric_sharpness : GeometricSharpness.{u} := by
  intro E _ _ V f c θ δ hconv hdiff hc hδ hsc hsharp xStar hxs S hSV x hx hlt a ha haS v hv hvV
  have hxV : x ∈ convexHull ℝ (↑V : Set E) := convexHull_mono (by exact_mod_cast hSV) hx
  obtain ⟨y, hy, hle⟩ := sharp_primal_gap (convexHull ℝ (↑V : Set E)) f c θ
    (V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)) hconv hdiff hc hsharp xStar hxs x hxV hlt
  have hsc' := hsc S hSV x hx y hy.1 (fderiv ℝ f x) a ha haS v hv hvV
  have hfy : f y = f xStar := le_antisymm (hy.2 xStar hxs.1) (hxs.2 y hy.1)
  have hxy : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun e => by
    rw [e] at hlt; linarith))
  have h2 : fderiv ℝ f x (x - y) / ‖x - y‖ ≤ fderiv ℝ f x (a - v) / δ := by
    rw [div_le_div_iff₀ hxy hδ]; linarith
  exact hle.trans h2

end Proof

end Lemmata.CGImprovements
