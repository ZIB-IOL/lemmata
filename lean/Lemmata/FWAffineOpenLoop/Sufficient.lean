module

public import Lemmata.FWAffineOpenLoop.Gaps
public import Lemmata.FWOpenLoop.Uniform

@[expose] public section

/-!
# Sufficient conditions for the growth properties: Propositions 2.8, 3.6, 4.3 and 5.3

Smoothness bounds the Bregman divergence along the Frank–Wolfe segment by `L/2 η² ‖v - x‖²`. The
diameter (Proposition 2.8), the scaling inequality of uniformly convex sets with gradients bounded
away from zero (Proposition 3.6) or with a Hölderian error bound (Proposition 4.3) then bound
`‖v - x‖²` by a power of the Frank–Wolfe gap. Proposition 5.3 is the interior gap bound of the entry
on open-loop acceleration.
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FrankWolfe Lemmata.FWOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothness bounds the Bregman divergence along the Frank–Wolfe segment. -/
theorem bregman_le_smooth {C : Set E} {f : E → ℝ} {L : ℝ} (hC : Convex ℝ C)
    (hs : IsSmoothOn C f L) {x v : E} (hx : x ∈ C) (hv : v ∈ C) {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) :
    bregman f (x + η • (v - x)) x ≤ L / 2 * η ^ 2 * ‖v - x‖ ^ 2 := by
  have hy : x + η • (v - x) ∈ C := hC.add_smul_sub_mem hx hv hη
  have h := hs x hx _ hy
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη.1, mul_pow] at h
  simp only [bregman, add_sub_cancel_left]
  linarith

/-- The Frank–Wolfe gap of a Frank–Wolfe vertex is nonnegative. -/
theorem fw_gap_nonneg {C : Set E} {f : E → ℝ} {x v : E} (hx : x ∈ C)
    (hvmin : ∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) : 0 ≤ fderiv ℝ f x (x - v) := by
  have := hvmin x hx; rw [map_sub]; linarith

/-- The primal gap is at most the Frank–Wolfe gap. -/
theorem subopt_le_fw_gap {C : Set E} {f : E → ℝ} (hconv : ConvexOn ℝ C f)
    (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y) {x v xStar : E} (hx : x ∈ C)
    (hvmin : ∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) (hxs : xStar ∈ minimizers C f) :
    f x - f xStar ≤ fderiv ℝ f x (x - v) := by
  have h1 := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv hx (hdiff x hx) hxs.1
  have h2 := hvmin xStar hxs.1
  rw [map_sub]
  rw [map_sub] at h1
  linarith

namespace Proof

theorem smooth_strong_growth : SmoothStrongGrowth.{u} := by
  intro E _ _ C f L hC hb hL hs x hx v hv _ η hη
  have h1 := bregman_le_smooth hC hs hx hv hη
  have h2 : ‖v - x‖ ≤ Metric.diam C := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hb hv hx
  have h3 : ‖v - x‖ ^ 2 ≤ Metric.diam C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [Real.rpow_zero, mul_one]
  calc bregman f (x + η • (v - x)) x ≤ L / 2 * η ^ 2 * ‖v - x‖ ^ 2 := h1
    _ ≤ L / 2 * η ^ 2 * Metric.diam C ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = L * Metric.diam C ^ 2 * η ^ 2 / 2 := by ring

theorem uniform_strong_growth : UniformStrongGrowth.{u} := by
  intro E _ _ C f α p L lam hC hUC hα hp hL hlam hs hgrad x hx v hv hvmin η hη
  have h1 := bregman_le_smooth hC hs hx hv hη
  have hsc := Lemmata.CGBasics.Proof.uniformly_convex_scaling C α p hUC (fderiv ℝ f x) v hv hvmin
    x hx
  set g := fderiv ℝ f x (x - v) with hg
  have hg0 : 0 ≤ g := fw_gap_nonneg hx hvmin
  set d := ‖x - v‖ with hd
  have hvx : ‖v - x‖ = d := norm_sub_rev _ _
  have hdp0 : 0 ≤ d ^ p := Real.rpow_nonneg (norm_nonneg _) p
  have hal : 0 < α * lam := mul_pos hα hlam
  have h2 : α * lam * d ^ p ≤ g := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgrad x hx) hα.le) hdp0
    linarith
  -- `(αλ)^{2/p} d² ≤ g^{2/p}`
  have h3 : (α * lam) ^ (2 / p) * d ^ 2 ≤ g ^ (2 / p) := by
    have := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0 : ℝ) ≤ 2 / p)
    rwa [Real.mul_rpow hal.le hdp0, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hp.ne',
      Real.rpow_two] at this
  have h4 : d ^ 2 ≤ (α * lam) ^ (-(2 / p)) * g ^ (2 / p) := by
    have hpos : 0 < (α * lam) ^ (2 / p) := Real.rpow_pos_of_pos hal _
    rw [Real.rpow_neg hal.le, inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  rw [hvx] at h1
  calc bregman f (x + η • (v - x)) x ≤ L / 2 * η ^ 2 * d ^ 2 := h1
    _ ≤ L / 2 * η ^ 2 * ((α * lam) ^ (-(2 / p)) * g ^ (2 / p)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = L * (α * lam) ^ (-(2 / p)) * η ^ 2 / 2 * g ^ (2 / p) := by ring

theorem uniform_weak_growth : UniformWeakGrowth.{u} := by
  intro E _ _ C f α p L μ θ hC hconv hdiff hUC hα hp hL hs heb hμ hθ x hx v hv hvmin xStar hxs
    η hη
  have h1 := bregman_le_smooth hconv.1 hs hx hv hη
  set g := fderiv ℝ f x (x - v) with hg
  have hg0 : 0 ≤ g := fw_gap_nonneg hx hvmin
  set h := f x - f xStar with hh
  have hh0 : 0 ≤ h := sub_nonneg.mpr (hxs.2 x hx)
  have hhg : h ≤ g := subopt_le_fw_gap hconv hdiff hx hvmin hxs
  have hp0 : 0 < p := by linarith
  have hr1 : 0 < 1 - 2 * θ / p := by
    rw [sub_pos, div_lt_one hp0]; linarith [hθ.2]
  set M := L * (μ / α) ^ (2 / p) with hM
  have hM0 : 0 ≤ M := by positivity
  rcases hh0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hr1.ne', mul_zero]
    positivity
  obtain ⟨y, -, -, -, -, hnorm⟩ := Lemmata.FrankWolfe.Proof.heb_scaling C f μ θ hC hconv hdiff
    heb xStar hxs x hx (by linarith)
  have hsc := Lemmata.CGBasics.Proof.uniformly_convex_scaling C α p hUC (fderiv ℝ f x) v hv hvmin
    x hx
  set d := ‖x - v‖ with hd
  have hvx : ‖v - x‖ = d := norm_sub_rev _ _
  have hdp0 : 0 ≤ d ^ p := Real.rpow_nonneg (norm_nonneg _) p
  have hgpos : 0 < g := lt_of_lt_of_le hpos hhg
  set k := h ^ (1 - θ) with hk
  have hk0 : 0 ≤ k := Real.rpow_nonneg hh0 _
  -- `k d^p ≤ (μ/α) g`
  have h2 : k * d ^ p ≤ μ / α * g := by
    have e1 := mul_le_mul_of_nonneg_right hnorm hdp0
    have e2 := mul_le_mul_of_nonneg_left hsc (by positivity : (0 : ℝ) ≤ μ / α)
    have e3 : μ / α * (α * ‖fderiv ℝ f x‖ * d ^ p) = μ * ‖fderiv ℝ f x‖ * d ^ p := by
      field_simp
    linarith
  -- `k^{2/p} d² ≤ (μ/α)^{2/p} g^{2/p}`
  have h3 : k ^ (2 / p) * d ^ 2 ≤ (μ / α) ^ (2 / p) * g ^ (2 / p) := by
    have := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0 : ℝ) ≤ 2 / p)
    rwa [Real.mul_rpow hk0 hdp0, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hp0.ne',
      Real.rpow_two, Real.mul_rpow (by positivity) hg0] at this
  -- `h^{1-2θ/p} = k^{2/p} h^{1-2/p}`
  have e4 : h ^ (1 - 2 * θ / p) = k ^ (2 / p) * h ^ (1 - 2 / p) := by
    rw [hk, ← Real.rpow_mul hh0, ← Real.rpow_add hpos]; congr 1; ring
  have h5 : h ^ (1 - 2 / p) ≤ g ^ (1 - 2 / p) := by
    apply Real.rpow_le_rpow hh0 hhg
    rw [sub_nonneg, div_le_one hp0]; exact hp
  have e6 : g ^ (2 / p) * g ^ (1 - 2 / p) = g := by
    rw [← Real.rpow_add hgpos]; norm_num
  rw [hvx] at h1
  have hD : bregman f (x + η • (v - x)) x * h ^ (1 - 2 * θ / p) ≤
      L / 2 * η ^ 2 * d ^ 2 * h ^ (1 - 2 * θ / p) :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hh0 _)
  calc bregman f (x + η • (v - x)) x * h ^ (1 - 2 * θ / p)
      ≤ L / 2 * η ^ 2 * d ^ 2 * h ^ (1 - 2 * θ / p) := hD
    _ = L / 2 * η ^ 2 * (k ^ (2 / p) * d ^ 2) * h ^ (1 - 2 / p) := by rw [e4]; ring
    _ ≤ L / 2 * η ^ 2 * ((μ / α) ^ (2 / p) * g ^ (2 / p)) * h ^ (1 - 2 / p) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh0 _)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ L / 2 * η ^ 2 * ((μ / α) ^ (2 / p) * g ^ (2 / p)) * g ^ (1 - 2 / p) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = M * η ^ 2 / 2 * (g ^ (2 / p) * g ^ (1 - 2 / p)) := by rw [hM]; ring
    _ = M * η ^ 2 / 2 * g := by rw [e6]

theorem interior_gaps_growth : InteriorGapsGrowth.{u} := by
  intro E _ _ C f μ θ ρ hC hconv hdiff heb hμ hθ hρ hball x hx v _ hvmin xStar hxs
  exact interior_gap hC hconv hdiff heb hμ (by linarith [hθ.2]) hρ hball hxs hx hvmin

end Proof

end Lemmata.FWAffineOpenLoop
