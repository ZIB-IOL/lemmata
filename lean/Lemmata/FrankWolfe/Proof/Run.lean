module

public import Lemmata.FrankWolfe.Statement
public import Lemmata.FrankWolfe.Proof.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Runs, error bounds and strong convexity

Proofs of the statements about Frank–Wolfe runs (`IsFWRun`), smoothness over a set
(`IsSmoothOn`), Hölderian error bounds (`IsHolderErrorBound`) and strong convexity (Mathlib's
`StrongConvexOn`). The first-order facts come from one limit argument, `fderiv_le_of_slope_le`:
a bound on the difference quotients of `s ↦ f(x + s d)` for small `s > 0` bounds the directional
derivative.
-/

namespace Lemmata.FrankWolfe

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `(f(x + s d) - f(x))/s ≤ A - (1 - s) B` for all `s ∈ (0, 1)`, then `f'(x) d ≤ A - B`. -/
theorem fderiv_le_of_slope_le {f : E → ℝ} {x d : E} (hf : DifferentiableAt ℝ f x) {A B : ℝ}
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) 1, (f (x + s • d) - f x) / s ≤ A - (1 - s) * B) :
    fderiv ℝ f x d ≤ A - B := by
  have hd : HasDerivAt (fun s : ℝ => f (x + s • d)) (fderiv ℝ f x d) 0 := by
    have hline : HasDerivAt (fun s : ℝ => x + s • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    have hfx : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • d) := by
      simpa using hf.hasFDerivAt
    exact hfx.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hd.tendsto_slope_zero_right
  have hrhs : Tendsto (fun s : ℝ => A - (1 - s) * B) (𝓝[>] 0) (𝓝 (A - B)) := by
    have hc : Continuous fun s : ℝ => A - (1 - s) * B := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hslope hrhs ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  have h1 := h s hs
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  rw [div_eq_inv_mul] at h1
  exact h1

/-- If `(1 - s) K ≤ h` for all `s ∈ (0, 1)`, then `K ≤ h`. -/
theorem le_of_one_sub_mul_le {K h : ℝ} (hK : ∀ s ∈ Set.Ioo (0 : ℝ) 1, (1 - s) * K ≤ h) :
    K ≤ h := by
  have hlim : Tendsto (fun s : ℝ => (1 - s) * K) (𝓝[>] 0) (𝓝 K) := by
    have hc : Continuous fun s : ℝ => (1 - s) * K := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact hK s hs

/-- First-order strong convexity on a set. -/
theorem strongConvexOn_add_fderiv_le {C : Set E} {f : E → ℝ} {μ : ℝ} (hsc : StrongConvexOn C μ f)
    {x : E} (hx : x ∈ C) (hf : DifferentiableAt ℝ f x) {y : E} (hy : y ∈ C) :
    f x + fderiv ℝ f x (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have key := fderiv_le_of_slope_le (d := y - x) hf (A := f y - f x) (B := μ / 2 * ‖x - y‖ ^ 2)
    (fun s hs => by
      have hs0 : 0 < s := hs.1
      have h := hsc.2 hx hy (show (0 : ℝ) ≤ 1 - s by linarith [hs.2]) hs0.le (by ring)
      have hpt : (1 - s) • x + s • y = x + s • (y - x) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [hpt, smul_eq_mul, smul_eq_mul] at h
      rw [div_le_iff₀ hs0]
      nlinarith)
  rw [norm_sub_rev] at key
  linarith

/-- First-order convexity on a set. -/
theorem convexOn_add_fderiv_le {C : Set E} {f : E → ℝ} (hconv : ConvexOn ℝ C f) {x : E}
    (hx : x ∈ C) (hf : DifferentiableAt ℝ f x) {y : E} (hy : y ∈ C) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  have := strongConvexOn_add_fderiv_le (strongConvexOn_zero.mpr hconv) hx hf hy
  simpa using this

/-- Quadratic growth around the minimizers of a strongly convex function. -/
theorem strongConvexOn_growth {C : Set E} {f : E → ℝ} {μ : ℝ} (hsc : StrongConvexOn C μ f)
    {xStar : E} (hxs : xStar ∈ minimizers C f) {x : E} (hx : x ∈ C) :
    μ / 2 * ‖x - xStar‖ ^ 2 ≤ f x - f xStar := by
  refine le_of_one_sub_mul_le (fun s hs => ?_)
  have hs0 : 0 < s := hs.1
  have h := hsc.2 hxs.1 hx (show (0 : ℝ) ≤ 1 - s by linarith [hs.2]) hs0.le (by ring)
  have hmem : (1 - s) • xStar + s • x ∈ C :=
    hsc.1 hxs.1 hx (by linarith [hs.2]) hs0.le (by ring)
  have hmin := hxs.2 _ hmem
  rw [smul_eq_mul, smul_eq_mul, norm_sub_rev] at h
  have : s * ((1 - s) * (μ / 2 * ‖x - xStar‖ ^ 2)) ≤ s * (f x - f xStar) := by nlinarith
  exact le_of_mul_le_mul_left this hs0

namespace Proof

universe u

theorem fw_run_mem : FWRunMem.{u} := by
  intro E _ _ C f' x v γ hC hrun t
  induction t with
  | zero => exact hrun.1
  | succ t ih =>
    obtain ⟨hv, -, hγ, hx⟩ := hrun.2 t
    rw [hx]
    exact hC.add_smul_sub_mem ih hv hγ

theorem fwIterates_isFWRun : FWIteratesIsRun.{u} := by
  intro E _ _ C lmo f' step x₀ hlmo hstep hx₀
  exact ⟨hx₀, fun t => ⟨(hlmo _).1, (hlmo _).2, hstep t _, rfl⟩⟩

theorem smoothOn_of_smooth : SmoothOnOfSmooth.{u} := by
  intro E _ _ C f L h x _ y _
  exact h.le_quadratic x y

theorem run_progress : RunProgress.{u} := by
  intro E _ _ C f L x v γ hC hsm hrun t
  obtain ⟨hv, -, hγ, hx⟩ := hrun.2 t
  have hxC : x t ∈ C := fw_run_mem C _ x v γ hC hrun t
  have hx1C : x (t + 1) ∈ C := fw_run_mem C _ x v γ hC hrun (t + 1)
  have h := hsm (x t) hxC (x (t + 1)) hx1C
  rw [hx, add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs] at h
  rw [hx]
  have hlin : fderiv ℝ f (x t) (x t - v t) = -fderiv ℝ f (x t) (v t - x t) := by
    rw [← map_neg, neg_sub]
  rw [hlin]
  nlinarith

theorem heb_scaling : HEBScaling.{u} := by
  intro E _ _ C f μ θ hC hconv hdiff heb xStar hxs x hx hlt
  set M := minimizers C f with hM
  have hcont : ContinuousOn f C := fun z hz => (hdiff z hz).continuousAt.continuousWithinAt
  have hMeq : M = C ∩ f ⁻¹' Set.Iic (f xStar) := by
    ext z
    constructor
    · rintro ⟨hz, hmin⟩
      exact ⟨hz, hmin xStar hxs.1⟩
    · rintro ⟨hz, hle⟩
      exact ⟨hz, fun y hy => le_trans hle (hxs.2 y hy)⟩
  have hMc : IsCompact M := by
    rw [hMeq]
    exact hC.of_isClosed_subset (hcont.preimage_isClosed_of_isClosed hC.isClosed isClosed_Iic)
      Set.inter_subset_left
  obtain ⟨y, hyM, hyd⟩ := hMc.exists_infDist_eq_dist ⟨xStar, hxs⟩ x
  have hfy : f y = f xStar := le_antisymm (hyM.2 xStar hxs.1) (hxs.2 y hyM.1)
  set h := f x - f xStar with hh
  have hpos : 0 < h := by rw [hh]; linarith
  have hxy : x ≠ y := by
    rintro rfl
    linarith
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdist : ‖x - y‖ = Metric.infDist x M := by rw [hyd, dist_eq_norm]
  have hheb : ‖x - y‖ ≤ μ * h ^ θ := by
    rw [hdist]
    exact heb x hx xStar hxs
  have hgap : h ≤ fderiv ℝ f x (x - y) := by
    have := convexOn_add_fderiv_le hconv hx (hdiff x hx) hyM.1
    have hlin : fderiv ℝ f x (y - x) = -fderiv ℝ f x (x - y) := by rw [← map_neg, neg_sub]
    rw [hlin] at this
    linarith
  have hθpos : 0 < h ^ θ := Real.rpow_pos_of_pos hpos θ
  have hμ : 0 < μ := by
    by_contra hμ
    replace hμ := not_lt.mp hμ
    have : μ * h ^ θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hμ hθpos.le
    linarith
  have hsplit : h ^ (1 - θ) * h ^ θ = h := by
    rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
  have h1θ : 0 ≤ h ^ (1 - θ) := (Real.rpow_pos_of_pos hpos _).le
  have hmain : h ^ (1 - θ) * ‖x - y‖ ≤ μ * fderiv ℝ f x (x - y) := by
    calc h ^ (1 - θ) * ‖x - y‖ ≤ h ^ (1 - θ) * (μ * h ^ θ) :=
          mul_le_mul_of_nonneg_left hheb h1θ
      _ = μ * (h ^ (1 - θ) * h ^ θ) := by ring
      _ = μ * h := by rw [hsplit]
      _ ≤ μ * fderiv ℝ f x (x - y) := mul_le_mul_of_nonneg_left hgap hμ.le
  refine ⟨y, hyM, hxy, hdist, hmain, ?_⟩
  have hop : fderiv ℝ f x (x - y) ≤ ‖fderiv ℝ f x‖ * ‖x - y‖ :=
    le_trans (le_abs_self _) (by
      rw [← Real.norm_eq_abs]
      exact (fderiv ℝ f x).le_opNorm (x - y))
  have : h ^ (1 - θ) * ‖x - y‖ ≤ (μ * ‖fderiv ℝ f x‖) * ‖x - y‖ := by
    calc h ^ (1 - θ) * ‖x - y‖ ≤ μ * fderiv ℝ f x (x - y) := hmain
      _ ≤ μ * (‖fderiv ℝ f x‖ * ‖x - y‖) := mul_le_mul_of_nonneg_left hop hμ.le
      _ = (μ * ‖fderiv ℝ f x‖) * ‖x - y‖ := by ring
  exact le_of_mul_le_mul_right this hnorm

theorem strongConvex_first_order : StrongConvexFirstOrder.{u} := by
  intro E _ _ C f μ hsc x hx hf y hy
  exact strongConvexOn_add_fderiv_le hsc hx hf hy

theorem strongConvex_heb : StrongConvexHEB.{u} := by
  intro E _ _ C f μ hsc hμ
  refine ⟨fun xStar hxs x hx => strongConvexOn_growth hsc hxs hx, fun x hx xStar hxs => ?_⟩
  have hg := strongConvexOn_growth hsc hxs hx
  have hh : 0 ≤ f x - f xStar := sub_nonneg.mpr (hxs.2 x hx)
  calc Metric.infDist x (minimizers C f) ≤ dist x xStar := Metric.infDist_le_dist_of_mem hxs
    _ = Real.sqrt (‖x - xStar‖ ^ 2) := by rw [dist_eq_norm, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (2 / μ * (f x - f xStar)) := by
        apply Real.sqrt_le_sqrt
        rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
        nlinarith
    _ = Real.sqrt (2 / μ) * (f x - f xStar) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (f x - f xStar)]

end Proof

end Lemmata.FrankWolfe
