module

public import Lemmata.FWUniformlyConvex.Local

@[expose] public section

/-!
# Examples of uniformly convex sets (Section 4 and Appendix D)

Unit balls of uniformly convex spaces are uniformly convex sets (Lemma 4.2). Sublevel sets of
nonnegative smooth uniformly convex functions (Lemma D.2) and balls of norms with a uniformly convex
square (Lemma D.3) are uniformly convex, with half the constants printed in the paper: its proofs
give these constants, and the Euclidean unit disk shows that the printed ones are too large. For
exponents above `2` the hypotheses of Lemmas D.2 and D.3 cannot hold on a nontrivial space.
-/

namespace Lemmata.FWUniformlyConvex

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 4.2**, unit balls. -/
theorem ball_uc_of_modulus {α q : ℝ} (hα : 0 ≤ α)
    (hδ : ∀ ε ∈ Set.Icc (0 : ℝ) 2, α * ε ^ q ≤ modulusOfConvexity E ε) :
    IsUniformlyConvexSet (Metric.closedBall (0 : E) 1) α q := by
  intro x hx y hy η hη z hz
  rw [mem_closedBall_zero_iff] at hx hy ⊢
  set d := ‖x - y‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd2 : d ≤ 2 := by
    have := norm_sub_le x y; linarith
  set m := (1 / 2 : ℝ) • (x + y) with hm
  have hmod : modulusOfConvexity E d ≤ 1 - ‖m‖ := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨a, b, ha, hb, -, rfl⟩
      have : ‖(1 / 2 : ℝ) • (a + b)‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        have := norm_add_le a b; linarith
      linarith
    · exact ⟨x, y, hx, hy, le_rfl, rfl⟩
  have hk : α * d ^ q ≤ 1 - ‖m‖ := (hδ d ⟨hd0, hd2⟩).trans hmod
  have hdq : 0 ≤ α * d ^ q := mul_nonneg hα (Real.rpow_nonneg hd0 q)
  have hη0 := hη.1
  have hη1 := hη.2
  set c := η * (1 - η) * α * d ^ q with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ η * (1 - η) := mul_nonneg hη0 (by linarith)
    rw [hc, mul_assoc]; exact mul_nonneg this hdq
  have hz' : ‖c • z‖ = c := by rw [norm_smul, hz, mul_one, Real.norm_of_nonneg hc0]
  rcases le_total η (1 / 2) with hle | hle
  · have e : η • x + (1 - η) • y = (2 * η) • m + (1 - 2 * η) • y := by rw [hm]; module
    have h1 : ‖η • x + (1 - η) • y‖ ≤ 1 - 2 * η * (α * d ^ q) := by
      rw [e]
      calc ‖(2 * η) • m + (1 - 2 * η) • y‖ ≤ ‖(2 * η) • m‖ + ‖(1 - 2 * η) • y‖ :=
            norm_add_le _ _
        _ = 2 * η * ‖m‖ + (1 - 2 * η) * ‖y‖ := by
            rw [norm_smul (2 * η) m, norm_smul (1 - 2 * η) y, Real.norm_of_nonneg (by linarith),
              Real.norm_of_nonneg (by linarith)]
        _ ≤ 2 * η * (1 - α * d ^ q) + (1 - 2 * η) * 1 := by
            have h2 : ‖m‖ ≤ 1 - α * d ^ q := by linarith
            have h3 : 0 ≤ 1 - 2 * η := by linarith
            nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * η),
              mul_le_mul_of_nonneg_left hy h3]
        _ = 1 - 2 * η * (α * d ^ q) := by ring
    calc ‖η • x + (1 - η) • y + c • z‖ ≤ ‖η • x + (1 - η) • y‖ + ‖c • z‖ := norm_add_le _ _
      _ ≤ 1 - 2 * η * (α * d ^ q) + c := by rw [hz']; linarith
      _ ≤ 1 := by
          have : c ≤ η * (α * d ^ q) := by
            rw [hc]; nlinarith [mul_nonneg hη0 hdq]
          nlinarith [mul_nonneg hη0 hdq]
  · have e : η • x + (1 - η) • y = (2 * (1 - η)) • m + (2 * η - 1) • x := by rw [hm]; module
    have h1 : ‖η • x + (1 - η) • y‖ ≤ 1 - 2 * (1 - η) * (α * d ^ q) := by
      rw [e]
      calc ‖(2 * (1 - η)) • m + (2 * η - 1) • x‖ ≤ ‖(2 * (1 - η)) • m‖ + ‖(2 * η - 1) • x‖ :=
            norm_add_le _ _
        _ = 2 * (1 - η) * ‖m‖ + (2 * η - 1) * ‖x‖ := by
            rw [norm_smul (2 * (1 - η)) m, norm_smul (2 * η - 1) x,
              Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
        _ ≤ 2 * (1 - η) * (1 - α * d ^ q) + (2 * η - 1) * 1 := by
            have h2 : ‖m‖ ≤ 1 - α * d ^ q := by linarith
            have h3 : 0 ≤ 2 * η - 1 := by linarith
            nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * (1 - η)),
              mul_le_mul_of_nonneg_left hx h3]
        _ = 1 - 2 * (1 - η) * (α * d ^ q) := by ring
    calc ‖η • x + (1 - η) • y + c • z‖ ≤ ‖η • x + (1 - η) • y‖ + ‖c • z‖ := norm_add_le _ _
      _ ≤ 1 - 2 * (1 - η) * (α * d ^ q) + c := by rw [hz']; linarith
      _ ≤ 1 := by
          have h4 : 0 ≤ 1 - η := by linarith
          have : c ≤ (1 - η) * (α * d ^ q) := by
            rw [hc]; nlinarith [mul_nonneg h4 hdq]
          nlinarith [mul_nonneg h4 hdq]

/-- **Lemma 4.2**, scaling of balls. -/
theorem ball_uc_scale {α q r : ℝ} (hr : 0 < r)
    (h1 : IsUniformlyConvexSet (Metric.closedBall (0 : E) 1) α q) :
    IsUniformlyConvexSet (Metric.closedBall (0 : E) r) (α / r ^ (q - 1)) q := by
  intro x hx y hy η hη z hz
  rw [mem_closedBall_zero_iff] at hx hy ⊢
  have hx' : r⁻¹ • x ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ hr]; linarith
  have hy' : r⁻¹ • y ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ hr]; linarith
  have h := h1 _ hx' _ hy' η hη z hz
  rw [mem_closedBall_zero_iff] at h
  set c := η * (1 - η) * (α / r ^ (q - 1)) * ‖x - y‖ ^ q with hc
  have hc' : η * (1 - η) * α * ‖r⁻¹ • x - r⁻¹ • y‖ ^ q = c / r := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity),
      Real.mul_rpow (by positivity) (norm_nonneg _), Real.inv_rpow hr.le, hc,
      Real.rpow_sub_one hr.ne']
    field_simp
  rw [hc'] at h
  have e : r • (η • (r⁻¹ • x) + (1 - η) • (r⁻¹ • y) + (c / r) • z) =
      η • x + (1 - η) • y + c • z := by
    rw [smul_add, smul_add, smul_comm r η, smul_inv_smul₀ hr.ne', smul_comm r (1 - η),
      smul_inv_smul₀ hr.ne', smul_smul, show r * (c / r) = c by field_simp]
  rw [← e, norm_smul, Real.norm_of_nonneg hr.le]
  calc r * ‖η • (r⁻¹ • x) + (1 - η) • (r⁻¹ • y) + (c / r) • z‖ ≤ r * 1 :=
        mul_le_mul_of_nonneg_left h hr.le
    _ = r := mul_one r

/-- `t^r ≤ C t²` for all `t > 0` forces `r ≤ 2`. -/
theorem exponent_le_two {r C : ℝ} (h : ∀ t : ℝ, 0 < t → t ^ r ≤ C * t ^ 2) : r ≤ 2 := by
  by_contra hr
  push Not at hr
  have hr2 : 0 < r - 2 := by linarith
  set t := (|C| + 1) ^ (1 / (r - 2)) with ht
  have htpos : 0 < t := by positivity
  have htr : t ^ (r - 2) = |C| + 1 := by
    rw [ht, ← Real.rpow_mul (by positivity), one_div_mul_cancel hr2.ne', Real.rpow_one]
  have hsplit : t ^ r = t ^ (r - 2) * t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htpos]; congr 1; push_cast; ring
  have h1 := h t htpos
  rw [hsplit, htr] at h1
  have ht2 : 0 < t ^ 2 := by positivity
  nlinarith [le_abs_self C]

/-- **No super-quadratic uniform convexity with smoothness.** -/
theorem smooth_uc_exponent {f : E → ℝ} {L : NNReal} {μ r : ℝ} (hE : ∃ e : E, e ≠ 0)
    (hsm : IsSmooth f L) (hμ : 0 < μ)
    (huc : ∀ x y, f x + fderiv ℝ f x (y - x) + μ / 2 * ‖x - y‖ ^ r ≤ f y) : r ≤ 2 := by
  obtain ⟨e, he⟩ := hE
  set u := ‖e‖⁻¹ • e with hu
  have hun : ‖u‖ = 1 := norm_smul_inv_norm he
  apply exponent_le_two (C := L / μ)
  intro t ht
  have h1 := huc 0 (t • u)
  have h2 := hsm.le_quadratic 0 (t • u)
  rw [sub_zero, zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg ht.le, hun, mul_one] at h1
  rw [sub_zero, norm_smul, Real.norm_of_nonneg ht.le, hun, mul_one] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  nlinarith

/-- A nonnegative `L`-smooth function has `‖f'(z)‖ ≤ √(2 L f(z))`. -/
theorem norm_fderiv_le_sqrt {f : E → ℝ} {L : NNReal} (hf0 : ∀ x, 0 ≤ f x) (hsm : IsSmooth f L)
    (hL : 0 < (L : ℝ)) (z : E) : ‖fderiv ℝ f z‖ ≤ Real.sqrt (2 * L * f z) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  set g := fderiv ℝ f z v with hg
  set n := ‖v‖ with hn
  have hnpos : 0 < n := norm_pos_iff.mpr hv
  have key : ∀ s : ℝ, 0 ≤ f z + s * g + L / 2 * s ^ 2 * n ^ 2 := by
    intro s
    have h1 := hsm.le_quadratic z (z + s • v)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs] at h1
    nlinarith [hf0 (z + s • v)]
  have h := key (-g / (L * n ^ 2))
  have hLn : 0 < (L : ℝ) * n ^ 2 := by positivity
  have hg2 : g ^ 2 ≤ 2 * L * f z * n ^ 2 := by
    have e : f z + -g / (L * n ^ 2) * g + L / 2 * (-g / (L * n ^ 2)) ^ 2 * n ^ 2 =
        f z - g ^ 2 / (2 * (L * n ^ 2)) := by field_simp; ring
    rw [e] at h
    have : g ^ 2 / (2 * (L * n ^ 2)) ≤ f z := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  calc Real.sqrt (g ^ 2) ≤ Real.sqrt (2 * L * f z * n ^ 2) := Real.sqrt_le_sqrt hg2
    _ = Real.sqrt (2 * L * f z) * n := by
        rw [Real.sqrt_mul (by have := hf0 z; positivity), Real.sqrt_sq hnpos.le]

/-- The midpoint-type inequality from first-order uniform convexity with exponent `2`. -/
theorem uc_combination {φ : E → StrongDual ℝ E} {F : E → ℝ} {μ : ℝ}
    (huc : ∀ a b, F a + φ a (b - a) + μ / 2 * ‖a - b‖ ^ (2 : ℝ) ≤ F b) (x y : E) {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) :
    F (η • x + (1 - η) • y) + μ / 2 * (η * (1 - η) * ‖x - y‖ ^ 2) ≤ η * F x + (1 - η) * F y := by
  set z₀ := η • x + (1 - η) • y with hz₀
  have h1 := huc z₀ x
  have h2 := huc z₀ y
  have ex : x - z₀ = (1 - η) • (x - y) := by rw [hz₀]; module
  have ey : y - z₀ = (-η) • (x - y) := by rw [hz₀]; module
  have nx : ‖z₀ - x‖ ^ (2 : ℝ) = (1 - η) ^ 2 * ‖x - y‖ ^ 2 := by
    rw [norm_sub_rev, ex, norm_smul, Real.norm_of_nonneg (by linarith [hη.2]), Real.rpow_two,
      mul_pow]
  have ny : ‖z₀ - y‖ ^ (2 : ℝ) = η ^ 2 * ‖x - y‖ ^ 2 := by
    rw [norm_sub_rev, ey, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη.1,
      Real.rpow_two, mul_pow]
  rw [ex, map_smul, smul_eq_mul, nx] at h1
  rw [ey, map_smul, smul_eq_mul, ny] at h2
  nlinarith [hη.1, hη.2, mul_le_mul_of_nonneg_left h1 hη.1,
    mul_le_mul_of_nonneg_left h2 (by linarith [hη.2] : (0 : ℝ) ≤ 1 - η)]

/-- `√(w - a) ≤ √w - a/(2√w)` for `0 ≤ a ≤ w`. -/
theorem sqrt_sub_le {w a : ℝ} (hw : 0 < w) (_ha : 0 ≤ a) (haw : a ≤ w) :
    Real.sqrt (w - a) ≤ Real.sqrt w - a / (2 * Real.sqrt w) := by
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hsq : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  have hy : 0 ≤ Real.sqrt w - a / (2 * Real.sqrt w) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]; nlinarith [hsq]
  have e : (Real.sqrt w - a / (2 * Real.sqrt w)) ^ 2 = w - a + a ^ 2 / (4 * w) := by
    rw [sub_sq, div_pow, mul_pow, hsq]; field_simp; ring
  calc Real.sqrt (w - a) ≤ Real.sqrt ((Real.sqrt w - a / (2 * Real.sqrt w)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [e]
        have : 0 ≤ a ^ 2 / (4 * w) := by positivity
        linarith
    _ = Real.sqrt w - a / (2 * Real.sqrt w) := Real.sqrt_sq hy

/-- **Lemma D.2**, corrected. -/
theorem sublevel_uc_bound {f : E → ℝ} {L : NNReal} {μ r w : ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hsm : IsSmooth f L) (hL : 0 < (L : ℝ)) (hμ : 0 < μ) (hr : 2 ≤ r)
    (huc : ∀ x y, f x + fderiv ℝ f x (y - x) + μ / 2 * ‖x - y‖ ^ r ≤ f y) (hw : 0 < w) :
    IsUniformlyConvexSet {x | f x ≤ w} (μ / (2 * Real.sqrt (2 * w * L))) r := by
  intro x hx y hy η hη z hz
  have hE : ∃ e : E, e ≠ 0 := ⟨z, by rw [← norm_pos_iff, hz]; norm_num⟩
  have hr2 : r = 2 := le_antisymm (smooth_uc_exponent hE hsm hμ huc) hr
  subst hr2
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  set d := ‖x - y‖ with hd
  set z₀ := η • x + (1 - η) • y with hz₀
  set a := μ / 2 * (η * (1 - η) * d ^ 2) with ha
  have hη0 := hη.1
  have hη1 := hη.2
  have ha0 : 0 ≤ a := by
    have : 0 ≤ η * (1 - η) := mul_nonneg hη0 (by linarith)
    positivity
  have hfz : f z₀ + a ≤ w := by
    have := uc_combination (φ := fderiv ℝ f) huc x y hη
    nlinarith
  have hfz0 := hf0 z₀
  have haw : a ≤ w := by linarith
  -- the step `u = η (1 - η) α d² z` keeps `f(z₀ + u) ≤ w`
  set u := (η * (1 - η) * (μ / (2 * Real.sqrt (2 * w * L))) * d ^ (2 : ℝ)) • z with hu
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hun : ‖u‖ = a / (2 * Real.sqrt w) / Real.sqrt ((L : ℝ) / 2) := by
    have h1 : 0 ≤ η * (1 - η) * (μ / (2 * Real.sqrt (2 * w * L))) * d ^ (2 : ℝ) := by
      have : 0 ≤ η * (1 - η) := mul_nonneg hη0 (by linarith)
      positivity
    rw [hu, norm_smul, hz, mul_one, Real.norm_of_nonneg h1, ha, Real.rpow_two,
      show (2 : ℝ) * w * L = 2 * L * w by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    have h2L : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.mpr (by positivity)
    have hL2 : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hL
    have e2 : Real.sqrt (2 * L) = Real.sqrt 2 * Real.sqrt L := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [e2]
    have h22 : 0 < Real.sqrt 2 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hgrad := norm_fderiv_le_sqrt hf0 hsm hL z₀
  have hq := hsm.le_quadratic z₀ (z₀ + u)
  rw [add_sub_cancel_left] at hq
  have hlin : fderiv ℝ f z₀ u ≤ Real.sqrt (2 * L * f z₀) * ‖u‖ :=
    (le_abs_self _).trans (by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hgrad (norm_nonneg _)))
  -- `f(z₀ + u) ≤ (√f(z₀) + √(L/2) ‖u‖)²`
  have hsq : f (z₀ + u) ≤ (Real.sqrt (f z₀) + Real.sqrt ((L : ℝ) / 2) * ‖u‖) ^ 2 := by
    have e1 : Real.sqrt (2 * L * f z₀) = 2 * Real.sqrt (f z₀) * Real.sqrt ((L : ℝ) / 2) := by
      rw [show (2 : ℝ) * L * f z₀ = 4 * (f z₀ * (L / 2)) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_mul hfz0, show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring
    have e2 : Real.sqrt ((L : ℝ) / 2) ^ 2 = L / 2 := Real.sq_sqrt (by positivity)
    have e3 : Real.sqrt (f z₀) ^ 2 = f z₀ := Real.sq_sqrt hfz0
    rw [e1] at hlin
    nlinarith [hlin, hq, e2, e3]
  have hroot : Real.sqrt (f z₀) ≤ Real.sqrt w - a / (2 * Real.sqrt w) :=
    (Real.sqrt_le_sqrt (by linarith)).trans (sqrt_sub_le hw ha0 haw)
  have hL2 : 0 < Real.sqrt ((L : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hcomp : Real.sqrt ((L : ℝ) / 2) * ‖u‖ = a / (2 * Real.sqrt w) := by
    rw [hun]; field_simp
  calc f (z₀ + u) ≤ (Real.sqrt (f z₀) + Real.sqrt ((L : ℝ) / 2) * ‖u‖) ^ 2 := hsq
    _ ≤ (Real.sqrt w - a / (2 * Real.sqrt w) + a / (2 * Real.sqrt w)) ^ 2 := by
        rw [hcomp]
        have h0 : 0 ≤ Real.sqrt (f z₀) + a / (2 * Real.sqrt w) := by positivity
        exact pow_le_pow_left₀ h0 (by linarith) 2
    _ = w := by rw [sub_add_cancel, Real.sq_sqrt hw.le]

/-- **Lemma D.3**, corrected. -/
theorem norm_ball_uc_bound {μ s ρ : ℝ} (hμ : 0 < μ) (hs : 2 ≤ s) (hρ : 0 < ρ)
    (huc : ∀ x y : E, ‖x‖ ^ 2 + fderiv ℝ (fun v : E => ‖v‖ ^ 2) x (y - x) +
      μ / 2 * ‖x - y‖ ^ s ≤ ‖y‖ ^ 2) :
    IsUniformlyConvexSet (Metric.closedBall (0 : E) ρ) (μ / (4 * ρ)) s := by
  intro x hx y hy η hη z hz
  rw [mem_closedBall_zero_iff] at hx hy ⊢
  -- the exponent is `2`: `‖·‖²` is `2`-homogeneous
  have hs2 : s = 2 := by
    apply le_antisymm _ hs
    apply exponent_le_two (C := 2 / μ)
    intro t ht
    have h1 := huc 0 (t • z)
    have h2 := huc 0 (-(t • z))
    simp only [norm_zero, sub_zero, zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg ht.le, hz,
      mul_one, map_neg] at h1 h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith
  subst hs2
  set d := ‖x - y‖ with hd
  set a := μ / 2 * (η * (1 - η) * d ^ 2) with ha
  have hη0 := hη.1
  have hη1 := hη.2
  have ha0 : 0 ≤ a := by
    have : 0 ≤ η * (1 - η) := mul_nonneg hη0 (by linarith)
    positivity
  set z₀ := η • x + (1 - η) • y with hz₀
  have hcomb := uc_combination (φ := fderiv ℝ (fun v : E => ‖v‖ ^ 2)) (F := fun v : E => ‖v‖ ^ 2)
    huc x y hη
  have hx2 : ‖x‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hy2 : ‖y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hz2 : ‖z₀‖ ^ 2 ≤ ρ ^ 2 - a := by nlinarith
  have haρ : a ≤ ρ ^ 2 := by nlinarith [sq_nonneg ‖z₀‖]
  have hzle : ‖z₀‖ ≤ ρ - a / (2 * ρ) := by
    have h1 : ‖z₀‖ ≤ Real.sqrt (ρ ^ 2 - a) := by
      rw [← Real.sqrt_sq (norm_nonneg z₀)]; exact Real.sqrt_le_sqrt hz2
    have h2 := sqrt_sub_le (by positivity : 0 < ρ ^ 2) ha0 haρ
    rw [Real.sqrt_sq hρ.le] at h2
    exact h1.trans h2
  set c := η * (1 - η) * (μ / (4 * ρ)) * d ^ (2 : ℝ) with hc
  have hcval : c = a / (2 * ρ) := by
    rw [hc, ha, Real.rpow_two]; field_simp; ring
  have hc0 : 0 ≤ c := by rw [hcval]; positivity
  calc ‖z₀ + c • z‖ ≤ ‖z₀‖ + ‖c • z‖ := norm_add_le _ _
    _ = ‖z₀‖ + c := by rw [norm_smul, hz, mul_one, Real.norm_of_nonneg hc0]
    _ ≤ ρ := by rw [hcval]; linarith

/-- The closed Euclidean unit disk is not `(1, 2)`-uniformly convex. -/
theorem disk_not_uc : EuclideanDiskNotUC := by
  intro h
  have hnorm : ∀ a b : ℝ, ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    intro a b
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
  have hx : (!₂[3 / 5, 4 / 5] : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, hnorm]
    rw [Real.sqrt_le_one]
    norm_num
  have hy : (!₂[3 / 5, -(4 / 5)] : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, hnorm]
    rw [Real.sqrt_le_one]
    norm_num
  have hz : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [hnorm]; norm_num
  have hp := h _ hx _ hy (1 / 2) ⟨by norm_num, by norm_num⟩ _ hz
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_one] at hp
  have hd : ‖(!₂[3 / 5, 4 / 5] : EuclideanSpace ℝ (Fin 2)) - !₂[3 / 5, -(4 / 5)]‖ ^ (2 : ℝ) =
      64 / 25 := by
    rw [Real.rpow_two, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_two]
    norm_num
  rw [hd] at hp
  simp [Fin.sum_univ_two] at hp
  norm_num at hp

namespace Proof

theorem uniformly_convex_ball : UniformlyConvexBall.{u} := by
  intro E _ _ α q
  exact ⟨fun hα hδ => ball_uc_of_modulus hα hδ, fun r hr h1 => ball_uc_scale hr h1⟩

theorem smooth_uniformly_convex_exponent : SmoothUniformlyConvexExponent.{u} := by
  intro E _ _ f L μ r hE hsm hμ huc
  exact smooth_uc_exponent hE hsm hμ huc

theorem sublevel_uniformly_convex : SublevelUniformlyConvex.{u} := by
  intro E _ _ f L μ r w hf0 hsm hL hμ hr huc hw
  exact sublevel_uc_bound hf0 hsm hL hμ hr huc hw

theorem norm_ball_uniformly_convex : NormBallUniformlyConvex.{u} := by
  intro E _ _ μ s ρ hμ hs hρ huc
  exact norm_ball_uc_bound hμ hs hρ huc

theorem euclidean_disk_not_uc : EuclideanDiskNotUC := disk_not_uc

end Proof

end Lemmata.FWUniformlyConvex
