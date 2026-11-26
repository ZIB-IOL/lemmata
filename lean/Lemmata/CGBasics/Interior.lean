module

public import Lemmata.CGBasics.Statement
public import Lemmata.FrankWolfe.Proof.Rate

@[expose] public section

/-!
# Interior minimizers (Proposition 2.16, Theorem 2.17)

The atom `v` minimizes `f'(x)` over `C`, which contains the ball of radius `r` around `x⋆`, so
`f'(x)(x⋆ - v) ≥ r ‖f'(x)‖`; convexity gives `f'(x)(x - x⋆) ≥ 0`. In Theorem 2.17 the gradient
vanishes at the interior minimizer, so the Frank–Wolfe gap is at most `L D²`, and the step
`g / (L D²)` gives the progress `g² / (2 L D²) ≥ r² ‖f'(x)‖² / (2 L D²) ≥ r² h / (2 L c² D²)`.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaling_interior : ScalingInterior.{u} := by
  intro E _ _ C f r hconv hf xStar hxs hr hball x hx v hv hvmin
  set φ := fderiv ℝ f x with hφ
  have hnn : 0 ≤ φ (x - xStar) := by
    have h1 := add_fderiv_le_of_convexOn hconv hf x xStar
    have h2 := hxs.2 x hx
    have e : φ (xStar - x) = -φ (x - xStar) := by rw [← map_neg, neg_sub]
    rw [← hφ, e] at h1
    linarith
  have hb : ∀ u : E, ‖u‖ ≤ 1 → r * φ u ≤ φ xStar - φ v := by
    intro u hu
    have hmem : xStar - r • u ∈ C := by
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hr.le]
      nlinarith [hu, hr]
    have := hvmin _ hmem
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hM0 : 0 ≤ (φ xStar - φ v) / r := by
    have := hb 0 (by simp)
    simp only [map_zero, mul_zero] at this
    exact div_nonneg (by linarith) hr.le
  have hle : ‖φ‖ ≤ (φ xStar - φ v) / r := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hM0 (fun u hu => ?_)
    have h1 := hb u hu.le
    have h2 := hb (-u) (by rw [norm_neg]; exact hu.le)
    rw [map_neg] at h2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [neg_le, le_div_iff₀ hr]; linarith
    · rw [le_div_iff₀ hr]; linarith
  have hnorm : r * ‖φ‖ ≤ φ xStar - φ v := by
    have := mul_le_mul_of_nonneg_left hle hr.le
    rwa [mul_div_cancel₀ _ hr.ne'] at this
  refine ⟨?_, ?_⟩
  · have e : φ (x - v) = φ (x - xStar) + (φ xStar - φ v) := by rw [map_sub, map_sub]; ring
    rw [e]
    linarith
  · rcases eq_or_lt_of_le (norm_nonneg (x - xStar)) with hd | hd
    · rw [← hd, div_zero]; positivity
    · rw [div_le_iff₀ hd]
      have hop : φ (x - xStar) ≤ ‖φ‖ * ‖x - xStar‖ :=
        (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact φ.le_opNorm _)
      nlinarith [mul_le_mul_of_nonneg_left hop hr.le]

theorem interior_step {C : Set E} {lmo : StrongDual ℝ E → E} {f : E → ℝ} {L : NNReal} {c r : ℝ}
    (h : StandingAssumptions C lmo f L) {xStar : E} (hxs : xStar ∈ minimizers C f) (hr : 0 < r)
    (hball : Metric.closedBall xStar r ⊆ C)
    (hgd : ∀ x ∈ C, f x - f xStar ≤ c ^ 2 * ‖fderiv ℝ f x‖ ^ 2)
    (hgrad0 : fderiv ℝ f xStar = 0) {x x' : E} (hx : x ∈ C)
    (hbound : ∀ γ ∈ Set.Icc (0 : ℝ) 1, f x' ≤ f x - γ * fderiv ℝ f x (x - lmo (fderiv ℝ f x)) +
      γ ^ 2 * L / 2 * ‖lmo (fderiv ℝ f x) - x‖ ^ 2) :
    f x' - f xStar ≤ (1 - r ^ 2 / (2 * L * c ^ 2 * Metric.diam C ^ 2)) * (f x - f xStar) ∧
      f x' ≤ f x := by
  have hbdd := h.isCompact.isBounded
  set D := Metric.diam C with hD
  set φ := fderiv ℝ f x with hφ
  set v := lmo φ with hv
  have hvC : v ∈ C := h.lmo_mem φ
  have hvmin : ∀ y ∈ C, φ v ≤ φ y := (h.isLMO φ).2
  set g := φ (x - v) with hg
  have hg0 : 0 ≤ g := by rw [hg, map_sub]; linarith [hvmin x hx]
  have hdv : ‖v - x‖ ≤ D := by rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd hvC hx
  have hdx : ‖x - xStar‖ ≤ D := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd hx hxs.1
  have hx'x : f x' ≤ f x := by have := hbound 0 ⟨le_rfl, zero_le_one⟩; simpa using this
  refine ⟨?_, hx'x⟩
  have hh0 : 0 ≤ f x - f xStar := sub_nonneg.mpr (hxs.2 x hx)
  have hL0 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ 2 * L * c ^ 2 * D ^ 2) with hden | hden
  · rw [← hden, div_zero, sub_zero, one_mul]; linarith
  · have hK : 0 < (L : ℝ) * D ^ 2 := by
      have : 0 < (L : ℝ) * D ^ 2 * (2 * c ^ 2) := by nlinarith
      exact pos_of_mul_pos_left this (by positivity)
    have hc2 : 0 < c ^ 2 := by
      have : 0 < c ^ 2 * (2 * L * D ^ 2) := by nlinarith
      exact pos_of_mul_pos_left this (by positivity)
    -- the Frank–Wolfe gap is at most `L D²`
    have hgK : g ≤ L * D ^ 2 := by
      have e : g = (φ - fderiv ℝ f xStar) (x - v) := by rw [hgrad0, sub_zero]
      have hlip : ‖φ - fderiv ℝ f xStar‖ ≤ L * ‖x - xStar‖ := by
        have := h.isSmooth.2.dist_le_mul x xStar
        rwa [dist_eq_norm, dist_eq_norm] at this
      have hop : (φ - fderiv ℝ f xStar) (x - v) ≤ ‖φ - fderiv ℝ f xStar‖ * ‖x - v‖ :=
        (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
      rw [norm_sub_rev x v] at hop
      have : ‖φ - fderiv ℝ f xStar‖ * ‖v - x‖ ≤ L * D * D := by
        calc ‖φ - fderiv ℝ f xStar‖ * ‖v - x‖ ≤ (L * ‖x - xStar‖) * ‖v - x‖ :=
              mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
          _ ≤ (L * D) * D := mul_le_mul (mul_le_mul_of_nonneg_left hdx hL0) hdv (norm_nonneg _)
              (by positivity)
      nlinarith
    -- progress with the step `g / (L D²)`
    set K : ℝ := L * D ^ 2 with hKdef
    have hγ : g / K ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg hg0 hK.le, (div_le_one hK).mpr hgK⟩
    have hb := hbound _ hγ
    have hd2 : ‖v - x‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdv 2
    have hquad : (g / K) ^ 2 * L / 2 * ‖v - x‖ ^ 2 ≤ g ^ 2 / (2 * K) := by
      calc (g / K) ^ 2 * L / 2 * ‖v - x‖ ^ 2 ≤ (g / K) ^ 2 * L / 2 * D ^ 2 :=
            mul_le_mul_of_nonneg_left hd2 (by positivity)
        _ = g ^ 2 / (2 * K) := by rw [hKdef]; field_simp
    have hprog : f x' ≤ f x - g ^ 2 / (2 * K) := by
      have e : g / K * g = g ^ 2 / K := by ring
      have e2 : g ^ 2 / K - g ^ 2 / (2 * K) = g ^ 2 / (2 * K) := by field_simp; ring
      linarith
    -- scaling and gradient domination
    have hsc := (scaling_interior C f r h.convexOn h.isSmooth.1 xStar hxs hr hball x hx v hvC
      hvmin).1
    have hsq : r ^ 2 * ‖φ‖ ^ 2 ≤ g ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hsc 2
      rwa [mul_pow] at this
    have hgdx := hgd x hx
    have hfin : r ^ 2 / (2 * L * c ^ 2 * D ^ 2) * (f x - f xStar) ≤ g ^ 2 / (2 * K) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hden (by positivity), hKdef]
      have : r ^ 2 * (f x - f xStar) ≤ c ^ 2 * g ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hgdx (sq_nonneg r)]
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * (L * D ^ 2))]
    nlinarith

theorem linear_rate_interior : LinearRateInterior.{u} := by
  intro E _ _ C lmo f L c r h σ hσ xStar hxs hr hball hgd x₀ hx₀ t
  have hloc : IsLocalMin f xStar := by
    filter_upwards [Metric.closedBall_mem_nhds xStar hr] with y hy using hxs.2 y (hball hy)
  have hgrad0 : fderiv ℝ f xStar = 0 := hloc.fderiv_eq_zero
  set D := Metric.diam C with hD
  set ρ := r ^ 2 / (2 * L * c ^ 2 * D ^ 2) with hρ
  set q := max (1 - ρ) 0 with hq
  have hinit : ∀ y ∈ C, f y - f xStar ≤ L * D ^ 2 / 2 := by
    intro y hy
    have h1 := h.isSmooth.le_quadratic xStar y
    have h0 : fderiv ℝ f xStar (y - xStar) = 0 := by rw [hgrad0]; rfl
    rw [h0, add_zero] at h1
    have hd : dist y xStar ≤ D := Metric.dist_le_diam_of_mem h.isCompact.isBounded hy hxs.1
    rw [dist_eq_norm] at hd
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2)
      (by positivity : (0 : ℝ) ≤ L / 2)
    nlinarith
  have induct : ∀ x : ℕ → E, x 0 = x₀ → (∀ k, x k ∈ C) →
      (∀ k, f (x (k + 1)) - f xStar ≤ (1 - ρ) * (f (x k) - f xStar) ∧ f (x (k + 1)) ≤ f (x k)) →
      ∀ k, f (x k) - f xStar ≤ q ^ k * (L * D ^ 2 / 2) := by
    intro x h0 hmem hstep k
    induction k with
    | zero => rw [pow_zero, one_mul, h0]; exact hinit x₀ hx₀
    | succ k ih =>
      have hkk : 0 ≤ f (x k) - f xStar := sub_nonneg.mpr (hxs.2 _ (hmem k))
      have hqk : f (x (k + 1)) - f xStar ≤ q * (f (x k) - f xStar) := by
        rcases le_total 0 (1 - ρ) with h1 | h1
        · rw [hq, max_eq_left h1]; exact (hstep k).1
        · rw [hq, max_eq_right h1, zero_mul]
          have := (hstep k).1
          nlinarith
      calc f (x (k + 1)) - f xStar ≤ q * (f (x k) - f xStar) := hqk
        _ ≤ q * (q ^ k * (L * D ^ 2 / 2)) := mul_le_mul_of_nonneg_left ih (le_max_right _ _)
        _ = q ^ (k + 1) * (L * D ^ 2 / 2) := by ring
  have hss : ∀ k, ∀ x ∈ C, shortStep lmo (fderiv ℝ f) L k x ∈ Set.Icc (0 : ℝ) 1 := by
    intro k x hx
    have hg : 0 ≤ fderiv ℝ f x (x - lmo (fderiv ℝ f x)) := by
      rw [map_sub]; linarith [(h.isLMO (fderiv ℝ f x)).2 x hx]
    exact ⟨le_min (div_nonneg hg (by positivity)) zero_le_one, min_le_right _ _⟩
  have hmem1 := fwIterates_mem h.convex h.lmo_mem (fderiv ℝ f) hss hx₀
  have hmem2 := fwIterates_mem h.convex h.lmo_mem (fderiv ℝ f)
    (step := fun _ => σ) (fun _ x _ => (hσ x).1) hx₀
  refine ⟨induct _ rfl hmem1 (fun k => interior_step h hxs hr hball hgd hgrad0 (hmem1 k)
    (fun γ hγ => shortStep_le h (hmem1 k) hγ k)) t, induct _ rfl hmem2 (fun k =>
    interior_step h hxs hr hball hgd hgrad0 (hmem2 k)
      (fun γ hγ => ((hσ _).2 γ hγ).trans (h.isSmooth.progress _ _ γ))) t⟩

end Proof

end Lemmata.CGBasics
