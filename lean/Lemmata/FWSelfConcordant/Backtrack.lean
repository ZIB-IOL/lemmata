module

public import Lemmata.FWSelfConcordant.Monotonic
public import Lemmata.CGBasics.UniformlyConvex

@[expose] public section

/-!
# Frank–Wolfe with backtracking (Theorems 2.11, 2.15 and 2.16)

The line search returns the minimizer `γ_t` over `[0, 1]` of the quadratic model with an estimate
`L_t ≤ L̃`, so every step does at least as well as each `s ∈ [0, 1]` in the model with `L̃`, and
`f` decreases. The rates then follow as for short steps: from the scaling inequality at an
interior minimizer and the PL inequality of local strong convexity (Theorem 2.11), and from the
scaling inequality of uniformly convex sets with the contraction lemma of the basics entry
(Theorems 2.15 and 2.16).
-/

namespace Lemmata.FWSelfConcordant

open Lemmata.FrankWolfe

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {C D : Set E} {f : E → ℝ}
  {Lmax : ℝ} {x v : ℕ → E} {γ : ℕ → ℝ}

/-- One step of the backtracking run: the step size lies in `[0, 1]`, and every `s ∈ [0, 1]` does
no better in the quadratic model with `L̃`. -/
theorem bfw_step (hrun : IsBFWRun C D f Lmax x v γ) (t : ℕ) (hxC : x t ∈ C) :
    γ t ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      s * fderiv ℝ f (x t) (x t - v t) - s ^ 2 * Lmax / 2 * ‖v t - x t‖ ^ 2 ≤
        f (x t) - f (x (t + 1)) := by
  obtain ⟨-, hvmin, -, -, L, hL, hLm, hγ, hdec⟩ := hrun.2.2 t
  set g := fderiv ℝ f (x t) (x t - v t) with hg
  set n := ‖v t - x t‖ with hn
  have hg0 : 0 ≤ g := by have := hvmin (x t) hxC; rw [hg, map_sub]; linarith
  have hγ01 : γ t ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hγ]
    exact ⟨le_min zero_le_one (div_nonneg hg0 (by positivity)), min_le_left _ _⟩
  refine ⟨hγ01, fun s hs => ?_⟩
  -- `γ_t` maximizes `s ↦ s g - L s² n²/2` over `[0, 1]`
  have hmax : s * g - L * s ^ 2 / 2 * n ^ 2 ≤ γ t * g - L * γ t ^ 2 / 2 * n ^ 2 := by
    rcases eq_or_lt_of_le (norm_nonneg (v t - x t)) with hn0 | hnpos
    · have hn00 : n = 0 := hn0.symm
      have hvx : v t = x t := sub_eq_zero.mp (norm_eq_zero.mp hn00)
      have hg00 : g = 0 := by rw [hg, hvx, sub_self, map_zero]
      rw [hn00, hg00]; simp
    · have hLn : 0 < L * n ^ 2 := by positivity
      by_cases hbig : L * n ^ 2 ≤ g
      · have h1 : γ t = 1 := by
          rw [hγ]; exact min_eq_left (by rw [le_div_iff₀ hLn]; linarith)
        rw [h1]
        have key : 1 * g - L * 1 ^ 2 / 2 * n ^ 2 - (s * g - L * s ^ 2 / 2 * n ^ 2) =
            (1 - s) * (g - L * n ^ 2) + (1 - s) ^ 2 * (L * n ^ 2) / 2 := by ring
        have k1 : 0 ≤ (1 - s) * (g - L * n ^ 2) :=
          mul_nonneg (by linarith [hs.2]) (by linarith)
        have k2 : 0 ≤ (1 - s) ^ 2 * (L * n ^ 2) / 2 := by positivity
        linarith
      · push Not at hbig
        have h1 : γ t = g / (L * n ^ 2) := by
          rw [hγ]; exact min_eq_right (by rw [div_le_one hLn]; exact hbig.le)
        rw [h1]
        have hn0' : n ≠ 0 := hnpos.ne'
        have hL0 : L ≠ 0 := hL.ne'
        have key : g / (L * n ^ 2) * g - L * (g / (L * n ^ 2)) ^ 2 / 2 * n ^ 2 -
            (s * g - L * s ^ 2 / 2 * n ^ 2) = L * n ^ 2 / 2 * (s - g / (L * n ^ 2)) ^ 2 := by
          field_simp; ring
        nlinarith [sq_nonneg (s - g / (L * n ^ 2))]
  have hmono : - (s ^ 2 * Lmax / 2 * n ^ 2) ≤ - (L * s ^ 2 / 2 * n ^ 2) := by
    have : L * s ^ 2 / 2 * n ^ 2 ≤ s ^ 2 * Lmax / 2 * n ^ 2 := by
      have hs2 : 0 ≤ s ^ 2 * n ^ 2 / 2 := by positivity
      nlinarith
    linarith
  linarith

theorem bfw_invariant (hC : Convex ℝ C) (hrun : IsBFWRun C D f Lmax x v γ) :
    ∀ t, x t ∈ C ∧ x t ∈ D ∧ f (x t) ≤ f (x 0) := by
  intro t
  induction t with
  | zero => exact ⟨hrun.1, hrun.2.1, le_rfl⟩
  | succ t ih =>
    obtain ⟨hvC, -, hx, hxD, -⟩ := hrun.2.2 t
    obtain ⟨hγ, hst⟩ := bfw_step hrun t ih.1
    have hdec := hst 0 ⟨le_rfl, zero_le_one⟩
    refine ⟨by rw [hx]; exact hC.add_smul_sub_mem ih.1 hvC hγ, hxD, ?_⟩
    have : f (x (t + 1)) ≤ f (x t) := by nlinarith
    linarith [ih.2.2]

theorem bfw_gap (hC : Convex ℝ C) (hconv : ConvexOn ℝ (C ∩ D) f)
    (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) {xStar : E} (hxs : xStar ∈ minimizers (C ∩ D) f)
    (hrun : IsBFWRun C D f Lmax x v γ) (t : ℕ) :
    0 ≤ f (x t) - f xStar ∧ f (x t) - f xStar ≤ fderiv ℝ f (x t) (x t - v t) := by
  obtain ⟨hxC, hxD, -⟩ := bfw_invariant hC hrun t
  obtain ⟨-, hvmin, -⟩ := hrun.2.2 t
  refine ⟨sub_nonneg.mpr (hxs.2 _ ⟨hxC, hxD⟩), ?_⟩
  have h1 := convexOn_add_fderiv_le hconv ⟨hxC, hxD⟩ (hdiff _ ⟨hxC, hxD⟩) hxs.1
  have h2 := hvmin xStar hxs.1.1
  rw [map_sub] at h1 ⊢
  linarith

/-- The scaling inequality at an interior minimizer. -/
theorem ball_scaling {ψ : StrongDual ℝ E} {x v xStar : E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall xStar r ⊆ C) (hx : x ∈ C) (hvmin : ∀ y ∈ C, ψ v ≤ ψ y)
    (hxs : 0 ≤ ψ (x - xStar)) : r * ‖ψ‖ ≤ ψ (x - v) := by
  have hbound : ∀ z : E, ψ z ≤ ψ (x - v) / r * ‖z‖ := by
    intro z
    rcases eq_or_ne z 0 with hz | hz
    · rw [hz, map_zero, norm_zero, mul_zero]
    · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      set w := (r / ‖z‖) • z with hw
      have hwn : ‖w‖ = r := by
        rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
      have hmem : xStar - w ∈ C := hball (by rw [Metric.mem_closedBall, dist_eq_norm,
        show xStar - w - xStar = -w by abel, norm_neg, hwn])
      have h1 := hvmin _ hmem
      have h2 : ψ (x - v) = ψ (x - xStar) + ψ w + (ψ (xStar - w) - ψ v) := by
        simp only [map_sub]; ring
      have h3 : ψ w ≤ ψ (x - v) := by linarith
      rw [hw, map_smul, smul_eq_mul] at h3
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      have : r / ‖z‖ * ψ z * ‖z‖ = r * ψ z := by field_simp
      nlinarith
  have hM : 0 ≤ ψ (x - v) / r := by
    have := hvmin x hx
    apply div_nonneg _ hr.le
    rw [map_sub]; linarith
  have hop : ‖ψ‖ ≤ ψ (x - v) / r := by
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun z => ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := hbound (-z); rw [map_neg, norm_neg] at this; linarith
    · exact hbound z
  rw [le_div_iff₀ hr] at hop
  linarith

/-- The PL inequality from strong convexity at the pair `(x, x⋆)`. -/
theorem pl_of_strong {ψ : StrongDual ℝ E} {fx fs μ : ℝ} {d : E} (hμ : 0 < μ)
    (h : fx + ψ d + μ / 2 * ‖d‖ ^ 2 ≤ fs) : fx - fs ≤ ‖ψ‖ ^ 2 / (2 * μ) := by
  have h1 : -ψ d ≤ ‖ψ‖ * ‖d‖ := by
    have := ψ.le_opNorm d
    rw [Real.norm_eq_abs] at this
    linarith [neg_le_abs (ψ d)]
  have h2 : ‖ψ‖ * ‖d‖ - μ / 2 * ‖d‖ ^ 2 ≤ ‖ψ‖ ^ 2 / (2 * μ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖ψ‖ - μ * ‖d‖)]
  linarith

theorem interior_linear_bound (hCc : IsCompact C) (hC : Convex ℝ C)
    (hconv : ConvexOn ℝ (C ∩ D) f) (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) {xStar : E}
    (hxs : xStar ∈ minimizers (C ∩ D) f) (hL : 0 < Lmax) {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r)
    (hball : Metric.closedBall xStar r ⊆ C)
    (hsc : ∀ y ∈ C ∩ D, f y ≤ f (x 0) → ∀ z ∈ C ∩ D, f z ≤ f (x 0) →
      f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    (hrun : IsBFWRun C D f Lmax x v γ) :
    ∀ t : ℕ, f (x t) - f xStar ≤
      (1 - 1 / 2 * min 1 (μ * r ^ 2 / (Lmax * Metric.diam C ^ 2))) ^ t * (f (x 0) - f xStar) := by
  set a := μ * r ^ 2 / (Lmax * Metric.diam C ^ 2) with ha
  set ρ := 1 - 1 / 2 * min 1 a with hρ
  have ha0 : 0 ≤ a := by positivity
  have hmin1 : min 1 a ≤ 1 := min_le_left _ _
  have hρ0 : 0 ≤ ρ := by linarith
  have hbdd := hCc.isBounded
  have hxs0 : f xStar ≤ f (x 0) :=
    hxs.2 _ ⟨(bfw_invariant hC hrun 0).1, (bfw_invariant hC hrun 0).2.1⟩
  have hstep : ∀ t, f (x (t + 1)) - f xStar ≤ ρ * (f (x t) - f xStar) := by
    intro t
    obtain ⟨hxC, hxD, hxf⟩ := bfw_invariant hC hrun t
    obtain ⟨hvC, hvmin, -⟩ := hrun.2.2 t
    obtain ⟨hh0, hhg⟩ := bfw_gap hC hconv hdiff hxs hrun t
    obtain ⟨-, hst⟩ := bfw_step hrun t hxC
    set g := fderiv ℝ f (x t) (x t - v t) with hg
    set h := f (x t) - f xStar with hh
    set n := ‖v t - x t‖ with hn
    set Dm := Metric.diam C with hDm
    have hnD : n ≤ Dm := by rw [hn, ← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd hvC hxC
    have hn0 : 0 ≤ n := norm_nonneg _
    have hn2 : n ^ 2 ≤ Dm ^ 2 := pow_le_pow_left₀ hn0 hnD 2
    have hxpos : 0 ≤ fderiv ℝ f (x t) (x t - xStar) := by
      have h1 := convexOn_add_fderiv_le hconv ⟨hxC, hxD⟩ (hdiff _ ⟨hxC, hxD⟩) hxs.1
      have h2 := hxs.2 _ ⟨hxC, hxD⟩
      rw [map_sub] at h1 ⊢; linarith
    have hsc' := ball_scaling hr hball hxC hvmin hxpos
    have hpl : h ≤ ‖fderiv ℝ f (x t)‖ ^ 2 / (2 * μ) :=
      pl_of_strong hμ (hsc (x t) ⟨hxC, hxD⟩ hxf xStar hxs.1 hxs0)
    have hprog : 1 / 2 * min 1 a * h ≤ f (x t) - f (x (t + 1)) := by
      have hΔ0 := hst 0 ⟨le_rfl, zero_le_one⟩
      simp only [zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div] at hΔ0
      rcases eq_or_lt_of_le (Metric.diam_nonneg : 0 ≤ Dm) with hD0 | hDpos
      · have hnz : n = 0 := le_antisymm (by rw [hD0]; exact hnD) hn0
        have hvx : v t = x t := sub_eq_zero.mp (norm_eq_zero.mp hnz)
        have hg0 : g = 0 := by rw [hg, hvx, sub_self, map_zero]
        have hh00 : h = 0 := le_antisymm (by linarith) hh0
        rw [hh00, mul_zero]; exact hΔ0
      · by_cases hbig : Lmax * Dm ^ 2 ≤ g
        · have h1 := hst 1 ⟨zero_le_one, le_rfl⟩
          have h2 : Lmax * n ^ 2 ≤ Lmax * Dm ^ 2 := mul_le_mul_of_nonneg_left hn2 hL.le
          have h3 : 1 / 2 * min 1 a * h ≤ 1 / 2 * h := by
            have := mul_le_mul_of_nonneg_right hmin1 hh0; linarith
          linarith
        · push Not at hbig
          have hLD : 0 < Lmax * Dm ^ 2 := by positivity
          have hg0 : 0 ≤ g := le_trans hh0 hhg
          set s := g / (Lmax * Dm ^ 2) with hs
          have hs01 : s ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨div_nonneg hg0 hLD.le, by rw [hs, div_le_one hLD]; exact hbig.le⟩
          have h1 := hst s hs01
          have h2 : g ^ 2 / (2 * Lmax * Dm ^ 2) ≤ s * g - s ^ 2 * Lmax / 2 * n ^ 2 := by
            have i1 : s ^ 2 * Lmax / 2 * n ^ 2 ≤ s ^ 2 * Lmax / 2 * Dm ^ 2 :=
              mul_le_mul_of_nonneg_left hn2 (by positivity)
            have e : s * g - s ^ 2 * Lmax / 2 * Dm ^ 2 = g ^ 2 / (2 * Lmax * Dm ^ 2) := by
              rw [hs]; field_simp; ring
            linarith
          have h3 : r ^ 2 * (2 * μ * h) ≤ g ^ 2 := by
            have hsq := pow_le_pow_left₀ (by positivity) hsc' 2
            have i1 : 2 * μ * h ≤ ‖fderiv ℝ f (x t)‖ ^ 2 := by
              rw [le_div_iff₀ (by positivity)] at hpl; linarith
            have i2 : r ^ 2 * (2 * μ * h) ≤ r ^ 2 * ‖fderiv ℝ f (x t)‖ ^ 2 :=
              mul_le_mul_of_nonneg_left i1 (by positivity)
            rw [mul_pow] at hsq
            linarith
          have h4 : a * h ≤ g ^ 2 / (2 * Lmax * Dm ^ 2) := by
            rw [ha, le_div_iff₀ (by positivity)]
            have hDm0 : Dm ≠ 0 := hDpos.ne'
            have hL0 : Lmax ≠ 0 := hL.ne'
            have e : μ * r ^ 2 / (Lmax * Dm ^ 2) * h * (2 * Lmax * Dm ^ 2) =
                r ^ 2 * (2 * μ * h) := by field_simp
            rw [e]; exact h3
          have h5 : 1 / 2 * min 1 a * h ≤ a * h := by
            have := mul_le_mul_of_nonneg_right (min_le_right 1 a) hh0
            nlinarith
          linarith
    have e : f (x (t + 1)) - f xStar = h - (f (x t) - f (x (t + 1))) := by rw [hh]; ring
    rw [e, hρ]
    have : (1 - 1 / 2 * min 1 a) * h = h - 1 / 2 * min 1 a * h := by ring
    linarith
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    calc f (x (t + 1)) - f xStar ≤ ρ * (f (x t) - f xStar) := hstep t
      _ ≤ ρ * (ρ ^ t * (f (x 0) - f xStar)) := mul_le_mul_of_nonneg_left ih hρ0
      _ = ρ ^ (t + 1) * (f (x 0) - f xStar) := by ring

/-- The progress of a backtracking step over a uniformly convex set, with a lower bound `β` on
`κ ‖f'(x_t)‖`. -/
theorem uc_bfw_progress (hC : Convex ℝ C) {κ q : ℝ} (hUC : IsUniformlyConvexSet C κ q)
    (hq : 2 ≤ q) (hconv : ConvexOn ℝ (C ∩ D) f) (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y)
    {xStar : E} (hxs : xStar ∈ minimizers (C ∩ D) f) (hL : 0 < Lmax)
    (hrun : IsBFWRun C D f Lmax x v γ) (t : ℕ) {β : ℝ} (hβ : 0 < β)
    (hβle : β ≤ κ * ‖fderiv ℝ f (x t)‖) :
    (f (x t) - f xStar) * min (1 / 2) (β ^ (2 / q) * (f (x t) - f xStar) ^ (1 - 2 / q) /
      (2 * Lmax)) ≤ f (x t) - f (x (t + 1)) := by
  obtain ⟨hxC, -, -⟩ := bfw_invariant hC hrun t
  obtain ⟨hvC, hvmin, -⟩ := hrun.2.2 t
  obtain ⟨hh0, hhg⟩ := bfw_gap hC hconv hdiff hxs hrun t
  obtain ⟨-, hst⟩ := bfw_step hrun t hxC
  have hscal := Lemmata.CGBasics.Proof.uniformly_convex_scaling C κ q hUC (fderiv ℝ f (x t)) (v t)
    hvC hvmin (x t) hxC
  have hscal' : β * ‖v t - x t‖ ^ q ≤ fderiv ℝ f (x t) (x t - v t) := by
    rw [norm_sub_rev]
    calc β * ‖x t - v t‖ ^ q ≤ κ * ‖fderiv ℝ f (x t)‖ * ‖x t - v t‖ ^ q :=
          mul_le_mul_of_nonneg_right hβle (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ _ := hscal
  exact Lemmata.CGBasics.Proof.uc_progress hL hq hβ hhg hh0 (norm_nonneg _) hscal' hst

/-- The constant of the contraction lemma in the paper's form:
`(1/2/(B^{m/q}/(2L)))^{1/(1-m/q)} = (L^q/B^m)^{1/(q-m)}`. -/
theorem tau_identity {L B q m : ℝ} (hL : 0 < L) (hB : 0 < B) (hm : 0 < m) (hqm : m < q) :
    (1 / 2 / (B ^ (m / q) / (2 * L))) ^ (1 / (1 - m / q)) = (L ^ q / B ^ m) ^ (1 / (q - m)) := by
  have hq : 0 < q := lt_trans hm hqm
  have hBm : 0 < B ^ (m / q) := Real.rpow_pos_of_pos hB _
  have e1 : 1 / 2 / (B ^ (m / q) / (2 * L)) = L / B ^ (m / q) := by field_simp
  have e2 : 1 / (1 - m / q) = q / (q - m) := by
    have : q - m ≠ 0 := by linarith
    field_simp
  rw [e1, e2, Real.div_rpow hL.le hBm.le, ← Real.rpow_mul hB.le,
    Real.div_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hB.le _), ← Real.rpow_mul hL.le,
    ← Real.rpow_mul hB.le]
  congr 2
  · field_simp
  · have : q - m ≠ 0 := by linarith
    field_simp

theorem uc_gradient_bound (hC : Convex ℝ C) {κ q c : ℝ}
    (hUC : IsUniformlyConvexSet C κ q) (hκ : 0 < κ) (hq : 2 ≤ q) (hconv : ConvexOn ℝ (C ∩ D) f)
    (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) {xStar : E} (hxs : xStar ∈ minimizers (C ∩ D) f)
    (hL : 0 < Lmax) (hc : 0 < c) (hgrad : ∀ y ∈ C ∩ D, c ≤ ‖fderiv ℝ f y‖)
    (hrun : IsBFWRun C D f Lmax x v γ) :
    (q = 2 → ∀ t : ℕ, f (x t) - f xStar ≤
      (1 - 1 / 2 * min 1 (κ * c / Lmax)) ^ t * (f (x 0) - f xStar)) ∧
    (2 < q →
      let τ := (Lmax ^ q / (κ * c) ^ 2) ^ (1 / (q - 2))
      let t₀ : ℤ := max (⌊Real.logb (1 / 2) (τ / (f (x 0) - f xStar))⌋ + 2) 1
      ∀ t : ℕ, 1 ≤ t →
        ((t : ℤ) < t₀ → f (x t) - f xStar ≤ (f (x 0) - f xStar) * (1 / 2) ^ (t - 1)) ∧
        (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
          τ / (1 + (q - 2) / (2 * q) * ((t : ℝ) - (t₀ : ℝ))) ^ (q / (q - 2)))) := by
  have hprog : ∀ t, (f (x t) - f xStar) * min (1 / 2) ((κ * c) ^ (2 / q) *
      (f (x t) - f xStar) ^ (1 - 2 / q) / (2 * Lmax)) ≤ f (x t) - f (x (t + 1)) := by
    intro t
    obtain ⟨hxC, hxD, -⟩ := bfw_invariant hC hrun t
    exact uc_bfw_progress hC hUC hq hconv hdiff hxs hL hrun t (by positivity)
      (mul_le_mul_of_nonneg_left (hgrad _ ⟨hxC, hxD⟩) hκ.le)
  have hmono : ∀ t, f (x (t + 1)) - f xStar ≤ f (x t) - f xStar := by
    intro t
    obtain ⟨hxC, -, -⟩ := bfw_invariant hC hrun t
    have := (bfw_step hrun t hxC).2 0 ⟨le_rfl, zero_le_one⟩
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero] at this
    linarith
  refine ⟨fun hq2 => ?_, fun hq2 => ?_⟩
  · set ρ := 1 - 1 / 2 * min 1 (κ * c / Lmax) with hρ
    have hρ0 : 0 ≤ ρ := by have : min 1 (κ * c / Lmax) ≤ 1 := min_le_left _ _; linarith
    have hstep : ∀ t, f (x (t + 1)) - f xStar ≤ ρ * (f (x t) - f xStar) := by
      intro t
      have h1 := hprog t
      rw [hq2, div_self two_ne_zero, Real.rpow_one, sub_self, Real.rpow_zero, mul_one] at h1
      have e : 1 / 2 * min 1 (κ * c / Lmax) = min (1 / 2) (κ * c / (2 * Lmax)) := by
        rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]; congr 1 <;> ring
      rw [hρ, e]
      nlinarith
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc f (x (t + 1)) - f xStar ≤ ρ * (f (x t) - f xStar) := hstep t
        _ ≤ ρ * (ρ ^ t * (f (x 0) - f xStar)) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (t + 1) * (f (x 0) - f xStar) := by ring
  · intro τ t₀ t ht
    have hτ0 : 0 ≤ τ := Real.rpow_nonneg (by positivity) _
    have hq0 : 0 < q := by linarith
    have ha : 0 < 1 - 2 / q := by rw [sub_pos, div_lt_one hq0]; exact hq2
    have hanti : ∀ s, f (x s) - f xStar ≤ f (x 0) - f xStar := by
      intro s
      induction s with
      | zero => exact le_rfl
      | succ s ih => exact le_trans (hmono s) ih
    rcases (bfw_gap hC hconv hdiff hxs hrun 0).1.eq_or_lt with h00 | h0pos
    · have hz : f (x t) - f xStar = 0 :=
        le_antisymm (by rw [h00]; exact hanti t) (bfw_gap hC hconv hdiff hxs hrun t).1
      refine ⟨fun _ => by rw [hz, ← h00]; simp, fun hge => ?_⟩
      rw [hz]
      have hge' : (t₀ : ℝ) ≤ t := by exact_mod_cast hge
      apply div_nonneg hτ0 (Real.rpow_nonneg _ _)
      have : 0 ≤ (q - 2) / (2 * q) := div_nonneg (by linarith) (by linarith)
      nlinarith
    · have hra := Lemmata.CGBasics.Proof.rate_assembly (fun s => f (x s) - f xStar)
        (f (x 0) - f xStar) ((κ * c) ^ (2 / q) / (2 * Lmax)) (1 - 2 / q) h0pos (by positivity) ha
        (fun s => (bfw_gap hC hconv hdiff hxs hrun s).1) hmono (hanti 1)
        (fun s _ _ => by
          have := hprog s
          rw [show (κ * c) ^ (2 / q) / (2 * Lmax) * (f (x s) - f xStar) ^ (1 - 2 / q) =
            (κ * c) ^ (2 / q) * (f (x s) - f xStar) ^ (1 - 2 / q) / (2 * Lmax) by ring]
          linarith) t ht
      have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      have ea : 1 / 2 * (1 - 2 / q) = (q - 2) / (2 * q) := by field_simp
      have eb : 1 / (1 - 2 / q) = q / (q - 2) := by
        have : q - 2 ≠ 0 := by linarith
        field_simp
      have eτ : (1 / 2 / ((κ * c) ^ (2 / q) / (2 * Lmax))) ^ (q / (q - 2)) = τ := by
        rw [← eb, tau_identity hL (by positivity) (by norm_num) hq2, Real.rpow_two]
      simp only [e1, ea, eb] at hra
      rw [eτ] at hra
      exact hra

theorem uc_strong_bound (hC : Convex ℝ C) {κ q μ : ℝ}
    (hUC : IsUniformlyConvexSet C κ q) (hκ : 0 < κ) (hq : 2 ≤ q) (hconv : ConvexOn ℝ (C ∩ D) f)
    (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) {xStar : E} (hxs : xStar ∈ minimizers (C ∩ D) f)
    (hL : 0 < Lmax) (hμ : 0 < μ)
    (hsc : ∀ y ∈ C ∩ D, f y ≤ f (x 0) → ∀ z ∈ C ∩ D, f z ≤ f (x 0) →
      f y + fderiv ℝ f y (z - y) + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    (hrun : IsBFWRun C D f Lmax x v γ) :
    let τ := (Lmax ^ q / (κ ^ 2 * μ)) ^ (1 / (q - 1))
    let t₀ : ℤ := max (⌊Real.logb (1 / 2) (τ / (f (x 0) - f xStar))⌋ + 2) 1
    ∀ t : ℕ, 1 ≤ t →
      ((t : ℤ) < t₀ → f (x t) - f xStar ≤ (f (x 0) - f xStar) * (1 / 2) ^ (t - 1)) ∧
      (t₀ ≤ (t : ℤ) → f (x t) - f xStar ≤
        τ / (1 + (q - 1) / (2 * q) * ((t : ℝ) - (t₀ : ℝ))) ^ (q / (q - 1))) := by
  intro τ t₀ t ht
  have hq0 : 0 < q := by linarith
  have hτ0 : 0 ≤ τ := Real.rpow_nonneg (by positivity) _
  have ha : 0 < 1 - 1 / q := by rw [sub_pos, div_lt_one hq0]; linarith
  have hxs0 : f xStar ≤ f (x 0) :=
    hxs.2 _ ⟨(bfw_invariant hC hrun 0).1, (bfw_invariant hC hrun 0).2.1⟩
  have hmono : ∀ s, f (x (s + 1)) - f xStar ≤ f (x s) - f xStar := by
    intro s
    obtain ⟨hxC, -, -⟩ := bfw_invariant hC hrun s
    have := (bfw_step hrun s hxC).2 0 ⟨le_rfl, zero_le_one⟩
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero] at this
    linarith
  have hanti : ∀ s, f (x s) - f xStar ≤ f (x 0) - f xStar := by
    intro s
    induction s with
    | zero => exact le_rfl
    | succ s ih => exact le_trans (hmono s) ih
  set c₂ := (κ ^ 2 * μ) ^ (1 / q) / (2 * Lmax) with hc₂
  have hprog : ∀ s, 1 ≤ s → 0 < f (x s) - f xStar →
      (f (x s) - f xStar) * min (1 / 2) (c₂ * (f (x s) - f xStar) ^ (1 - 1 / q)) ≤
        (f (x s) - f xStar) - (f (x (s + 1)) - f xStar) := by
    intro s _ hpos
    obtain ⟨hxC, hxD, hxf⟩ := bfw_invariant hC hrun s
    set h := f (x s) - f xStar with hh
    have hpl : h ≤ ‖fderiv ℝ f (x s)‖ ^ 2 / (2 * μ) :=
      pl_of_strong hμ (hsc (x s) ⟨hxC, hxD⟩ hxf xStar hxs.1 hxs0)
    have hμh : 0 < μ * h := by positivity
    have hβle : κ * Real.sqrt (μ * h) ≤ κ * ‖fderiv ℝ f (x s)‖ := by
      apply mul_le_mul_of_nonneg_left _ hκ.le
      have h1 : μ * h ≤ ‖fderiv ℝ f (x s)‖ ^ 2 := by
        rw [le_div_iff₀ (by positivity)] at hpl; nlinarith
      calc Real.sqrt (μ * h) ≤ Real.sqrt (‖fderiv ℝ f (x s)‖ ^ 2) := Real.sqrt_le_sqrt h1
        _ = ‖fderiv ℝ f (x s)‖ := Real.sqrt_sq (norm_nonneg _)
    have hp := uc_bfw_progress hC hUC hq hconv hdiff hxs hL hrun s (by positivity) hβle
    have e1 : (κ * Real.sqrt (μ * h)) ^ (2 / q) = κ ^ (2 / q) * μ ^ (1 / q) * h ^ (1 / q) := by
      rw [Real.mul_rpow hκ.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hμh.le,
        show (1 / 2 : ℝ) * (2 / q) = 1 / q by field_simp, Real.mul_rpow hμ.le hpos.le]
      ring
    have e2 : (κ ^ 2 * μ) ^ (1 / q) = κ ^ (2 / q) * μ ^ (1 / q) := by
      rw [Real.mul_rpow (by positivity) hμ.le, ← Real.rpow_natCast κ 2, ← Real.rpow_mul hκ.le]
      congr 2
      push_cast
      ring
    have e3 : h ^ (1 / q) * h ^ (1 - 2 / q) = h ^ (1 - 1 / q) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    have e : (κ * Real.sqrt (μ * h)) ^ (2 / q) * h ^ (1 - 2 / q) / (2 * Lmax) =
        c₂ * h ^ (1 - 1 / q) := by
      rw [e1, hc₂, e2, ← e3]; ring
    rw [e] at hp
    linarith
  rcases (bfw_gap hC hconv hdiff hxs hrun 0).1.eq_or_lt with h00 | h0pos
  · have hz : f (x t) - f xStar = 0 :=
      le_antisymm (by rw [h00]; exact hanti t) (bfw_gap hC hconv hdiff hxs hrun t).1
    refine ⟨fun _ => by rw [hz, ← h00]; simp, fun hge => ?_⟩
    rw [hz]
    have hge' : (t₀ : ℝ) ≤ t := by exact_mod_cast hge
    apply div_nonneg hτ0 (Real.rpow_nonneg _ _)
    have : 0 ≤ (q - 1) / (2 * q) := div_nonneg (by linarith) (by linarith)
    nlinarith
  · have hra := Lemmata.CGBasics.Proof.rate_assembly (fun s => f (x s) - f xStar)
      (f (x 0) - f xStar) c₂ (1 - 1 / q) h0pos (by positivity) ha
      (fun s => (bfw_gap hC hconv hdiff hxs hrun s).1) hmono (hanti 1) hprog t ht
    have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    have ea : 1 / 2 * (1 - 1 / q) = (q - 1) / (2 * q) := by field_simp
    have eb : 1 / (1 - 1 / q) = q / (q - 1) := by
      have : q - 1 ≠ 0 := by linarith
      field_simp
    have eτ : (1 / 2 / c₂) ^ (q / (q - 1)) = τ := by
      rw [← eb, hc₂, tau_identity hL (by positivity) one_pos (by linarith), Real.rpow_one]
    simp only [e1, ea, eb] at hra
    rw [eτ] at hra
    exact hra

namespace Proof

theorem interior_linear_rate : InteriorLinearRate.{u} := by
  intro E _ _ C D f Lmax μ r x v γ xStar hCc hC hconv hdiff hxs hL hμ hr hball hsc hrun t
  exact interior_linear_bound hCc hC hconv hdiff hxs hL hμ hr hball hsc hrun t

theorem uniformly_convex_gradient_rate : UniformlyConvexGradientRate.{u} := by
  intro E _ _ C D f Lmax κ q c x v γ xStar _ hC hUC hκ hq hconv hdiff hxs hL hc hgrad hrun
  exact uc_gradient_bound hC hUC hκ hq hconv hdiff hxs hL hc hgrad hrun

theorem uniformly_convex_strong_rate : UniformlyConvexStrongRate.{u} := by
  intro E _ _ C D f Lmax κ q μ x v γ xStar _ hC hUC hκ hq hconv hdiff hxs hL hμ hsc hrun
  exact uc_strong_bound hC hUC hκ hq hconv hdiff hxs hL hμ hsc hrun

end Proof

end Lemmata.FWSelfConcordant
