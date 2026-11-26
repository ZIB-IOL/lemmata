module

public import Lemmata.CGBasics.Statement
public import Lemmata.FrankWolfe.Proof.Calculus

@[expose] public section

/-!
# Smoothness, the Frank–Wolfe gap and strong convexity (Lemma 1.7, Proposition 1.12, Lemma 2.13)

Co-coercivity follows from the quadratic upper bound and convexity alone: compare the bound at `y`
with first-order convexity at `x`, at a point `y - (r/L) w` for a vector `w` nearly attaining the
norm of `f'(y) - f'(x)`. Adding it for `(x, y)` and `(y, x)` gives the Lipschitz bound.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cocoercive_of_bound {f : E → ℝ} {L : NNReal} (hconv : ConvexOn ℝ Set.univ f)
    (hf : Differentiable ℝ f)
    (hq : ∀ x y : E, f y ≤ f x + fderiv ℝ f x (y - x) + L / 2 * ‖y - x‖ ^ 2)
    (hL : 0 < (L : ℝ)) (x y : E) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ^ 2 ≤ 2 * L * (f y - f x - fderiv ℝ f x (y - x)) := by
  set φ' := fderiv ℝ f y - fderiv ℝ f x with hφ'
  set A := 2 * (L : ℝ) * (f y - f x - fderiv ℝ f x (y - x)) with hA
  have claim : ∀ r : ℝ, 0 ≤ r → r < ‖φ'‖ → r ^ 2 ≤ A := by
    intro r hr0 hr
    obtain ⟨u, hu, hru⟩ := φ'.exists_lt_apply_of_lt_opNorm hr
    obtain ⟨w, hw, hrw⟩ : ∃ w : E, ‖w‖ ≤ 1 ∧ r < φ' w := by
      rcases le_or_gt 0 (φ' u) with h | h
      · exact ⟨u, hu.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h] at hru⟩
      · refine ⟨-u, by rw [norm_neg]; exact hu.le, ?_⟩
        rw [map_neg]
        rw [Real.norm_eq_abs, abs_of_neg h] at hru
        linarith
    set t := r / (L : ℝ) with ht
    have ht0 : 0 ≤ t := by positivity
    have hd := hq y (y - t • w)
    have hfo := add_fderiv_le_of_convexOn hconv hf x (y - t • w)
    have e1 : y - t • w - y = -(t • w) := by abel
    have e2 : y - t • w - x = (y - x) - t • w := by abel
    rw [e1, map_neg, map_smul, smul_eq_mul, norm_neg, norm_smul, Real.norm_of_nonneg ht0,
      mul_pow] at hd
    rw [e2, map_sub, map_smul, smul_eq_mul] at hfo
    have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    have hφw : φ' w = fderiv ℝ f y w - fderiv ℝ f x w := rfl
    have hkey : t * φ' w ≤ (f y - f x - fderiv ℝ f x (y - x)) + L / 2 * t ^ 2 := by
      rw [hφw]
      nlinarith [mul_le_mul_of_nonneg_left hw2 (by positivity : (0 : ℝ) ≤ L / 2 * t ^ 2)]
    have htr : t * r ≤ t * φ' w := mul_le_mul_of_nonneg_left hrw.le ht0
    have hrt : t * r = r ^ 2 / L := by rw [ht]; ring
    have ht2 : (L : ℝ) / 2 * t ^ 2 = r ^ 2 / (2 * L) := by rw [ht]; field_simp
    have : r ^ 2 / (2 * L) ≤ (f y - f x - fderiv ℝ f x (y - x)) := by
      have h1 : r ^ 2 / L = r ^ 2 / (2 * L) + r ^ 2 / (2 * L) := by field_simp; ring
      linarith
    rw [div_le_iff₀ (by positivity)] at this
    rw [hA]; linarith
  have hA0 : 0 ≤ A := by
    have := add_fderiv_le_of_convexOn hconv hf x y
    have h0 : 0 ≤ f y - f x - fderiv ℝ f x (y - x) := by linarith
    positivity
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ‖φ'‖ := by
    rcases eq_or_lt_of_le (norm_nonneg φ') with h | h
    · rw [← h] at hlt; nlinarith
    · exact h
  have hsq : Real.sqrt A < ‖φ'‖ := (Real.sqrt_lt' hpos).mpr hlt
  obtain ⟨r, hr1, hr2⟩ := exists_between hsq
  have hr0 : 0 ≤ r := le_trans (Real.sqrt_nonneg _) hr1.le
  have h1 := claim r hr0 hr2
  have h2 := Real.lt_sq_of_sqrt_lt hr1
  linarith

theorem smooth_iff_lipschitz : SmoothIffLipschitz.{u} := by
  intro E _ _ f L hconv hf
  constructor
  · intro hq
    rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with hL0 | hLpos
    · -- `L = 0`: `f` is affine, so its derivative is constant
      have haff : ∀ x z : E, f z = f x + fderiv ℝ f x (z - x) := by
        intro x z
        have h1 := hq x z
        rw [← hL0] at h1
        have h2 := add_fderiv_le_of_convexOn hconv hf x z
        linarith [h1, h2, show (0 : ℝ) / 2 * ‖z - x‖ ^ 2 = 0 by ring]
      have hconst : ∀ x y : E, fderiv ℝ f x = fderiv ℝ f y := by
        intro x y
        ext w
        have e1 := haff y (y + w)
        have e2 := haff x (y + w)
        have e3 := haff x y
        rw [add_sub_cancel_left] at e1
        have e4 : fderiv ℝ f x (y + w - x) = fderiv ℝ f x (y - x) + fderiv ℝ f x w := by
          rw [← map_add]; congr 1; abel
        linarith
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [hconst x y, dist_self]
      positivity
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 := cocoercive_of_bound hconv hf hq hLpos y x
      have h2 := cocoercive_of_bound hconv hf hq hLpos x y
      rw [norm_sub_rev] at h2
      set φ := fderiv ℝ f x - fderiv ℝ f y with hφ
      have happ : φ (x - y) = -(fderiv ℝ f x (y - x)) - fderiv ℝ f y (x - y) := by
        have e : φ (x - y) = fderiv ℝ f x (x - y) - fderiv ℝ f y (x - y) := rfl
        rw [e, ← map_neg, neg_sub]
      have hsum : ‖φ‖ ^ 2 ≤ L * φ (x - y) := by rw [happ]; nlinarith [h1, h2]
      have hop : φ (x - y) ≤ ‖φ‖ * ‖x - y‖ :=
        (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact φ.le_opNorm _)
      have hsq : ‖φ‖ ^ 2 ≤ L * (‖φ‖ * ‖x - y‖) :=
        hsum.trans (mul_le_mul_of_nonneg_left hop hLpos.le)
      rcases eq_or_lt_of_le (norm_nonneg φ) with h0 | hpos
      · rw [← h0]; positivity
      · nlinarith [hsq]
  · intro hlip x y
    exact IsSmooth.le_quadratic ⟨hf, hlip⟩ x y

theorem gap_by_primal_gap : GapByPrimalGap.{u} := by
  intro E _ _ C f L hsm hC hbdd xStar hxs x hx v hv
  set D := Metric.diam C with hD
  set K : ℝ := L * D ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hd2 : ‖v - x‖ ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (by rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd hv hx) 2
  have key : ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      γ * fderiv ℝ f x (x - v) ≤ f x - f xStar + γ ^ 2 * K / 2 := by
    intro γ hγ
    have hmin := hxs.2 _ (hC.add_smul_sub_mem hx hv hγ)
    have hp := hsm.progress x v γ
    have hb : γ ^ 2 * L / 2 * ‖v - x‖ ^ 2 ≤ γ ^ 2 * L / 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left hd2 (by positivity)
    have e : γ ^ 2 * K / 2 = γ ^ 2 * L / 2 * D ^ 2 := by rw [hK]; ring
    linarith
  have h1 := key 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_mul, one_pow] at h1
  refine ⟨fun _ => by linarith, fun hsmall => ?_⟩
  have hh0 : 0 ≤ f x - f xStar := sub_nonneg.mpr (hxs.2 x hx)
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have e : D * Real.sqrt (2 * L * (f x - f xStar)) =
      Real.sqrt (2 * (f x - f xStar) * K) := by
    rw [hK, show 2 * (f x - f xStar) * (L * D ^ 2) = D ^ 2 * (2 * L * (f x - f xStar)) by ring,
      Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD0]
  rw [e]
  rcases le_or_gt (fderiv ℝ f x (x - v)) 0 with hg | hg
  · exact hg.trans (Real.sqrt_nonneg _)
  · have hgK : fderiv ℝ f x (x - v) ≤ K := by linarith
    have hKpos : 0 < K := lt_of_lt_of_le hg hgK
    have hγ : fderiv ℝ f x (x - v) / K ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hg.le hK0, (div_le_one hKpos).mpr hgK⟩
    have h2 := key _ hγ
    set g := fderiv ℝ f x (x - v)
    have e1 : g / K * g = g ^ 2 / K := by ring
    have e2 : (g / K) ^ 2 * K / 2 = g ^ 2 / K / 2 := by field_simp
    rw [e1, e2] at h2
    have h3 : g ^ 2 / K ≤ 2 * (f x - f xStar) := by linarith
    rw [div_le_iff₀ hKpos] at h3
    exact (Real.le_sqrt' hg).mpr (by linarith)

theorem primal_gap_strong_convexity : PrimalGapStrongConvexity.{u} := by
  intro E _ _ C f μ hμ hsc xStar hxs x hx
  set a := fderiv ℝ f x (x - xStar) with ha
  have hsc' := hsc x hx xStar hxs.1
  have e1 : fderiv ℝ f x (xStar - x) = -a := by rw [ha, ← map_neg, neg_sub]
  rw [e1, norm_sub_rev] at hsc'
  rcases eq_or_lt_of_le (norm_nonneg (x - xStar)) with hd | hd
  · have hx' : x = xStar := by rw [← sub_eq_zero, ← norm_eq_zero]; exact hd.symm
    subst hx'
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, div_zero, le_refl, true_and]
    positivity
  · set d := ‖x - xStar‖ with hdd
    constructor
    · have hfrac : a - μ / 2 * d ^ 2 ≤ a ^ 2 / (2 * μ * d ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (a - μ * d ^ 2)]
      linarith
    · have hop : |a| ≤ ‖fderiv ℝ f x‖ * d := by
        have := (fderiv ℝ f x).le_opNorm (x - xStar)
        rwa [Real.norm_eq_abs] at this
      have hsq : a ^ 2 ≤ (‖fderiv ℝ f x‖ * d) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hop 2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsq]

end Proof

end Lemmata.CGBasics
