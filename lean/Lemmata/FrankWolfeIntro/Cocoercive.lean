module

public import Lemmata.FrankWolfeIntro.Proof

@[expose] public section

/-!
# Co-coercivity and Lemma 4.9

For a convex `L`-smooth `f`, `‖f'(y) - f'(x)‖² ≤ 2L (f y - f x - f'(x)(y - x))`, in any real normed
space: compare the descent lemma at `y` with first-order convexity at `x`, at the point
`y - (r/L) w`
for a vector `w` nearly attaining the norm of `f'(y) - f'(x)`.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

universe u

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cocoercive {f : E → ℝ} {L : NNReal} (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
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
    have hd := hsm.le_quadratic y (y - t • w)
    have hfo := add_fderiv_le_of_convexOn hconv hsm.1 x (y - t • w)
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
    have := add_fderiv_le_of_convexOn hconv hsm.1 x y
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

theorem smoothness_revisited : SmoothnessRevisited.{u} := by
  intro E _ _ f L hconv hsm hL x y
  have hL' : (0 : ℝ) < L := hL
  have hcc := cocoercive hconv hsm hL' x y
  rcases eq_or_lt_of_le (norm_nonneg (y - x)) with h | h
  · have hy : y = x := by rw [← sub_eq_zero, ← norm_eq_zero]; exact h.symm
    subst hy
    simp
  · have hop := (fderiv ℝ f y - fderiv ℝ f x).le_opNorm (y - x)
    have habs : |(fderiv ℝ f y - fderiv ℝ f x) (y - x)| ≤
        ‖fderiv ℝ f y - fderiv ℝ f x‖ * ‖y - x‖ := by rwa [Real.norm_eq_abs] at hop
    have hsq : ((fderiv ℝ f y - fderiv ℝ f x) (y - x)) ^ 2 ≤
        ‖fderiv ℝ f y - fderiv ℝ f x‖ ^ 2 * ‖y - x‖ ^ 2 := by
      rw [← mul_pow]; exact sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hcc (by positivity : (0 : ℝ) ≤ ‖y - x‖ ^ 2)]

end Proof

end Lemmata.FrankWolfeIntro
