module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# One signed shift strictly improves the Bell test score

The two reference phases in the three-party problem are 0 and π/(2m).
The same score uses the fundamental and the eleven odd harmonics from 3 to 23.
The proof simplifies the two score differences by the double- and triple-angle
identities. All numerical inequalities are over the reals with rational constants.
-/

@[expose] public section

namespace Lemmata.BellFollowup.Shift

open scoped BigOperators
noncomputable section

/-- The secondary frequencies appearing in the separating test. -/
def harmonics : Finset ℕ := {3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23}

/-- Ratio of the harmonic to the fundamental Fourier radius of the threshold sign wave. -/
def radius (x : ℝ) (h : ℕ) : ℝ := Real.sin x / Real.sin (h * x)

/-- Normalized cubic amplitude, with the translation phase included. -/
def term (x p : ℝ) (h : ℕ) : ℝ := radius x h ^ 3 * Real.cos (h * p)

/-- Coefficient normalizing the score at reference phase `p` to one. -/
def weight (x p : ℝ) : ℝ :=
  (1 + (9 / 10 : ℝ) * ∑ h ∈ harmonics, term x p h) / Real.cos p

/-- The Bell linear functional evaluated on a signed threshold profile of phase `q`.
The alternating sign of the odd harmonic occurs in both the coefficient and profile,
so their product is positive before the common coefficient `-9/10`. -/
def score (x p q : ℝ) : ℝ :=
  weight x p * Real.cos q - (9 / 10 : ℝ) * ∑ h ∈ harmonics, term x q h

private lemma freq_bounds {h : ℕ} (hh : h ∈ harmonics) :
    0 < (h : ℝ) ∧ (h : ℝ) ≤ 23 := by
  have h' : h ∈ Finset.Icc 1 23 := by
    have sel : harmonics ⊆ Finset.Icc 1 23 := by decide
    exact sel hh
  obtain ⟨hpos, hle⟩ := Finset.mem_Icc.mp h'
  constructor
  · exact_mod_cast (by omega : 0 < h)
  · exact_mod_cast hle

private lemma sin_bounds {z : ℝ} (hz : 0 ≤ z) (hmax : z ≤ 2 / 5) :
    (973 / 1000 : ℝ) * z ≤ Real.sin z ∧ Real.sin z ≤ z := by
  constructor
  · have hsq : z ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (show 0 ≤ 2 / 5 + z by linarith)]
    have hg := Real.sin_ge_sub_cube hz
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hsq)]
  · exact Real.sin_le hz

private lemma bound_radius {x : ℝ} (hx : 0 < x) (hmax : x ≤ 171 / 10000)
    {h : ℕ} (hh : h ∈ harmonics) :
    0 < Real.sin (h * x) ∧
    (999 / 1000 : ℝ) / h ≤ radius x h ∧ radius x h ≤ (1028 / 1000 : ℝ) / h := by
  obtain ⟨hp, hm⟩ := freq_bounds hh
  have hp' : 0 < (h : ℝ) * x := mul_pos hp hx
  have hz : (h : ℝ) * x ≤ 2 / 5 := by
    calc
      _ ≤ 23 * (171 / 10000 : ℝ) := mul_le_mul hm hmax hx.le (by norm_num)
      _ ≤ _ := by norm_num
  obtain ⟨hl, hu⟩ := sin_bounds hp'.le hz
  have hpos : 0 < Real.sin (h * x) := by linarith
  have hsmall : (999 / 1000 : ℝ) * x ≤ Real.sin x := by
    have hsq : x ^ 2 ≤ (171 / 10000 : ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (show 0 ≤ 171/10000+x by linarith)]
    nlinarith [Real.sin_ge_sub_cube hx.le, mul_nonneg hx.le (sub_nonneg.mpr hsq)]
  refine ⟨hpos, ?_, ?_⟩
  · unfold radius
    apply (div_le_div_iff₀ hp hpos).2
    nlinarith [mul_le_mul_of_nonneg_right hsmall hp.le]
  · unfold radius
    apply (div_le_div_iff₀ hpos hp).2
    nlinarith [mul_le_mul_of_nonneg_right (Real.sin_le hx.le) hp.le]

private lemma cos_lower {h : ℕ} {x : ℝ} (hx : 0 ≤ x) (hm : x ≤ 171/10000) :
    1 - ((h : ℝ) * (171 / 10000))^2 / 2 ≤ Real.cos (h * x) := by
  have h1 : 0 ≤ (h : ℝ) * x := by positivity
  have h2 : (h : ℝ) * x ≤ (h : ℝ) * (171/10000) := by gcongr
  have hs : ((h : ℝ) * x)^2 ≤ ((h : ℝ) * (171/10000))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ (h : ℝ)*(171/10000)+(h : ℝ)*x by positivity)]
  linarith [Real.one_sub_sq_div_two_le_cos (x := (h : ℝ) * x)]

private lemma lower_nonneg {h : ℕ} (hh : h ∈ harmonics) :
    0 ≤ 1 - ((h : ℝ) * (171/10000))^2 / 2 := by
  obtain ⟨hp, hm⟩ := freq_bounds hh
  have hs : (h : ℝ)^2 ≤ 23^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ 23 + (h : ℝ) by linarith)]
  nlinarith

private lemma upper_weight {x p : ℝ} (hx : 0 < x) (hm : x ≤ 171/10000)
    (hp : 0 ≤ p) (hpx : p ≤ x) : weight x p ≤ 1054/1000 := by
  have hmax : p ≤ 171/10000 := hpx.trans hm
  have hsq : p^2 ≤ (171/10000 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (show 0 ≤ 171/10000+p by linarith)]
  have hc := Real.one_sub_sq_div_two_le_cos (x := p)
  have hcp : 0 < Real.cos p := by linarith
  have hsum : (∑ h ∈ harmonics, term x p h) ≤
      ∑ h ∈ harmonics, ((1028/1000 : ℝ) / h)^3 := by
    apply Finset.sum_le_sum
    intro h hh
    obtain ⟨_, hlo, hup⟩ := bound_radius hx hm hh
    have rnon : 0 ≤ radius x h := le_trans (by positivity) hlo
    unfold term
    calc
      _ ≤ radius x h ^ 3 * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) (by positivity)
      _ ≤ _ := by rw [mul_one]; gcongr
  have hconst : (∑ h ∈ harmonics, ((1028/1000 : ℝ) / h)^3) < 56 / 1000 := by
    norm_num [harmonics, Finset.sum_insert]
  unfold weight
  apply (div_le_iff₀ hcp).2
  linarith

/-- The normalized fundamental coefficient remains positive and at most 1.054. -/
theorem weight_abs_le {x p : ℝ} (hx : 0 < x) (hm : x ≤ 171/10000)
    (hp : 0 ≤ p) (hpx : p ≤ x) : |weight x p| ≤ 1054/1000 := by
  have hs : 0 ≤ ∑ h ∈ harmonics, term x p h := by
    apply Finset.sum_nonneg
    intro h hh
    have hu := (bound_radius hx hm hh).2.1
    have hr : 0 ≤ radius x h := le_trans (by positivity) hu
    have hc : 0 ≤ Real.cos (h*p) := (lower_nonneg hh).trans (cos_lower hp (hpx.trans hm))
    unfold term
    positivity
  have hcp : 0 < Real.cos p := by
    have h := cos_lower (h := 1) hp (hpx.trans hm)
    norm_num at h
    linarith
  have hw : 0 ≤ weight x p := by unfold weight; positivity
  rw [abs_of_nonneg hw]
  exact upper_weight hx hm hp hpx

/-- Coefficient on physical harmonic `k`, including the threshold phase sign. -/
def testCoefficient (x p : ℝ) (k : ℕ) : ℝ :=
  if k = 1 then weight x p else if k ∈ harmonics then
    -(9/10 : ℝ) * Real.sin (Real.pi * k/2) else 0

/-- The modulus of every secondary coefficient is at most 9/10. -/
theorem coefficient_nonfund (x p : ℝ) {k : ℕ} (hk : k ≠ 1) :
    |testCoefficient x p k| ≤ 9/10 := by
  unfold testCoefficient
  rw [ite_eq_right hk]
  split
  · rw [abs_mul]
    have hs : |Real.sin (Real.pi*k/2)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    norm_num
    linarith
  · norm_num

/-- Uniform coefficient cap including the normalized fundamental. -/
theorem coefficient_bound {x p : ℝ} (hx : 0 < x) (hm : x ≤ 171/10000)
    (hp : 0 ≤ p) (hpx : p ≤ x) (k : ℕ) : |testCoefficient x p k| ≤ 1054/1000 := by
  by_cases hk : k = 1
  · simpa [testCoefficient, hk] using weight_abs_le hx hm hp hpx
  · exact (coefficient_nonfund x p hk).trans (by norm_num)

private lemma gain_mass {x : ℝ} (hx : 0 < x) (hm : x ≤ 171/10000) :
    (1054/1000 : ℝ) < (9/10 : ℝ) * ∑ h ∈ harmonics, radius x h * Real.cos (h*x) := by
  have hsum : (∑ h ∈ harmonics, ((999/1000 : ℝ)/h) *
      (1 - ((h : ℝ)*(171/10000))^2 / 2)) ≤
      ∑ h ∈ harmonics, radius x h * Real.cos (h*x) := by
    apply Finset.sum_le_sum
    intro h hh
    obtain ⟨_, hlo, _⟩ := bound_radius hx hm hh
    exact mul_le_mul hlo (cos_lower hx.le hm) (lower_nonneg hh)
      (le_trans (by positivity) hlo)
  have hconst : (1054/1000 : ℝ) < (9/10 : ℝ) *
      ∑ h ∈ harmonics, ((999/1000 : ℝ)/h) * (1 - ((h : ℝ)*(171/10000))^2 / 2) := by
    norm_num [harmonics, Finset.sum_insert]
  linarith

private lemma base_score {x p : ℝ} (hp : Real.cos p ≠ 0) : score x p p = 1 := by
  unfold score weight
  rw [div_mul_cancel₀ _ hp]
  ring

private lemma delta_identity (x p q c b : ℝ) (f : ℕ → ℝ)
    (hf : Real.cos p - Real.cos q = c * b)
    (hh : ∀ h ∈ harmonics, term x p h - term x q h = c * f h) :
    score x p q - score x p p =
      c * ((9/10 : ℝ) * (∑ h ∈ harmonics, f h) - weight x p * b) := by
  have hs : ((∑ h ∈ harmonics, term x p h) - ∑ h ∈ harmonics, term x q h)
        = c * ∑ h ∈ harmonics, f h := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hh
  unfold score
  linear_combination (9/10 : ℝ) * hs - weight x p * hf

private lemma double_gap (t : ℝ) : 1 - Real.cos (2*t) = 2*(Real.sin t)^2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq t]

private lemma triple_gap (t : ℝ) :
    Real.cos t - Real.cos (3*t) = 4*(Real.sin t)^2 * Real.cos t := by
  rw [show 3*t = 2*t+t by ring, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination -(2 * Real.cos t) * Real.sin_sq_add_cos_sq t

/-- The value of the explicit threshold test increases under one signed input shift
at either possible reference phase. This is a theorem about actual sine and cosine
values, including the coefficient normalizing the reference score. -/
theorem shifted_score (x : ℝ) (hx : 0 < x) (hm : x ≤ 171/10000) :
    (score x 0 0 = 1 ∧ 1 < score x 0 (2*x)) ∧
    (score x x x = 1 ∧ 1 < score x x (3*x)) := by
  have cs : 0 < Real.cos x := by
    have h := cos_lower (h := 1) hx.le hm
    norm_num at h
    linarith
  have ss : 0 < Real.sin x := by
    have h := (sin_bounds hx.le (show x ≤ 2/5 by linarith)).1
    linarith
  have oddBase := base_score (x := x) (p := 0) (by simp)
  have evenBase := base_score (x := x) (p := x) cs.ne'
  have gain := gain_mass hx hm
  have massLe : (∑ h ∈ harmonics, radius x h * Real.cos (h*x)) ≤
      ∑ h ∈ harmonics, radius x h := by
    apply Finset.sum_le_sum
    intro h hh
    have hr := (bound_radius hx hm hh).2.1
    exact mul_le_of_le_one_right (le_trans (by positivity) hr) (Real.cos_le_one _)
  have wo := upper_weight (p := 0) hx hm (by norm_num) hx.le
  have we := upper_weight (p := x) hx hm hx.le le_rfl
  have wc : weight x x * Real.cos x ≤ 1054/1000 := by
    calc
      _ ≤ (1054/1000 : ℝ) * 1 := mul_le_mul we (Real.cos_le_one x) cs.le (by norm_num)
      _ = _ := by ring
  have go := delta_identity x 0 (2*x) (2*Real.sin x^2) 1 (radius x)
    (by simpa using double_gap x) (by
      intro h hh
      have hn := (bound_radius hx hm hh).1.ne'
      unfold term
      rw [mul_zero, Real.cos_zero, show (h : ℝ) * (2*x) = 2*(h*x) by ring,
        ← mul_sub, double_gap]
      unfold radius
      field_simp [hn])
  have ge := delta_identity x x (3*x) (4*Real.sin x^2) (Real.cos x)
    (fun h => radius x h * Real.cos (h*x)) (triple_gap x) (by
      intro h hh
      have hn := (bound_radius hx hm hh).1.ne'
      unfold term
      rw [show (h : ℝ) * (3*x) = 3*(h*x) by ring, ← mul_sub, triple_gap]
      unfold radius
      field_simp [hn])
  rw [oddBase] at go
  rw [evenBase] at ge
  refine ⟨⟨oddBase, ?_⟩, ⟨evenBase, ?_⟩⟩
  · have hpos : 0 < (9/10 : ℝ) * (∑ h ∈ harmonics, radius x h) - weight x 0 * 1 := by
      linarith
    nlinarith [mul_pos (show 0 < 2*Real.sin x^2 by positivity) hpos]
  · have hpos : 0 < (9/10 : ℝ) * (∑ h ∈ harmonics, radius x h * Real.cos (h*x)) -
        weight x x * Real.cos x := by linarith
    nlinarith [mul_pos (show 0 < 4*Real.sin x^2 by positivity) hpos]

/-- At every integer number of settings at least 92, a one-setting shift beats
the normalized reference score for both possible parities. -/
theorem shifted_score_of_settings (m : ℕ) (hm : 92 ≤ m) :
    let x := Real.pi / (2*(m : ℝ))
    (score x 0 0 = 1 ∧ 1 < score x 0 (2*x)) ∧
    (score x x x = 1 ∧ 1 < score x x (3*x)) := by
  dsimp only
  have hm' : (92 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 2*(m : ℝ) := by linarith
  apply shifted_score _ (div_pos Real.pi_pos hp)
  apply (div_le_iff₀ hp).2
  linarith [Real.pi_lt_d4]

end
end Lemmata.BellFollowup.Shift
