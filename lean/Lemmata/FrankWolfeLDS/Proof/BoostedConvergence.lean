module

public import Lemmata.FrankWolfeLDS.Proof.Convergence
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.FrankWolfeLDS

open InnerProductSpace Set Filter
local notation "inner" => inner ℝ

section BoostedConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} (O : Oracle C)

/-- Definition of a strongly convex set -/
def IsStronglyConvex (C : Set E) (μ : ℝ) : Prop :=
  0 < μ ∧
  ∀ v ∈ C, ∀ η : E, (∀ y ∈ C, inner η (y - v) ≥ (0 : ℝ)) →
    ∀ x ∈ C, inner η (x - v) ≥ (μ / 2) * ‖η‖ * ‖x - v‖^2

/-- The LMO point exposes a supporting normal: every feasible displacement away
from it has nonnegative inner product with the oracle normal. -/
lemma lmo_normal_nonneg (g : E) {y : E} (hy : y ∈ C) :
    0 ≤ (inner g (y - LMO O g) : ℝ) := by
  rw [inner_sub_right]
  linarith [LMO_le O g hy]

/-- The dual gap at a feasible point is nonnegative. -/
lemma lmo_gap_nonneg (g : E) {x : E} (hx : x ∈ C) :
    0 ≤ (inner g (x - LMO O g) : ℝ) :=
  lmo_normal_nonneg (O := O) (g := g) hx

/-- The primal gap is bounded by the Frank-Wolfe dual gap. -/
lemma primalGap_le_lmoGap
    (f : E → ℝ) (f' : E → E) (hConv : IsFirstOrderConvex f f')
    {x x_star : E} (hx_star : x_star ∈ C) :
    f x - f x_star ≤ (inner (f' x) (x - LMO O (f' x)) : ℝ) := by
  have hfirst :
      f x - f x_star ≤ (inner (f' x) (x - x_star) : ℝ) := by
    have hconv := hConv x x_star
    rw [inner_sub_right] at hconv ⊢
    linarith
  have hmin :
      (inner (f' x) (x - x_star) : ℝ) ≤
        (inner (f' x) (x - LMO O (f' x)) : ℝ) := by
    rw [inner_sub_right, inner_sub_right]
    linarith [LMO_le O (f' x) hx_star]
  exact le_trans hfirst hmin

/-- Convexity plus Cauchy-Schwarz bounds the primal gap by gradient norm times
distance to the minimizer. -/
lemma primalGap_le_gradNorm_mul_dist
    (f : E → ℝ) (f' : E → E) (hConv : IsFirstOrderConvex f f')
    {x x_star : E} :
    f x - f x_star ≤ ‖f' x‖ * ‖x - x_star‖ := by
  have hfirst :
      f x - f x_star ≤ (inner (f' x) (x - x_star) : ℝ) := by
    have hconv := hConv x x_star
    rw [inner_sub_right] at hconv ⊢
    linarith
  exact le_trans hfirst (real_inner_le_norm _ _)

/-- Smoothness at a zero-gradient minimizer bounds the primal gap by a squared
distance scale. -/
lemma primalGap_le_half_L_mul_sqDist
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E}
    (hgrad : f' x_star = 0) :
    f x - f x_star ≤ (L / 2 : ℝ) * ‖x - x_star‖ ^ 2 := by
  have hsmooth := hSmooth x_star x
  have hsmooth' :
      f x ≤ f x_star + (L / 2 : ℝ) * ‖x - x_star‖ ^ 2 := by
    simpa [hgrad] using hsmooth
  linarith

/-- Strong convexity of the feasible set upgrades the LMO supporting-normal
condition into a quadratic lower bound on the dual gap. -/
lemma stronglyConvex_lmoGap_lower_bound
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (g : E) {x : E} (hx : x ∈ C) :
    (μ / 2) * ‖g‖ * ‖x - LMO O g‖ ^ 2 ≤
      (inner g (x - LMO O g) : ℝ) := by
  let s := LMO O g
  have hs : s ∈ C := LMO_mem O g
  have hnormal : ∀ y ∈ C, (inner g (y - s) : ℝ) ≥ (0 : ℝ) := by
    intro y hy
    simpa [s] using
      (lmo_normal_nonneg (O := O) (g := g) (y := y) hy)
  have hbound : (inner g (x - s) : ℝ) ≥ (μ / 2) * ‖g‖ * ‖x - s‖ ^ 2 :=
    hSC.2 s hs g hnormal x hx
  simpa [s] using hbound

/-- A zero-gradient point for the global short-step rule is a fixed point. -/
lemma globalShortStep_eq_self_of_zero_gradient
    (f' : E → E) (L : NNReal) {x : E} (hgrad : f' x = 0) :
    globalShortStep O f' L x = x := by
  simp [globalShortStep, frankWolfeStep, globalShortStepSize, hgrad]

/-- A zero-gradient minimizer has nonnegative primal gap everywhere. -/
lemma primalGap_nonneg_of_zero_gradient
    (f : E → ℝ) (f' : E → E) (hConv : IsFirstOrderConvex f f')
    {x x_star : E}
    (hgrad : f' x_star = 0) :
    0 ≤ f x - f x_star := by
  have hconv := hConv x_star x
  simpa [hgrad] using hconv


/-- Smoothness plus convex feasibility shows that a feasible minimizer satisfies
the usual first-order variational inequality on the feasible set. -/
lemma firstOrder_nonneg_of_isMinOn
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x y : E} (hx : x ∈ C) (hy : y ∈ C)
    (hmin : ∀ z ∈ C, f x ≤ f z) :
    0 ≤ (inner (f' x) (y - x) : ℝ) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  by_contra hneg
  let γ : ℝ := min 1 (-inner (f' x) (y - x) / ((L : ℝ) * ‖y - x‖ ^ 2))
  have hyx_ne : y - x ≠ 0 := by
    intro hyx
    have hEq : y = x := sub_eq_zero.mp hyx
    have : (inner (f' x) (y - x) : ℝ) = 0 := by simp [hEq]
    linarith
  have hdist_pos : 0 < ‖y - x‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hyx_ne)
  have hden_pos : 0 < (L : ℝ) * ‖y - x‖ ^ 2 := mul_pos hL_real hdist_pos
  have hquot_pos :
      0 < -inner (f' x) (y - x) / ((L : ℝ) * ‖y - x‖ ^ 2) := by
    exact div_pos (by linarith) hden_pos
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    exact lt_min (by norm_num) hquot_pos
  have hγ_mem : γ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt hγ_pos
    · dsimp [γ]
      exact min_le_left _ _
  let z : E := (1 - γ) • x + γ • y
  have hz : z ∈ C := by
    exact hC_convex hx hy (by linarith [hγ_mem.2]) hγ_mem.1 (by ring)
  have hsmooth0 := hSmooth x z
  have hsmooth :
      f z ≤
        f x + γ * (inner (f' x) (y - x) : ℝ) +
          (L / 2 : ℝ) * γ ^ 2 * ‖y - x‖ ^ 2 := by
    have hz_sub : z - x = γ • (y - x) := by
      dsimp [z]
      calc
        (1 - γ) • x + γ • y - x
            = (1 - γ) • x + (-1 : ℝ) • x + γ • y := by
                  simp [sub_eq_add_neg, add_left_comm, add_comm]
        _ = ((1 - γ) + (-1 : ℝ)) • x + γ • y := by
              rw [← add_smul]
        _ = (-γ) • x + γ • y := by ring_nf
        _ = γ • y + -(γ • x) := by simp [add_comm]
        _ = γ • (y - x) := by rw [smul_sub, sub_eq_add_neg]
    simpa [hz_sub, inner_smul_right, norm_smul, Real.norm_of_nonneg hγ_pos.le, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsmooth0
  have hγ_le :
      γ ≤ -inner (f' x) (y - x) / ((L : ℝ) * ‖y - x‖ ^ 2) := by
    dsimp [γ]
    exact min_le_right _ _
  have hmul :
      γ * ((L : ℝ) * ‖y - x‖ ^ 2) ≤ -inner (f' x) (y - x) := by
    exact (_root_.le_div_iff₀ hden_pos).1 hγ_le
  have hcurv :
      (L / 2 : ℝ) * γ ^ 2 * ‖y - x‖ ^ 2 ≤
        -(γ * (inner (f' x) (y - x) : ℝ)) / 2 := by
    nlinarith [hmul, hγ_pos.le]
  have hneg' : (inner (f' x) (y - x) : ℝ) < 0 := lt_of_not_ge hneg
  have hstrict_aux :
      γ * (inner (f' x) (y - x) : ℝ) +
          (L / 2 : ℝ) * γ ^ 2 * ‖y - x‖ ^ 2 < 0 := by
    have hlin_neg : γ * (inner (f' x) (y - x) : ℝ) < 0 :=
      mul_neg_of_pos_of_neg hγ_pos hneg'
    have hsum_le :
        γ * (inner (f' x) (y - x) : ℝ) +
            (L / 2 : ℝ) * γ ^ 2 * ‖y - x‖ ^ 2 ≤
          (γ * (inner (f' x) (y - x) : ℝ)) / 2 := by
      linarith [hcurv]
    have hhalf_neg : (γ * (inner (f' x) (y - x) : ℝ)) / 2 < 0 := by
      nlinarith [hlin_neg]
    exact lt_of_le_of_lt hsum_le hhalf_neg
  have hstrict : f z < f x := by
    linarith [hsmooth, hstrict_aux]
  exact (not_lt_of_ge (hmin z hz)) hstrict

/-- At a feasible minimizer, the Frank-Wolfe dual gap vanishes. -/
lemma lmoGap_eq_zero_of_isMinOn
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x : E} (hx : x ∈ C)
    (hmin : ∀ y ∈ C, f x ≤ f y) :
    (inner (f' x) (x - LMO O (f' x)) : ℝ) = 0 := by
  have hnonneg :
      0 ≤ (inner (f' x) (x - LMO O (f' x)) : ℝ) :=
    lmo_gap_nonneg (O := O) (C := C)
      (g := f' x) (x := x) hx
  have hnonpos :
      (inner (f' x) (x - LMO O (f' x)) : ℝ) ≤ 0 := by
    have hs :
        0 ≤ (inner (f' x) (LMO O (f' x) - x) : ℝ) := by
      exact
        firstOrder_nonneg_of_isMinOn
          (C := C) hC_convex f f' L hL hSmooth
          hx (LMO_mem O (f' x)) hmin
    have hEq :
        (inner (f' x) (LMO O (f' x) - x) : ℝ) =
          -(inner (f' x) (x - LMO O (f' x)) : ℝ) := by
      rw [inner_sub_right, inner_sub_right]
      ring
    rw [hEq] at hs
    linarith
  exact le_antisymm hnonpos hnonneg

/-- A feasible minimizer is a fixed point of the global short-step rule. -/
lemma globalShortStep_eq_self_of_isMinOn
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x : E} (hx : x ∈ C)
    (hmin : ∀ y ∈ C, f x ≤ f y) :
    globalShortStep O f' L x = x := by
  have hgap_zero :
      (inner (f' x) (x - LMO O (f' x)) : ℝ) = 0 := by
    exact
      lmoGap_eq_zero_of_isMinOn
        (O := O)
        (C := C) hC_convex f f' L hL hSmooth hx hmin
  simp [globalShortStep, frankWolfeStep, globalShortStepSize, hgap_zero]

/-- Any point with the same objective value as a zero-gradient minimizer is
itself a zero-gradient minimizer. -/
lemma gradient_eq_zero_of_eq_minimizer_value
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E} (hgrad : f' x_star = 0) (hval : f x = f x_star) :
    f' x = 0 := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  have hmin : ∀ y, f x ≤ f y := by
    intro y
    have hgap_nonneg :=
      primalGap_nonneg_of_zero_gradient
        (f := f) (f' := f') hConv (x := y) (x_star := x_star) hgrad
    linarith
  by_contra hgrad_ne
  let y := x - ((L : ℝ)⁻¹) • f' x
  have hymin : f x ≤ f y := hmin y
  have hsmooth := hSmooth x y
  have hdecrease :
      f y ≤ f x - (1 / (2 * (L : ℝ))) * ‖f' x‖ ^ 2 := by
    have hsmooth' :
        f y ≤
          f x + (inner (f' x) (-((L : ℝ)⁻¹) • f' x) : ℝ) +
            (L / 2 : ℝ) * ‖-((L : ℝ)⁻¹) • f' x‖ ^ 2 := by
      simpa [y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsmooth
    have hinner :
        (inner (f' x) (-((L : ℝ)⁻¹) • f' x) : ℝ) = -((L : ℝ)⁻¹) * ‖f' x‖ ^ 2 := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
    have hnorm :
        ‖-((L : ℝ)⁻¹) • f' x‖ ^ 2 = ((L : ℝ)⁻¹) ^ 2 * ‖f' x‖ ^ 2 := by
      calc
        ‖-((L : ℝ)⁻¹) • f' x‖ ^ 2 = (‖-((L : ℝ)⁻¹)‖ * ‖f' x‖) ^ 2 := by
          rw [norm_smul]
        _ = (((L : ℝ)⁻¹) * ‖f' x‖) ^ 2 := by
          simp [Real.norm_eq_abs, abs_of_nonneg]
        _ = ((L : ℝ)⁻¹) ^ 2 * ‖f' x‖ ^ 2 := by ring
    rw [hinner, hnorm] at hsmooth'
    have hL_ne : (L : ℝ) ≠ 0 := hL_real.ne'
    have hcoeff :
        -((L : ℝ)⁻¹) * ‖f' x‖ ^ 2 + (L / 2 : ℝ) * (((L : ℝ)⁻¹) ^ 2 * ‖f' x‖ ^ 2) =
          -(1 / (2 * (L : ℝ))) * ‖f' x‖ ^ 2 := by
      field_simp [hL_ne]
      ring
    linarith [hsmooth', hcoeff]
  have hnorm_pos : 0 < ‖f' x‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hgrad_ne)
  have hstrict : f y < f x := by
    have hcoef_pos : 0 < (1 / (2 * (L : ℝ))) * ‖f' x‖ ^ 2 := by positivity
    linarith
  exact (not_lt_of_ge hymin) hstrict

/-- Reciprocal increments dominate any realized decrease, normalized by the
current squared gap. -/
lemma reciprocalIncrement_ge_decrease_over_sq
    {F Fnext a : ℝ}
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (ha_nonneg : 0 ≤ a) (hdec : Fnext ≤ F - a) :
    a / F ^ 2 ≤ Fnext⁻¹ - F⁻¹ := by
  have hstep : a ≤ F - Fnext := by linarith
  have hnum_nonneg : 0 ≤ F - Fnext := by linarith
  have hden_cmp : F * Fnext ≤ F ^ 2 := by
    nlinarith
  calc
    a / F ^ 2 ≤ (F - Fnext) / F ^ 2 := by
      exact div_le_div_of_nonneg_right hstep (sq_nonneg F)
    _ ≤ (F - Fnext) / (F * Fnext) := by
      simpa [pow_two, mul_comm] using
        (div_le_div_of_nonneg_left hnum_nonneg (mul_pos hF_pos hFnext_pos) hden_cmp)
    _ = Fnext⁻¹ - F⁻¹ := by
      simpa [mul_comm] using (inv_sub_inv hFnext_pos.ne' hF_pos.ne').symm

lemma min_gap_eq_of_large_case
    {g d L : ℝ}
    (hg_pos : 0 < g) (hLd2_pos : 0 < L * d ^ 2) (hcase : L * d ^ 2 ≤ g) :
    min g (g ^ 2 / (L * d ^ 2)) = g := by
  apply min_eq_left
  rw [_root_.le_div_iff₀ hLd2_pos]
  nlinarith

lemma min_gap_eq_of_small_case
    {g d L : ℝ}
    (hg_pos : 0 < g) (hLd2_pos : 0 < L * d ^ 2) (hcase : g ≤ L * d ^ 2) :
    min g (g ^ 2 / (L * d ^ 2)) = g ^ 2 / (L * d ^ 2) := by
  apply min_eq_right
  rw [_root_.div_le_iff₀ hLd2_pos]
  nlinarith

/-- In the large-gap regime `g ≥ L d²`, universal decrease yields a reciprocal
increment lower bound of order `1 / δ²`. -/
lemma reciprocalIncrement_large_gap_lower_bound
    {F Fnext g d δ L : ℝ}
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hd_pos : 0 < d) (hL : 0 < L)
    (hgap : F ≤ g)
    (hsmooth : F ≤ (L / 2) * δ ^ 2)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : L * d ^ 2 ≤ g) :
    1 / (L * δ ^ 2) ≤ Fnext⁻¹ - F⁻¹ := by
  have hg_pos : 0 < g := lt_of_lt_of_le hF_pos hgap
  have hd2_pos : 0 < d ^ 2 := sq_pos_of_pos hd_pos
  have hLd2_pos : 0 < L * d ^ 2 := mul_pos hL hd2_pos
  have hmin_eq := min_gap_eq_of_large_case hg_pos hLd2_pos hcase
  have hdec' : Fnext ≤ F - g / 2 := by
    have hdec0 : Fnext ≤ F - (1 / 2) * g := by
      simpa [hmin_eq] using hdec
    calc
      Fnext ≤ F - (1 / 2) * g := hdec0
      _ = F - g / 2 := by ring
  have hinc :
      (g / 2) / F ^ 2 ≤ Fnext⁻¹ - F⁻¹ :=
    reciprocalIncrement_ge_decrease_over_sq
      hF_pos hFnext_pos (by positivity : 0 ≤ g / 2) hdec'
  have hmid : 1 / (2 * F) ≤ (g / 2) / F ^ 2 := by
    have hEq : 1 / (2 * F) = F / (2 * F ^ 2) := by
      field_simp [hF_pos.ne']
    have hEqR : (g / 2) / F ^ 2 = g / (2 * F ^ 2) := by
      field_simp [hF_pos.ne']
    rw [hEq, hEqR]
    exact div_le_div_of_nonneg_right hgap (by positivity)
  have hfront : 1 / (L * δ ^ 2) ≤ 1 / (2 * F) := by
    have hden_cmp : 2 * F ≤ L * δ ^ 2 := by
      nlinarith
    exact div_le_div_of_nonneg_left zero_le_one (show 0 < 2 * F by positivity) hden_cmp
  exact le_trans hfront (le_trans hmid hinc)

/-- If `δ ≤ 4 / μ`, the large-gap regime already implies the `1 / δ` reciprocal
increment lower bound needed for the asymptotic boost. -/
lemma reciprocalIncrement_large_gap_lower_bound_of_small_delta
    {F Fnext g d δ L μ : ℝ}
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hδ_pos : 0 < δ) (hd_pos : 0 < d) (hL : 0 < L) (hμ : 0 < μ)
    (hgap : F ≤ g)
    (hsmooth : F ≤ (L / 2) * δ ^ 2)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : L * d ^ 2 ≤ g)
    (hδsmall : δ ≤ 4 / μ) :
    (μ / (4 * L)) / δ ≤ Fnext⁻¹ - F⁻¹ := by
  have hbase :=
    reciprocalIncrement_large_gap_lower_bound
      hF_pos hFnext_pos hd_pos hL hgap hsmooth hdec hcase
  have hfront : (μ / (4 * L)) / δ ≤ 1 / (L * δ ^ 2) := by
    have hmul : μ * δ ≤ 4 := by
      have htmp : δ * μ ≤ 4 := (_root_.le_div_iff₀ hμ).1 hδsmall
      simpa [mul_comm] using htmp
    have hδbound : μ / 4 ≤ 1 / δ := by
      exact (_root_.le_div_iff₀ hδ_pos).2 (by nlinarith [hmul])
    have hfactor_nonneg : 0 ≤ 1 / (L * δ) := by positivity
    have hmul' :
        (μ / 4) * (1 / (L * δ)) ≤ (1 / δ) * (1 / (L * δ)) := by
      exact mul_le_mul_of_nonneg_right hδbound hfactor_nonneg
    have hEqL : (μ / (4 * L)) / δ = (μ / 4) * (1 / (L * δ)) := by
      field_simp [hμ.ne', hL.ne', hδ_pos.ne']
    have hEqR : 1 / (L * δ ^ 2) = (1 / δ) * (1 / (L * δ)) := by
      field_simp [hL.ne', hδ_pos.ne']
    rw [hEqL, hEqR]
    exact hmul'
  exact le_trans hfront hbase

/-- In the small-gap regime `g ≤ L d²`, universal decrease together with the
strong-convex-set geometry yields a reciprocal increment lower bound of order
`1 / δ`. -/
lemma reciprocalIncrement_small_gap_lower_bound
    {F Fnext g d δ L μ : ℝ}
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hδ_pos : 0 < δ) (hd_pos : 0 < d) (hL : 0 < L) (hμ : 0 < μ)
    (hgap : F ≤ g)
    (hgeom : (μ / 2) * (F / δ) * d ^ 2 ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : g ≤ L * d ^ 2) :
    (μ / (4 * L)) / δ ≤ Fnext⁻¹ - F⁻¹ := by
  have hg_pos : 0 < g := lt_of_lt_of_le hF_pos hgap
  have hd2_pos : 0 < d ^ 2 := sq_pos_of_pos hd_pos
  have hLd2_pos : 0 < L * d ^ 2 := mul_pos hL hd2_pos
  have hmin_eq := min_gap_eq_of_small_case hg_pos hLd2_pos hcase
  have hdec' : Fnext ≤ F - g ^ 2 / (2 * L * d ^ 2) := by
    have hdec0 : Fnext ≤ F - (1 / 2) * (g ^ 2 / (L * d ^ 2)) := by
      simpa [hmin_eq] using hdec
    have hEq :
        (1 / 2 : ℝ) * (g ^ 2 / (L * d ^ 2)) = g ^ 2 / (2 * L * d ^ 2) := by
      field_simp [hL.ne', hd_pos.ne']
    calc
      Fnext ≤ F - (1 / 2) * (g ^ 2 / (L * d ^ 2)) := hdec0
      _ = F - g ^ 2 / (2 * L * d ^ 2) := by rw [hEq]
  have hinc :
      (g ^ 2 / (2 * L * d ^ 2)) / F ^ 2 ≤ Fnext⁻¹ - F⁻¹ :=
    reciprocalIncrement_ge_decrease_over_sq
      hF_pos hFnext_pos (by positivity : 0 ≤ g ^ 2 / (2 * L * d ^ 2)) hdec'
  have hgeomF : ((μ / 2) * (F / δ) * d ^ 2) * F ≤ g * g := by
    exact mul_le_mul hgeom hgap (le_of_lt hF_pos) (le_of_lt hg_pos)
  have hgeomF' : μ * d ^ 2 * F ^ 2 ≤ 2 * g ^ 2 * δ := by
    have hmult :
        (((μ / 2) * (F / δ) * d ^ 2) * F) * (2 * δ) ≤ (g * g) * (2 * δ) := by
      exact mul_le_mul_of_nonneg_right hgeomF (by positivity)
    field_simp [hδ_pos.ne'] at hmult
    nlinarith [hmult]
  have hfront : (μ / (4 * L)) / δ ≤ (g ^ 2 / (2 * L * d ^ 2)) / F ^ 2 := by
    have hgeomF'' : μ * d ^ 2 * F ^ 2 / (2 * δ) ≤ g ^ 2 := by
      have hgeomF''' : μ * d ^ 2 * F ^ 2 ≤ g ^ 2 * (2 * δ) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hgeomF'
      exact (_root_.div_le_iff₀ (show 0 < 2 * δ by positivity)).2 hgeomF'''
    have hfront0 :
        (μ * d ^ 2 * F ^ 2 / (2 * δ)) / (2 * L * d ^ 2 * F ^ 2) ≤
          g ^ 2 / (2 * L * d ^ 2 * F ^ 2) := by
      exact div_le_div_of_nonneg_right hgeomF'' (by positivity)
    have hEqL :
        (μ * d ^ 2 * F ^ 2 / (2 * δ)) / (2 * L * d ^ 2 * F ^ 2) = (μ / (4 * L)) / δ := by
      field_simp [hμ.ne', hL.ne', hd_pos.ne', hF_pos.ne', hδ_pos.ne']
      ring
    have hEqR :
        g ^ 2 / (2 * L * d ^ 2 * F ^ 2) = (g ^ 2 / (2 * L * d ^ 2)) / F ^ 2 := by
      field_simp [hL.ne', hd_pos.ne', hF_pos.ne']
    rw [← hEqL, ← hEqR]
    exact hfront0
  exact le_trans hfront hinc

/-- Abstract reciprocal-growth hypothesis for a positive gap sequence. -/
def ReciprocalIncrementDiverges (F : ℕ → ℝ) : Prop :=
  Tendsto (fun t => (F (t + 1))⁻¹ - (F t)⁻¹) atTop atTop

/-- The paper's universal decrease estimate together with the strong-convex-set
geometry forces the reciprocal gap increments to diverge. -/
theorem reciprocalIncrementDiverges_of_decrease_and_geometry
    {F g δ d : ℕ → ℝ} {L μ : ℝ}
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_pos : ∀ t, 0 < d t)
    (hL : 0 < L) (hμ : 0 < μ)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    (hgap : ∀ t, F t ≤ g t)
    (hsmooth : ∀ t, F t ≤ (L / 2) * (δ t) ^ 2)
    (hgeom : ∀ t, (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    ReciprocalIncrementDiverges F := by
  refine tendsto_atTop.2 ?_
  intro b
  by_cases hb : b ≤ 0
  · refine Filter.Eventually.of_forall ?_
    intro t
    have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) (hgap t)
    have hmin_nonneg : 0 ≤ min (g t) (g t ^ 2 / (L * (d t) ^ 2)) := by
      apply le_min
      · exact le_of_lt hg_pos
      · positivity
    have hFnext_le : F (t + 1) ≤ F t := by
      linarith [hdec t]
    have hinc_nonneg :
        0 ≤ (F (t + 1))⁻¹ - (F t)⁻¹ := by
      simpa using
        (reciprocalIncrement_ge_decrease_over_sq
          (F := F t) (Fnext := F (t + 1)) (a := 0)
          (hF_pos t) (hF_pos (t + 1)) (by positivity) (by simpa using hFnext_le))
    exact le_trans hb hinc_nonneg
  · have hb_pos : 0 < b := lt_of_not_ge hb
    have htarget_pos : 0 < min (4 / μ) ((μ / (4 * L)) / b) := by
      apply lt_min
      · exact div_pos (by positivity) hμ
      · exact div_pos (div_pos hμ (by positivity)) hb_pos
    have hnear : ∀ᶠ t in atTop, δ t < min (4 / μ) ((μ / (4 * L)) / b) := by
      exact hδ_zero.eventually (Iio_mem_nhds htarget_pos)
    filter_upwards [hnear] with t ht
    have hδsmall : δ t ≤ 4 / μ := le_of_lt (lt_of_lt_of_le ht (min_le_left _ _))
    have hfront : b ≤ (μ / (4 * L)) / δ t := by
      have hmul : b * δ t < μ / (4 * L) := by
        have htmp : δ t * b < μ / (4 * L) := by
          exact (_root_.lt_div_iff₀ hb_pos).1 (lt_of_lt_of_le ht (min_le_right _ _))
        simpa [mul_comm] using htmp
      exact le_of_lt ((_root_.lt_div_iff₀ (hδ_pos t)).2 hmul)
    by_cases hcase : L * (d t) ^ 2 ≤ g t
    · exact le_trans hfront
        (reciprocalIncrement_large_gap_lower_bound_of_small_delta
          (hF_pos t) (hF_pos (t + 1)) (hδ_pos t) (hd_pos t) hL hμ
          (hgap t) (hsmooth t) (hdec t) hcase hδsmall)
    · have hcase' : g t ≤ L * (d t) ^ 2 := le_of_not_ge hcase
      exact le_trans hfront
        (reciprocalIncrement_small_gap_lower_bound
          (hF_pos t) (hF_pos (t + 1)) (hδ_pos t) (hd_pos t) hL hμ
          (hgap t) (hgeom t) (hdec t) hcase')

/-- The primal-gap sequence along the standard Frank-Wolfe iterates. -/
noncomputable def primalGapSequence
    (f : E → ℝ) (f' : E → E) (x_star x0 : E) : ℕ → ℝ :=
  fun t => f (frankWolfeSequence O f' x0 t) - f x_star

/-- A uniform lower bound on successive increments gives an affine lower bound. -/
lemma affine_lower_bound_of_increment_lower_bound
    {u : ℕ → ℝ} {M : ℝ} {N : ℕ}
    (hstep : ∀ n ≥ N, M ≤ u (n + 1) - u n) :
    ∀ k : ℕ, u (N + k) ≥ u N + M * k := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep' : M ≤ u (N + k + 1) - u (N + k) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hstep (N + k) (Nat.le_add_right N k)
      calc
        u (N + (k + 1)) = u (N + k) + (u (N + k + 1) - u (N + k)) := by ring_nf
        _ ≥ (u N + M * k) + M := by linarith
        _ = u N + M * (k + 1 : ℕ) := by
            rw [show (M * (k + 1 : ℕ) : ℝ) = M * ((k : ℝ) + 1) by push_cast; ring]
            linarith

/-- Divergent reciprocal increments force the reciprocal gap to dominate `t`. -/
lemma tendsto_reciprocal_over_nat_of_increment_divergence
    {F : ℕ → ℝ} (hF_pos : ∀ t, 0 < F t)
    (hdiv : ReciprocalIncrementDiverges F) :
    Tendsto (fun t => (F t)⁻¹ / (t + 2 : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  by_cases hb : b ≤ 0
  · refine Filter.Eventually.of_forall ?_
    intro t
    have hnonneg :
        0 ≤ (F t)⁻¹ / (t + 2 : ℝ) := by
      exact div_nonneg (inv_nonneg.mpr (le_of_lt (hF_pos t))) (by positivity)
    exact le_trans hb hnonneg
  · have hstep_eventually :
        ∀ᶠ n in atTop, 2 * b ≤ (F (n + 1))⁻¹ - (F n)⁻¹ :=
      (tendsto_atTop.1 hdiv) (2 * b)
    rcases Filter.Eventually.exists_forall_of_atTop hstep_eventually with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ?_
    refine ⟨2 * N + 2, ?_⟩
    intro n hn
    have hNle : N ≤ n := by omega
    have haffine :=
      affine_lower_bound_of_increment_lower_bound
        (u := fun m => (F m)⁻¹) (M := 2 * b) (N := N) hN (n - N)
    have haffine' :
        (F n)⁻¹ ≥ (F N)⁻¹ + (2 * b) * (n - N : ℕ) := by
      simpa [Nat.add_sub_of_le hNle] using haffine
    have hden_bound_nat : n + 2 ≤ 2 * (n - N) := by
      omega
    have hden_bound : (n + 2 : ℝ) ≤ 2 * (n - N : ℕ) := by
      exact_mod_cast hden_bound_nat
    have hbase_nonneg : 0 ≤ (F N)⁻¹ := inv_nonneg.mpr (le_of_lt (hF_pos N))
    have hmul :
        b * (n + 2 : ℝ) ≤ (2 * b) * (n - N : ℕ) := by
      nlinarith
    have hnum :
        b * (n + 2 : ℝ) ≤ (F n)⁻¹ := by
      linarith
    exact (_root_.le_div_iff₀ (show (0 : ℝ) < n + 2 by positivity)).2 hnum

/-- [FW-BOOST-ABS] Divergent reciprocal increments force the gap itself
to be `o(1/t)`. -/
theorem tendsto_mul_gap_of_increment_divergence
    {F : ℕ → ℝ} (hF_pos : ∀ t, 0 < F t)
    (hdiv : ReciprocalIncrementDiverges F) :
    Tendsto (fun t : ℕ => (t + 2 : ℝ) * F t) atTop (nhds 0) := by
  let G : ℕ → ℝ := fun t => (F t)⁻¹ / (t + 2 : ℝ)
  have hG : Tendsto G atTop atTop :=
    tendsto_reciprocal_over_nat_of_increment_divergence
      (hF_pos := hF_pos) hdiv
  have hInv : Tendsto (fun t => (G t)⁻¹) atTop (nhds 0) :=
    hG.inv_tendsto_atTop
  have hEq : (fun t : ℕ => (G t)⁻¹) = fun t : ℕ => (t + 2 : ℝ) * F t := by
    funext t
    have hFt : F t ≠ 0 := (hF_pos t).ne'
    have ht : (t + 2 : ℝ) ≠ 0 := by positivity
    dsimp [G]
    field_simp [hFt, ht]
  rw [hEq] at hInv
  exact hInv

/-- [FW-BOOST-SCALES] Complementary reciprocal-increment lower bounds in terms
of a vanishing distance scale `δ_t` and a chord scale `d_t` force `o(1/t)`. -/
theorem tendsto_mul_gap_of_scale_lower_bounds
    {F δ d : ℕ → ℝ}
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_pos : ∀ t, 0 < d t)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hsmall : ∀ t, A / (d t) ^ 2 ≤ (F (t + 1))⁻¹ - (F t)⁻¹)
    (hlarge : ∀ t, B * (d t) ^ 2 / (δ t) ^ 2 ≤ (F (t + 1))⁻¹ - (F t)⁻¹) :
    Tendsto (fun t : ℕ => (t + 2 : ℝ) * F t) atTop (nhds 0) := by
  let inc : ℕ → ℝ := fun t => (F (t + 1))⁻¹ - (F t)⁻¹
  have hminpos : 0 < min A B := lt_min hA hB
  have hinc_lb : ∀ t, min A B / δ t ≤ inc t := by
    intro t
    by_cases hcase : (d t) ^ 2 ≤ δ t
    · have hA_le : A ≤ inc t * δ t := by
        have hs := hsmall t
        have hd2pos : 0 < (d t) ^ 2 := by
          exact sq_pos_of_pos (hd_pos t)
        have hinc_nonneg : 0 ≤ inc t := by
          have hAdiv_pos : 0 < A / (d t) ^ 2 := by
            exact div_pos hA hd2pos
          exact le_trans (le_of_lt hAdiv_pos) hs
        have hAd2 : A ≤ inc t * (d t) ^ 2 := (_root_.div_le_iff₀ hd2pos).1 hs
        have hAdelta : inc t * (d t) ^ 2 ≤ inc t * δ t :=
          mul_le_mul_of_nonneg_left hcase hinc_nonneg
        exact le_trans hAd2 hAdelta
      have hmin_le : min A B ≤ inc t * δ t := by
        have hleft : min A B ≤ A := min_le_left _ _
        linarith
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 hmin_le
    · have hcase' : δ t < (d t) ^ 2 := lt_of_not_ge hcase
      have hB_le : B ≤ inc t * δ t := by
        have hl := hlarge t
        have hδ2pos : 0 < (δ t) ^ 2 := by
          exact sq_pos_of_pos (hδ_pos t)
        have hBd2 : B * (d t) ^ 2 ≤ inc t * (δ t) ^ 2 := (_root_.div_le_iff₀ hδ2pos).1 hl
        have hBdelta : B * δ t ≤ B * (d t) ^ 2 :=
          mul_le_mul_of_nonneg_left (le_of_lt hcase') hB.le
        have hBdelta2 : B * δ t ≤ (inc t * δ t) * δ t := by
          calc
            B * δ t ≤ B * (d t) ^ 2 := hBdelta
            _ ≤ inc t * (δ t) ^ 2 := hBd2
            _ = (inc t * δ t) * δ t := by ring
        have hδpos : 0 < δ t := hδ_pos t
        nlinarith
      have hmin_le : min A B ≤ inc t * δ t := by
        have hright : min A B ≤ B := min_le_right _ _
        linarith
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 hmin_le
  have hdiv : ReciprocalIncrementDiverges F := by
    refine tendsto_atTop.2 ?_
    intro b
    by_cases hb : b ≤ 0
    · refine Filter.Eventually.of_forall ?_
      intro t
      have hinc_nonneg : 0 ≤ inc t := by
        have hbound := hinc_lb t
        have hnonneg : 0 ≤ min A B / δ t := by
          exact div_nonneg (le_of_lt hminpos) (le_of_lt (hδ_pos t))
        exact le_trans hnonneg hbound
      exact le_trans hb hinc_nonneg
    · have hb_pos : 0 < b := lt_of_not_ge hb
      have hnear : ∀ᶠ t in atTop, δ t < min A B / b := by
        exact hδ_zero.eventually (Iio_mem_nhds (div_pos hminpos hb_pos))
      filter_upwards [hnear] with t ht
      have hbound := hinc_lb t
      have hfront : b ≤ min A B / δ t := by
        have hmul : b * δ t < min A B := by
          have hmul' : δ t * b < min A B := (_root_.lt_div_iff₀ hb_pos).1 ht
          simpa [mul_comm] using hmul'
        exact le_of_lt ((_root_.lt_div_iff₀ (hδ_pos t)).2 hmul)
      exact le_trans hfront hbound
  exact tendsto_mul_gap_of_increment_divergence (hF_pos := hF_pos) hdiv

/-- [FW-BOOST-CORE] Universal decrease together with the C+SC geometric bounds
forces a positive gap sequence to be `o(1/t)`. -/
theorem tendsto_mul_gap_of_decrease_and_geometry
    {F g δ d : ℕ → ℝ} {L μ : ℝ}
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_pos : ∀ t, 0 < d t)
    (hL : 0 < L) (hμ : 0 < μ)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    (hgap : ∀ t, F t ≤ g t)
    (hsmooth : ∀ t, F t ≤ (L / 2) * (δ t) ^ 2)
    (hgeom : ∀ t, (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    Tendsto (fun t : ℕ => (t + 2 : ℝ) * F t) atTop (nhds 0) := by
  have hdiv :
      ReciprocalIncrementDiverges F :=
    reciprocalIncrementDiverges_of_decrease_and_geometry
      hF_pos hδ_pos hd_pos hL hμ hδ_zero hgap hsmooth hgeom hdec
  exact tendsto_mul_gap_of_increment_divergence (hF_pos := hF_pos) hdiv

/-- [FW-DELTA-UNIQ] If the primal gap along a feasible sequence tends to zero
and `x_star` is the unique minimizer on the compact feasible set, then the
iterate distance to `x_star` also tends to zero. -/
theorem tendsto_norm_sub_of_gap_tendsto_zero_of_unique_minimizer
    (hC_compact' : IsCompact C)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (hmin_unique : ∀ x ∈ C, f x = f x_star → x = x_star)
    (xSeq : ℕ → E) (hxSeq : ∀ t, xSeq t ∈ C)
    (hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0)) :
    Tendsto (fun t => ‖xSeq t - x_star‖) atTop (nhds 0) := by
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hx_tendsto : Tendsto xSeq atTop (nhds x_star) := by
    refine IsCompact.tendsto_nhds_of_unique_mapClusterPt hC_compact'
      (Filter.Eventually.of_forall hxSeq) ?_
    intro x hx hxcluster
    have hxcluster_neBot : NeBot ((nhds x) ⊓ Filter.map xSeq atTop) := by
      simpa [MapClusterPt, ClusterPt] using hxcluster
    obtain ⟨φ, hφmono, hφtendsto⟩ :=
      subseq_tendsto_of_neBot (f := nhds x) (u := xSeq) hxcluster_neBot
    have hgap_sub :
        Tendsto (fun n => f (xSeq (φ n)) - f x_star) atTop (nhds 0) :=
      hgap_zero.comp hφmono.tendsto_atTop
    have hfx_sub :
        Tendsto (fun n => f (xSeq (φ n))) atTop (nhds (f x)) := by
      simpa [Function.comp_def] using (hcont.continuousAt.tendsto.comp hφtendsto)
    have hgap_sub' :
        Tendsto (fun n => f (xSeq (φ n)) - f x_star) atTop (nhds (f x - f x_star)) := by
      simpa using hfx_sub.sub_const (f x_star)
    have hfx : f x - f x_star = 0 := tendsto_nhds_unique hgap_sub' hgap_sub
    exact hmin_unique x hx (sub_eq_zero.mp hfx)
  have hsub' :
      Tendsto (fun t => xSeq t - x_star) atTop (nhds (x_star - x_star)) :=
    hx_tendsto.sub_const x_star
  have hsub : Tendsto (fun t => xSeq t - x_star) atTop (nhds 0) := by
    simpa using hsub'
  exact tendsto_zero_iff_norm_tendsto_zero.mp hsub

/-- [FW-DELTA-SET] If the primal gap tends to zero, then the iterates approach
the compact set of minimizers with value `f x_star`. -/
theorem tendsto_infDist_minimizerSet_of_gap_tendsto_zero
    (hC_compact' : IsCompact C)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    (xSeq : ℕ → E) (hxSeq : ∀ t, xSeq t ∈ C)
    (hgap_zero : Tendsto (fun t => f (xSeq t) - f x_star) atTop (nhds 0)) :
    let M : Set E := C ∩ {y : E | f y = f x_star}
    Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  by_contra hdist
  rw [not_tendsto_iff_exists_frequently_notMem] at hdist
  rcases hdist with ⟨s, hs_mem, hs_freq⟩
  obtain ⟨ns, hns_tendsto, hns_notin⟩ := exists_seq_forall_of_frequently hs_freq
  have hx_ns : ∀ n, xSeq (ns n) ∈ C := by
    intro n
    exact hxSeq (ns n)
  obtain ⟨x, hxC, ψ, hψmono, hψtendsto⟩ :=
    IsCompact.tendsto_subseq (s := C) (x := fun n => xSeq (ns n)) hC_compact' hx_ns
  have hgap_sub :
      Tendsto (fun n => f (xSeq (ns (ψ n))) - f x_star) atTop (nhds 0) := by
    exact hgap_zero.comp (hns_tendsto.comp hψmono.tendsto_atTop)
  have hfx_sub :
      Tendsto (fun n => f (xSeq (ns (ψ n)))) atTop (nhds (f x)) := by
    simpa [Function.comp_def] using (hcont.continuousAt.tendsto.comp hψtendsto)
  have hgap_sub' :
      Tendsto (fun n => f (xSeq (ns (ψ n))) - f x_star) atTop (nhds (f x - f x_star)) := by
    simpa using hfx_sub.sub_const (f x_star)
  have hfx : f x = f x_star := sub_eq_zero.mp (tendsto_nhds_unique hgap_sub' hgap_sub)
  have hxM : x ∈ M := by
    simp [M, hxC, hfx]
  have hdist_sub :
      Tendsto (fun n => Metric.infDist (xSeq (ns (ψ n))) M) atTop (nhds (Metric.infDist x M)) := by
    simpa [Function.comp_def] using
      ((Metric.continuous_infDist_pt M).continuousAt.tendsto.comp hψtendsto)
  have hdist_sub_zero :
      Tendsto (fun n => Metric.infDist (xSeq (ns (ψ n))) M) atTop (nhds 0) := by
    simpa [Metric.infDist_zero_of_mem hxM] using hdist_sub
  have hmem_eventually :
      ∀ᶠ n in atTop, Metric.infDist (xSeq (ns (ψ n))) M ∈ s :=
    hdist_sub_zero.eventually hs_mem
  rcases Filter.Eventually.exists_forall_of_atTop hmem_eventually with ⟨N, hN⟩
  exact hns_notin (ψ N) (hN N le_rfl)

/-- [FW-BOOST-SS] Global short-step Frank-Wolfe satisfies the abstract boosted
theorem once the iterate distance to the minimizer is known to vanish. -/
theorem globalShortStep_boosted_convergence_of_dist_tendsto_zero
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    {x0 : E} (hx0 : x0 ∈ C)
    (hgap_pos :
      ∀ t,
        0 < f (globalShortStepSequence O f' L x0 t) - f x_star)
    (hδ_zero :
      Tendsto
        (fun t => ‖globalShortStepSequence O f' L x0 t - x_star‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (globalShortStepSequence O f' L x0 t) - f x_star))
      atTop (nhds 0) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let δ : ℕ → ℝ := fun t => ‖xSeq t - x_star‖
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hF_pos : ∀ t, 0 < F t := by
    intro t
    simpa [F, xSeq] using hgap_pos t
  have hδ_pos : ∀ t, 0 < δ t := by
    intro t
    by_contra hδt
    have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
    have hxeq : xSeq t = x_star := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
    have : F t = 0 := by simp [F, hxeq]
    exact (hF_pos t).ne' this
  have hd_pos : ∀ t, 0 < d t := by
    intro t
    have hgap_le : F t ≤ g t := by
      simpa [F, g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
    by_contra hdt
    have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    have : g t = 0 := by simp [g, hsx]
    exact hg_pos.ne' this
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    simpa [F, g, xSeq, s] using
      primalGap_le_lmoGap
        (O := O)
        (C := C) (f := f) (f' := f') hConv
        (x := xSeq t) (x_star := x_star) hx_star
  have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
    intro t
    simpa [F, δ, xSeq] using
      primalGap_le_half_L_mul_sqDist
        (f := f) (f' := f') (L := L) hSmooth
        (x := xSeq t) (x_star := x_star) hgrad
  have hgeom : ∀ t, (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤ g t := by
    intro t
    have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 <|
        (by simpa [F, δ, xSeq] using
          (primalGap_le_gradNorm_mul_dist
            (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := x_star)))
    let coeff : ℝ := (μ / 2) * (d t) ^ 2
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      have hμ_pos := hSC.1
      positivity
    have hscaled : coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
    have hsc :
        (μ / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (stronglyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hSC := hSC) (g := f' (xSeq t)) (x := xSeq t) (hxSeq t))
    have hscaled' :
        (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤
          (μ / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hsc
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hx_t : xSeq t ∈ C := hxSeq t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, globalShortStepSequence] using
        (globalShortStep_decrease
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) hx_t)
    linarith [hstep]
  have hcore :=
    tendsto_mul_gap_of_decrease_and_geometry
      (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
      (hL := hL_real) (hμ := hSC.1) (hδ_zero := by simpa [δ, xSeq] using hδ_zero)
      (hgap := hgap) (hsmooth := hsmooth) (hgeom := hgeom) (hdec := hdec)
  simpa [F, xSeq] using hcore

/-- [FW-BOOST-SS-SEQ] The abstract boosted short-step proof also applies when
the comparison minimizer may vary with `t`, provided every comparison point has
the same optimal value and zero gradient. -/
theorem globalShortStep_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hgradSeq : ∀ t, f' (xStarSeq t) = 0)
    {x0 : E} (hx0 : x0 ∈ C)
    (hgap_pos :
      ∀ t,
        0 < f (globalShortStepSequence O f' L x0 t) - f x_star)
    (hδ_zero :
      Tendsto
        (fun t => ‖globalShortStepSequence O f' L x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (globalShortStepSequence O f' L x0 t) - f x_star))
      atTop (nhds 0) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hF_pos : ∀ t, 0 < F t := by
    intro t
    simpa [F, xSeq] using hgap_pos t
  have hδ_pos : ∀ t, 0 < δ t := by
    intro t
    show 0 < ‖xSeq t - xStarSeq t‖
    exact norm_sub_pos_of_primalGap_pos_of_valSeq hvalSeq hF_pos t
  have hd_pos : ∀ t, 0 < d t := by
    intro t
    have hgap_le : F t ≤ g t := by
      have hgap_le' :
          f (xSeq t) - f (xStarSeq t) ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
      simpa [F, hvalSeq t] using hgap_le'
    have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
    by_contra hdt
    have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    have : g t = 0 := by simp [g, hsx]
    exact hg_pos.ne' this
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f (xStarSeq t) ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
    simpa [F, hvalSeq t] using hgap_le'
  have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
    intro t
    have hsmooth_t :
        f (xSeq t) - f (xStarSeq t) ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      simpa [δ, xSeq] using
        primalGap_le_half_L_mul_sqDist
          (f := f) (f' := f') (L := L) hSmooth
          (x := xSeq t) (x_star := xStarSeq t) (hgradSeq t)
    simpa [F, hvalSeq t] using hsmooth_t
  have hgeom : ∀ t, (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤ g t := by
    intro t
    have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
      have hgradbound_t :
          f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
        simpa [xSeq] using
          (primalGap_le_gradNorm_mul_dist
            (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t))
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by simpa [F, δ, hvalSeq t] using hgradbound_t
    let coeff : ℝ := (μ / 2) * (d t) ^ 2
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      have hμ_pos := hSC.1
      positivity
    have hscaled : coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
    have hsc :
        (μ / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (stronglyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hSC := hSC) (g := f' (xSeq t)) (x := xSeq t) (hxSeq t))
    have hscaled' :
        (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤
          (μ / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hsc
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hx_t : xSeq t ∈ C := hxSeq t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, globalShortStepSequence] using
        (globalShortStep_decrease
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) hx_t)
    linarith [hstep]
  have hcore :=
    tendsto_mul_gap_of_decrease_and_geometry
      (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
      (hL := hL_real) (hμ := hSC.1) (hδ_zero := by simpa [δ, xSeq] using hδ_zero)
      (hgap := hgap) (hsmooth := hsmooth) (hgeom := hgeom) (hdec := hdec)
  simpa [F, xSeq] using hcore

/-- Global short-step gaps converge to zero under the standard `O(1/t)` bound
and the zero-gradient minimizer assumption. -/
lemma globalShortStep_gap_tendsto_zero
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t => f (globalShortStepSequence O f' L x0 t) - f x_star)
      atTop (nhds 0) := by
  have hnonneg :
      ∀ t,
        0 ≤ f (globalShortStepSequence O f' L x0 t) - f x_star := by
    intro t
    exact primalGap_nonneg_of_zero_gradient
      (f := f) (f' := f') hConv
      (x := globalShortStepSequence O f' L x0 t)
      (x_star := x_star) hgrad
  have hbound :=
    global_short_step_convergence
      (O := O)
      hC_convex f f' L hL hSmooth hConv
      hx_star hx0 h0_bound
  exact squeeze_zero hnonneg hbound
    (tendsto_const_div_add_atTop_nhds_zero_nat (2 * (L : ℝ) * (Metric.diam C) ^ 2) 2)

/-- Global short-step gaps also converge to zero when compared against an
arbitrary feasible minimizer, using the standard `O(1/t)` recursion with a
generic initial constant. -/
lemma globalShortStep_gap_tendsto_zero_of_isMinOn
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t => f (globalShortStepSequence O f' L x0 t) - f x_star)
      atTop (nhds 0) := by
  let B : ℝ := max (f x0 - f x_star) ((L : ℝ) * (Metric.diam C) ^ 2)
  have hB_nonneg : 0 ≤ B := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hnonneg :
      ∀ t,
        0 ≤ f (globalShortStepSequence O f' L x0 t) - f x_star := by
    intro t
    exact
      primalGap_nonneg_of_isMinOn
        (C := C) (f := f)
        (globalShortStepSequence_mem
          (O := O)
          hC_convex f' L hx0 t)
        hmin
  have hbound :=
    global_short_step_convergence_of_initialGap_le
      (O := O)
      hC_convex f f' L hL hSmooth hConv hx_star hx0
      hB_nonneg (le_max_left _ _) (le_max_right _ _)
  exact squeeze_zero hnonneg hbound
    (tendsto_const_div_add_atTop_nhds_zero_nat (2 * B) 2)

/-- [FW-BOOST-SS-END] Global short-step Frank-Wolfe satisfies the full boosted
`o(1/t)` theorem once `x_star` is known to be the unique minimizer. -/
theorem globalShortStep_boosted_convergence
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    (hmin_unique : ∀ x ∈ C, f x = f x_star → x = x_star)
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (globalShortStepSequence O f' L x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      globalShortStep_gap_tendsto_zero
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hgrad hx0 h0_bound
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    have hx_t0 : xSeq t0 = x_star := by
      have hx_t0_mem : xSeq t0 ∈ C := by
        simpa [xSeq] using
          globalShortStepSequence_mem
            (O := O)
            hC_convex f' L hx0 t0
      exact hmin_unique (xSeq t0) hx_t0_mem (sub_eq_zero.mp ht0)
    have htail : ∀ n, xSeq (t0 + n) = x_star := by
      intro n
      induction n with
      | zero =>
          simpa using hx_t0
      | succ n ih =>
          calc
            xSeq (t0 + (n + 1))
                = globalShortStep O f' L (xSeq (t0 + n)) := by
                    simp [xSeq, globalShortStepSequence]
            _ = globalShortStep O f' L x_star := by rw [ih]
            _ = x_star := globalShortStep_eq_self_of_zero_gradient
                (O := O)
                (f' := f') (L := L) hgrad
    have h_eventually :
        ∀ᶠ n : ℕ in atTop, (n + 2 : ℝ) * F n = 0 := by
      refine Filter.eventually_atTop.2 ⟨t0, ?_⟩
      intro n hn
      have hxn : xSeq n = x_star := by
        have : n = t0 + (n - t0) := by omega
        rw [this]
        exact htail (n - t0)
      simp [F, hxn]
    exact tendsto_nhds_of_eventually_eq h_eventually
  · have hgap_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        dsimp [F, xSeq]
        exact primalGap_nonneg_of_zero_gradient
          (f := f) (f' := f') hConv
          (x := globalShortStepSequence O f' L x0 t)
          (x_star := x_star) hgrad
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hδ_zero :
        Tendsto (fun t => ‖xSeq t - x_star‖) atTop (nhds 0) := by
      exact tendsto_norm_sub_of_gap_tendsto_zero_of_unique_minimizer
        O.isCompact
        (f := f) (f' := f') (L := L) hConv hSmooth
        hmin_unique xSeq
        (by
          intro t
          simpa [xSeq] using
            globalShortStepSequence_mem
              (O := O)
              hC_convex f' L hx0 t)
        (by simpa [F, xSeq] using hgap_zero)
    simpa [F, xSeq] using
      globalShortStep_boosted_convergence_of_dist_tendsto_zero
        (O := O)
        hC_convex hSC f f' L hL hConv hSmooth hx_star hgrad hx0
        (by simpa [F, xSeq] using hgap_pos) hδ_zero

/-- [FW-BOOST-SS-SET] Global short-step Frank-Wolfe also satisfies the boosted
`o(1/t)` theorem without a uniqueness assumption, by comparing to a varying
nearest minimizer sequence. -/
theorem globalShortStep_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (globalShortStepSequence O f' L x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hM_compact : IsCompact M := by
    simpa [M] using O.isCompact.inter_right hlevel_closed
  have hM_nonempty : M.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [M, hx_star]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      globalShortStep_gap_tendsto_zero
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hgrad hx0 h0_bound
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    let y := xSeq t0
    have hyval : f y = f x_star := by
      exact sub_eq_zero.mp (by simpa [F, y] using ht0)
    have hygrad : f' y = 0 := by
      exact gradient_eq_zero_of_eq_minimizer_value
        (f := f) (f' := f') (L := L) hL hConv hSmooth hgrad hyval
    have htail : ∀ n, xSeq (t0 + n) = y := by
      intro n
      induction n with
      | zero =>
          simp [y]
      | succ n ih =>
          calc
            xSeq (t0 + (n + 1))
                = globalShortStep O f' L (xSeq (t0 + n)) := by
                    simp [xSeq, globalShortStepSequence]
            _ = globalShortStep O f' L y := by rw [ih]
            _ = y := globalShortStep_eq_self_of_zero_gradient
                (O := O)
                (f' := f') (L := L) hygrad
    have h_eventually :
        ∀ᶠ n : ℕ in atTop, (n + 2 : ℝ) * F n = 0 := by
      refine Filter.eventually_atTop.2 ⟨t0, ?_⟩
      intro n hn
      have hxn : xSeq n = y := by
        have : n = t0 + (n - t0) := by omega
        rw [this]
        exact htail (n - t0)
      simp [F, y, hxn, hyval]
    exact tendsto_nhds_of_eventually_eq h_eventually
  · have hgap_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        dsimp [F, xSeq]
        exact primalGap_nonneg_of_zero_gradient
          (f := f) (f' := f') hConv
          (x := globalShortStepSequence O f' L x0 t)
          (x_star := x_star) hgrad
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hdist_zero :
        Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
      simpa [xSeq, M] using
        tendsto_infDist_minimizerSet_of_gap_tendsto_zero
          O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
          (by simpa [F] using hgap_zero)
    classical
    let pSeq : ℕ → E := fun t =>
      Classical.choose (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))
    have hpSeq_memM : ∀ t, pSeq t ∈ M := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).1
    have hpSeq_mem : ∀ t, pSeq t ∈ C := by
      intro t
      exact (hpSeq_memM t).1
    have hpSeq_val : ∀ t, f (pSeq t) = f x_star := by
      intro t
      exact (hpSeq_memM t).2
    have hpSeq_grad : ∀ t, f' (pSeq t) = 0 := by
      intro t
      exact gradient_eq_zero_of_eq_minimizer_value
        (f := f) (f' := f') (L := L) hL hConv hSmooth hgrad (hpSeq_val t)
    have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) M = dist (xSeq t) (pSeq t) := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).2
    have hδ_zero :
        Tendsto (fun t => ‖xSeq t - pSeq t‖) atTop (nhds 0) := by
      have hdist_zero' :
          Tendsto (fun t => dist (xSeq t) (pSeq t)) atTop (nhds 0) := by
        simpa [hpSeq_dist] using hdist_zero
      simpa [dist_eq_norm] using hdist_zero'
    simpa [xSeq] using
      globalShortStep_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
        hC_convex hSC f f' L hL hConv hSmooth x_star pSeq hpSeq_mem hpSeq_val hpSeq_grad hx0
        (by simpa [F, xSeq] using hgap_pos) hδ_zero

/-- If a point already has the same value as a zero-gradient minimizer, exact
line search keeps the objective at that optimal value. -/
lemma exactLineSearch_value_eq_of_isMinOn
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E)
    (hLS : LineSearch O f f')
    {x : E}
    (hx : x ∈ C)
    (hmin : ∀ y ∈ C, f x ≤ f y) :
    f (exactLineSearch O f f' hLS x) = f x := by
  have hopt :
      f (exactLineSearch O f f' hLS x) ≤ f x := by
    simpa [exactLineSearch, frankWolfeStep] using
      (exactLineSearch_optimal
        (O := O)
        (f := f) (f' := f') hLS x
        (γ := 0) (by constructor <;> norm_num))
  have hlow :
      f x ≤ f (exactLineSearch O f f' hLS x) := by
    exact hmin _ <|
      exactLineSearch_mem
        (O := O)
        hC_convex f f' hLS hx
  linarith

/-- If a point already has the same value as a zero-gradient minimizer, exact
line search keeps the objective at that optimal value. -/
lemma exactLineSearch_value_eq_of_eq_minimizer_value
    (f : E → ℝ) (f' : E → E)
    (hLS : LineSearch O f f')
    (hConv : IsFirstOrderConvex f f')
    {x x_star : E}
    (hgrad : f' x_star = 0) (hval : f x = f x_star) :
    f (exactLineSearch O f f' hLS x) = f x_star := by
  have hopt :
      f (exactLineSearch O f f' hLS x) ≤ f x := by
    simpa [exactLineSearch, frankWolfeStep] using
      (exactLineSearch_optimal
        (O := O)
        (f := f) (f' := f') hLS x
        (γ := 0) (by constructor <;> norm_num))
  have hlow :
      f x_star ≤ f (exactLineSearch O f f' hLS x) := by
    have hgap_nonneg :=
      primalGap_nonneg_of_zero_gradient
        (f := f) (f' := f') hConv
        (x := exactLineSearch O f f' hLS x)
        (x_star := x_star) hgrad
    linarith
  linarith

/-- Exact line-search gaps converge to zero under the standard `O(1/t)` bound
and the zero-gradient minimizer assumption. -/
lemma exactLineSearch_gap_tendsto_zero
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f')
    (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t => f (exactLineSearchSequence O f f' hLS x0 t) - f x_star)
      atTop (nhds 0) := by
  have hnonneg :
      ∀ t,
        0 ≤ f (exactLineSearchSequence O f f' hLS x0 t) - f x_star := by
    intro t
    exact primalGap_nonneg_of_zero_gradient
      (f := f) (f' := f') hConv
      (x := exactLineSearchSequence O f f' hLS x0 t)
      (x_star := x_star) hgrad
  have hbound :=
    exact_line_search_convergence
      (O := O)
      hC_convex f f' hLS L hSmooth hConv hx_star hx0 h0_bound
  exact squeeze_zero hnonneg hbound
    (tendsto_const_div_add_atTop_nhds_zero_nat (2 * (L : ℝ) * (Metric.diam C) ^ 2) 2)

/-- Exact line-search gaps also converge to zero when compared against an
arbitrary feasible minimizer. -/
lemma exactLineSearch_gap_tendsto_zero_of_isMinOn
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (hLS : LineSearch O f f')
    (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t => f (exactLineSearchSequence O f f' hLS x0 t) - f x_star)
      atTop (nhds 0) := by
  let B : ℝ := max (f x0 - f x_star) ((L : ℝ) * (Metric.diam C) ^ 2)
  have hB_nonneg : 0 ≤ B := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hnonneg :
      ∀ t,
        0 ≤ f (exactLineSearchSequence O f f' hLS x0 t) - f x_star := by
    intro t
    exact
      primalGap_nonneg_of_isMinOn
        (C := C) (f := f)
        (exactLineSearchSequence_mem
          (O := O)
          hC_convex f f' hLS hx0 t)
        hmin
  have hbound :=
    exact_line_search_convergence_of_initialGap_le
      (O := O)
      hC_convex f f' hLS L hSmooth hConv hx_star hx0
      hB_nonneg (le_max_left _ _) (le_max_right _ _)
  exact squeeze_zero hnonneg hbound
    (tendsto_const_div_add_atTop_nhds_zero_nat (2 * B) 2)

/-- [FW-BOOST-LS-SEQ] Exact line-search Frank-Wolfe satisfies the abstract
boosted theorem once the iterates approach a varying zero-gradient minimizer
sequence. -/
theorem exactLineSearch_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hgradSeq : ∀ t, f' (xStarSeq t) = 0)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C)
    (hgap_pos :
      ∀ t,
        0 < f
          (exactLineSearchSequence O f f'
            hLS
            x0 t) - f x_star)
    (hδ_zero :
      Tendsto
        (fun t =>
          ‖exactLineSearchSequence O f f'
              hLS
              x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f
            (exactLineSearchSequence O f f'
              hLS
              x0 t) - f x_star))
      atTop (nhds 0) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hF_pos : ∀ t, 0 < F t := by
    intro t
    simpa [F, xSeq] using hgap_pos t
  have hδ_pos : ∀ t, 0 < δ t := by
    intro t
    show 0 < ‖xSeq t - xStarSeq t‖
    exact norm_sub_pos_of_primalGap_pos_of_valSeq hvalSeq hF_pos t
  have hd_pos : ∀ t, 0 < d t := by
    intro t
    have hgap_le : F t ≤ g t := by
      have hgap_le' :
          f (xSeq t) - f (xStarSeq t) ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
      simpa [F, hvalSeq t] using hgap_le'
    have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
    by_contra hdt
    have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    have : g t = 0 := by simp [g, hsx]
    exact hg_pos.ne' this
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f (xStarSeq t) ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
    simpa [F, hvalSeq t] using hgap_le'
  have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
    intro t
    have hsmooth_t :
        f (xSeq t) - f (xStarSeq t) ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      simpa [δ, xSeq] using
        primalGap_le_half_L_mul_sqDist
          (f := f) (f' := f') (L := L) hSmooth
          (x := xSeq t) (x_star := xStarSeq t) (hgradSeq t)
    simpa [F, hvalSeq t] using hsmooth_t
  have hgeom : ∀ t, (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤ g t := by
    intro t
    have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
      have hgradbound_t :
          f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
        simpa [xSeq] using
          (primalGap_le_gradNorm_mul_dist
            (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t))
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by simpa [F, δ, hvalSeq t] using hgradbound_t
    let coeff : ℝ := (μ / 2) * (d t) ^ 2
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      have hμ_pos := hSC.1
      positivity
    have hscaled : coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
    have hsc :
        (μ / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (stronglyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hSC := hSC) (g := f' (xSeq t)) (x := xSeq t) (hxSeq t))
    have hscaled' :
        (μ / 2) * (F t / δ t) * (d t) ^ 2 ≤
          (μ / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' hsc
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hx_t : xSeq t ∈ C := hxSeq t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, exactLineSearchSequence] using
        (exactLineSearch_decrease
          (O := O)
          (f := f) (f' := f') (L := L) hLS hSmooth (x := xSeq t) hx_t)
    linarith [hstep]
  have hcore :=
    tendsto_mul_gap_of_decrease_and_geometry
      (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
      (hL := hL_real) (hμ := hSC.1) (hδ_zero := by simpa [δ, xSeq] using hδ_zero)
      (hgap := hgap) (hsmooth := hsmooth) (hgeom := hgeom) (hdec := hdec)
  simpa [F, xSeq] using hcore

/-- [FW-BOOST-LS-SET] Exact line-search Frank-Wolfe also satisfies the boosted
`o(1/t)` theorem without a uniqueness assumption, by comparing to a varying
nearest minimizer sequence. -/
theorem exactLineSearch_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f
            (exactLineSearchSequence O f f'
              hLS
              x0 t) - f x_star))
      atTop (nhds 0) := by
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hfc continuous_const
  have hM_compact : IsCompact M := by
    simpa [M] using O.isCompact.inter_right hlevel_closed
  have hM_nonempty : M.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [M, hx_star]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      exactLineSearch_gap_tendsto_zero
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hgrad hx0 h0_bound
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    have htail_val : ∀ n, f (xSeq (t0 + n)) = f x_star := by
      intro n
      induction n with
      | zero =>
          exact sub_eq_zero.mp (by simpa [F, xSeq] using ht0)
      | succ n ih =>
          simpa [xSeq, exactLineSearchSequence, Nat.add_assoc] using
            (exactLineSearch_value_eq_of_eq_minimizer_value
              (O := O)
              (f := f) (f' := f') hLS hConv
              (x := xSeq (t0 + n)) (x_star := x_star) hgrad ih)
    have h_eventually :
        ∀ᶠ n : ℕ in atTop, (n + 2 : ℝ) * F n = 0 := by
      refine Filter.eventually_atTop.2 ⟨t0, ?_⟩
      intro n hn
      have hfn : f (xSeq n) = f x_star := by
        have : n = t0 + (n - t0) := by omega
        rw [this]
        exact htail_val (n - t0)
      simp [F, hfn]
    exact tendsto_nhds_of_eventually_eq h_eventually
  · have hgap_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        dsimp [F, xSeq]
        exact primalGap_nonneg_of_zero_gradient
          (f := f) (f' := f') hConv
          (x := exactLineSearchSequence O f f' hLS x0 t)
          (x_star := x_star) hgrad
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hdist_zero :
        Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
      simpa [xSeq, M] using
        tendsto_infDist_minimizerSet_of_gap_tendsto_zero
          O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
          (by simpa [F] using hgap_zero)
    classical
    let pSeq : ℕ → E := fun t =>
      Classical.choose (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))
    have hpSeq_memM : ∀ t, pSeq t ∈ M := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).1
    have hpSeq_mem : ∀ t, pSeq t ∈ C := by
      intro t
      exact (hpSeq_memM t).1
    have hpSeq_val : ∀ t, f (pSeq t) = f x_star := by
      intro t
      exact (hpSeq_memM t).2
    have hpSeq_grad : ∀ t, f' (pSeq t) = 0 := by
      intro t
      exact gradient_eq_zero_of_eq_minimizer_value
        (f := f) (f' := f') (L := L) hL hConv hSmooth hgrad (hpSeq_val t)
    have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) M = dist (xSeq t) (pSeq t) := by
      intro t
      exact (Classical.choose_spec (hM_compact.exists_infDist_eq_dist hM_nonempty (xSeq t))).2
    have hδ_zero :
        Tendsto (fun t => ‖xSeq t - pSeq t‖) atTop (nhds 0) := by
      have hdist_zero' :
          Tendsto (fun t => dist (xSeq t) (pSeq t)) atTop (nhds 0) := by
        simpa [hpSeq_dist] using hdist_zero
      simpa [dist_eq_norm] using hdist_zero'
    simpa [xSeq] using
      exactLineSearch_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
        hC_convex hSC f f' L hL hConv hSmooth x_star pSeq hpSeq_mem hpSeq_val hpSeq_grad hLS hx0
        (by simpa [F, xSeq] using hgap_pos) hδ_zero

/-- Under the strong-convex-set correction, one canonical Frank-Wolfe step with
the fixed rule `γ_t = 2 / (t + 2)` admits a local dual sharpness recursion whose
curvature term only depends on the current comparison distance. -/
lemma frankWolfeStep_gap_bound_with_correction
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E} (hx_star : x_star ∈ C)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hγsmall : γ ≤ μ * ‖f' x‖ / (2 * (L : ℝ))) :
    f (frankWolfeStep O f' x γ) - f x_star ≤
      (1 - γ) * (f x - f x_star) + (L : ℝ) * γ ^ 2 * ‖x - x_star‖ ^ 2 := by
  have hγsmall_kernel : γ * (L : ℝ) ≤ (μ / 2) * ‖f' x‖ := by
    by_cases hL0 : (L : ℝ) = 0
    · simp only [hL0, mul_zero]
      exact mul_nonneg (by linarith [hSC.1]) (norm_nonneg _)
    · have hL_pos : 0 < (L : ℝ) := lt_of_le_of_ne (by exact_mod_cast L.2) (Ne.symm hL0)
      have hmul := mul_le_mul_of_nonneg_left hγsmall hL_pos.le
      rw [show (L : ℝ) * (μ * ‖f' x‖ / (2 * (L : ℝ))) = μ / 2 * ‖f' x‖ by
            field_simp [hL0]] at hmul
      linarith
  exact frankWolfeStep_gap_bound_quadratic_kernel
    O f f' L hConv hSmooth hγ
    (A := μ / 2) hγsmall_kernel
    (by simpa [norm_sub_rev] using
        stronglyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hSC := hSC) (g := f' x) (x := x_star) hx_star)

/-- Canonical fixed-step Frank-Wolfe gaps converge to zero under the standard
`O(1/t)` bound and the zero-gradient minimizer assumption. -/
lemma frankWolfe_gap_tendsto_zero
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    {x0 : E} (hx0 : x0 ∈ C)
    (h0_bound : f x0 - f x_star ≤ L * (Metric.diam C) ^ 2) :
    Tendsto
      (fun t => f (frankWolfeSequence O f' x0 t) - f x_star)
      atTop (nhds 0) := by
  have hnonneg :
      ∀ t,
        0 ≤ f (frankWolfeSequence O f' x0 t) - f x_star := by
    intro t
    exact primalGap_nonneg_of_zero_gradient
      (f := f) (f' := f') hConv
      (x := frankWolfeSequence O f' x0 t)
      (x_star := x_star) hgrad
  have hbound :=
    frank_wolfe_convergence
      (O := O)
      hC_convex f f' L hSmooth hConv hx_star hx0 h0_bound
  exact squeeze_zero hnonneg hbound
    (tendsto_const_div_add_atTop_nhds_zero_nat (2 * (L : ℝ) * (Metric.diam C) ^ 2) 2)

/-- Canonical fixed-step Frank-Wolfe gaps also converge to zero when compared
against an arbitrary feasible minimizer. -/
lemma frankWolfe_gap_tendsto_zero_of_isMinOn
    (hC_convex : Convex ℝ C)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t => f (frankWolfeSequence O f' x0 t) - f x_star)
      atTop (nhds 0) := by
  let B : ℝ := max (f x0 - f x_star) ((L : ℝ) * (Metric.diam C) ^ 2)
  have hB_nonneg : 0 ≤ B := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hnonneg :
      ∀ t,
        0 ≤ f (frankWolfeSequence O f' x0 t) - f x_star := by
    intro t
    exact
      primalGap_nonneg_of_isMinOn
        (C := C) (f := f)
        (frankWolfeSequence_mem
          (O := O)
          hC_convex f' hx0 t)
        hmin
  have hbound :=
    frank_wolfe_convergence_of_initialGap_le
      (O := O)
      hC_convex f f' L hSmooth hConv hx_star hx0
      hB_nonneg (le_max_left _ _) (le_max_right _ _)
  exact squeeze_zero hnonneg hbound
    (tendsto_const_div_add_atTop_nhds_zero_nat (2 * B) 2)

/-- Elementary coefficient bound for the open-loop scaling `γ_t = 2 / (t + 2)`. -/
lemma frankWolfe_openLoop_coeff_le_one (t : ℕ) :
    (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ 1 := by
  have := openLoop_coeff_le_one (ell := 2) (hell := by norm_num) t
  push_cast at this; ring_nf at this ⊢; linarith

/-- The fixed-step curvature tail is bounded by the standard `1 / t` tail. -/
lemma frankWolfe_openLoop_stdConst_bound
    {B : ℝ} (hB : 0 ≤ B) (t : ℕ) :
    2 * B * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ 4 * B / (t + 2 : ℝ) := by
  have := openLoop_stdConst_bound (ell := 2) (hell := by norm_num) hB t
  push_cast at this; ring_nf at this ⊢; linarith

/-- Auxiliary coefficient bound for the refined open-loop stability step. -/
lemma frankWolfe_openLoop_refined_coeff_le_one (t : ℕ) :
    (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 +
      (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ 1 := by
  have := openLoop_refined_coeff_le_one (ell := 2) (hell := by norm_num) t
  push_cast at this; ring_nf at this ⊢; linarith

/-- The same refined coefficient is in fact separated from `1` by a concrete
`1/(2(t+2))` slack. -/
lemma frankWolfe_openLoop_refined_coeff_drop (t : ℕ) :
    (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 +
      (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤
        1 - 1 / (2 * (t + 2 : ℝ)) := by
  have := openLoop_refined_coeff_drop (ell := 2) (hell := by norm_num) t
  push_cast at this; ring_nf at this ⊢; linarith

/-- Scaling the standard one-step bound by `t + 3` yields the `h_{t+1}` form
used in the open-loop proof. -/
lemma frankWolfe_openLoop_scaled_standard_eq
    {F : ℕ → ℝ} {Dsq L : ℝ} (t : ℕ) :
    (t + 3 : ℝ) *
        ((1 - 2 / (t + 2 : ℝ)) * F t +
          (L / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq) =
      ((t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2) * ((t + 2 : ℝ) * F t) +
        2 * L * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
  have h := openLoop_scaled_standard_eq (ell := 2) (hell := by norm_num)
    (F := F) (Dsq := Dsq) (L := L) t
  push_cast at h; ring_nf at h ⊢; linarith

/-- Scaling the refined one-step bound by `t + 3` yields the `h_{t+1}` form
used in the open-loop proof. -/
lemma frankWolfe_openLoop_scaled_refined_eq
    {F δ : ℕ → ℝ} {L : ℝ} (t : ℕ) :
    (t + 3 : ℝ) *
        ((1 - 2 / (t + 2 : ℝ)) * F t +
          L * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2) =
      ((t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2) * ((t + 2 : ℝ) * F t) +
        4 * L * (δ t) ^ 2 * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
  have h := openLoop_scaled_refined_eq (ell := 2) (hell := by norm_num)
    (F := F) (δ := δ) (L := L) t
  push_cast at h; ring_nf at h ⊢; linarith

/-- If `H ≥ ε`, then the refined open-loop affine update is already smaller
than `H` by at least `ε / (2(t+2))`. -/
lemma frankWolfe_openLoop_drop_bound
    (t : ℕ) {ε H : ℝ} (hε : 0 ≤ ε) (hH : ε ≤ H) :
    (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 * H +
      (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤
        H - ε / (2 * (t + 2 : ℝ)) := by
  have h := openLoop_drop_bound (ell := 2) (hell := by norm_num) t hε hH
  push_cast at h; ring_nf at h ⊢; linarith

/-- On the block `N0 ≤ t ≤ 2N0`, the reciprocal denominator
`2(t+2)` is at most `4(N0+1)`. -/
lemma frankWolfe_openLoop_blockFraction_bound
    {ε : ℝ} (hε : 0 ≤ ε) {N0 t : ℕ}
    (htN0 : t ≤ 2 * N0) :
    ε / (4 * (N0 + 1 : ℝ)) ≤ ε / (2 * (t + 2 : ℝ)) := by
  have hden_nat : 2 * (t + 2) ≤ 4 * (N0 + 1) := by
    omega
  have hden : 2 * (t + 2 : ℝ) ≤ 4 * (N0 + 1 : ℝ) := by
    exact_mod_cast hden_nat
  have hinv :
      (4 * (N0 + 1 : ℝ))⁻¹ ≤ (2 * (t + 2 : ℝ))⁻¹ := by
    exact inv_anti₀ (by positivity : 0 < 2 * (t + 2 : ℝ)) hden
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hinv hε)

/-- [FW-BOOST-FW-SEQ] The canonical fixed-step Frank-Wolfe sequence also
satisfies the boosted `o(1/t)` conclusion once the iterates approach a varying
feasible minimizer sequence. -/
theorem frankWolfe_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (x_star : E)
    (xStarSeq : ℕ → E)
    (hxStarSeq : ∀ t, xStarSeq t ∈ C)
    (hvalSeq : ∀ t, f (xStarSeq t) = f x_star)
    (hminSeq : ∀ t, ∀ y ∈ C, f (xStarSeq t) ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C)
    (hδ_zero :
      Tendsto
        (fun t => ‖frankWolfeSequence O f' x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (frankWolfeSequence O f' x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := frankWolfeSequence O f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let h : ℕ → ℝ := fun t => (t + 2 : ℝ) * F t
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let M : ℝ := 2 * max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let Ksmall : ℝ := 4 * (L : ℝ) / μ
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => 2 * (L : ℝ) * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  let beta : ℕ → ℝ :=
    fun t => 4 * (L : ℝ) * (δ t) ^ 2 * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeSequence_mem
        (O := O)
        hC_convex f' hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    show 0 ≤ f (xSeq t) - f x_star
    exact primalGap_nonneg_of_minimizerSeq' hvalSeq hminSeq hxSeq t
  have hgap_grad : ∀ t, F t ≤ ‖f' (xSeq t)‖ * δ t := by
    intro t
    have hgap_t :
        f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
      simpa [xSeq] using
        (primalGap_le_gradNorm_mul_dist
          (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := xStarSeq t))
    simpa [F, δ, hvalSeq t] using hgap_t
  have hsmall_or_refined :
      ∀ t,
        h t ≤ Ksmall * δ t ∨
          F (t + 1) ≤
            (1 - 2 / (t + 2 : ℝ)) * F t +
              (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hKsmall_nonneg : 0 ≤ Ksmall := by
        have hμ_pos := hSC.1
        positivity
      have hδ_nonneg : 0 ≤ δ t := by
        dsimp [δ]
        positivity
      simpa [h, hFt0] using (mul_nonneg hKsmall_nonneg hδ_nonneg)
    · by_cases hcase : 2 / (t + 2 : ℝ) ≤ μ * ‖f' (xSeq t)‖ / (2 * (L : ℝ))
      · right
        have href :
            f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
                f (xStarSeq t) ≤
              (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
                (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * ‖xSeq t - xStarSeq t‖ ^ 2 := by
          simpa [xSeq, δ] using
            (frankWolfeStep_gap_bound_with_correction
              (O := O)
              (C := C) (hSC := hSC) (f := f) (f' := f') (L := L) hConv hSmooth
              (x := xSeq t) (x_star := xStarSeq t) (hxStarSeq t)
              (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t) hcase)
        simpa [F, xSeq, frankWolfeSequence, hvalSeq t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
      · left
        have hδ_pos_t : 0 < δ t := by
          by_contra hδt
          have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
          have hxeq : xSeq t = xStarSeq t := by
            exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
          have : F t = 0 := by simp [F, hxeq, hvalSeq t]
          exact hFt0 this
        have hcase' :
            μ * ‖f' (xSeq t)‖ / (2 * (L : ℝ)) < 2 / (t + 2 : ℝ) := lt_of_not_ge hcase
        have hmul :
            μ * ‖f' (xSeq t)‖ < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
          exact (_root_.div_lt_iff₀ (show 0 < 2 * (L : ℝ) by positivity)).1 hcase'
        have hgrad_lt :
            ‖f' (xSeq t)‖ < ((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / μ := by
          have : ‖f' (xSeq t)‖ * μ < (2 / (t + 2 : ℝ)) * (2 * (L : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          exact (_root_.lt_div_iff₀ hSC.1).2 this
        have hsmall' :
            F t < (((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / μ) * δ t := by
          exact lt_of_le_of_lt (hgap_grad t) <|
            mul_lt_mul_of_pos_right hgrad_lt hδ_pos_t
        have hscaled :
            h t < Ksmall * δ t := by
          dsimp [h, Ksmall]
          have hEq :
              (t + 2 : ℝ) * ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / μ) * δ t) =
                (4 * (L : ℝ) / μ) * δ t := by
            field_simp [hSC.1.ne', (show (t + 2 : ℝ) ≠ 0 by positivity)]
            ring
          have hmul' :
              (t + 2 : ℝ) * F t <
                (t + 2 : ℝ) * ((((2 / (t + 2 : ℝ)) * (2 * (L : ℝ))) / μ) * δ t) := by
            exact mul_lt_mul_of_pos_left hsmall' (by positivity)
          simpa [hEq] using hmul'
        exact le_of_lt hscaled
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - 2 / (t + 2 : ℝ)) * F t +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f' (xSeq t) (2 / (t + 2 : ℝ))) -
            f (xStarSeq t) ≤
          (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
            ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := xStarSeq t) (hxSeq t) (hxStarSeq t)
          (γ := 2 / (t + 2 : ℝ)) (standardStepSize_mem_Icc t))
    simpa [F, xSeq, frankWolfeSequence, hvalSeq t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
  have hstd_bound :
      ∀ t, F t ≤ M / (t + 2 : ℝ) := by
    intro t
    let B : ℝ := max (f x0 - f (xStarSeq 0)) ((L : ℝ) * Dsq)
    have hB_nonneg : 0 ≤ B := by
      have hgap0_nonneg : 0 ≤ f x0 - f (xStarSeq 0) := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 (hminSeq 0)
      exact le_trans hgap0_nonneg (le_max_left _ _)
    have hfw :=
      frank_wolfe_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hSmooth hConv (hx_star := hxStarSeq 0) hx0
        hB_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [B, M, F, xSeq, hvalSeq 0] using hfw
  have hbounded : ∀ t, h t ≤ M := by
    intro t
    calc
      h t = (t + 2 : ℝ) * F t := by rfl
      _ ≤ (t + 2 : ℝ) * (M / (t + 2 : ℝ)) := by
            gcongr
            exact hstd_bound t
      _ = M := by
            field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
  have hnonneg_h : ∀ t, 0 ≤ h t := by
    intro t
    dsimp [h]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  apply boosted_convergence_kernel hnonneg_h
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hKsmall_event : ∀ᶠ t : ℕ in atTop, Ksmall * δ t < ε / 2 := by
    have hKzero :
        Tendsto (fun t => Ksmall * δ t) atTop (nhds 0) := by
      simpa [δ, Ksmall] using hδ_zero.const_mul Ksmall
    exact hKzero.eventually (Iio_mem_nhds hε2)
  have hδsq_zero : Tendsto (fun t => (δ t) ^ 2) atTop (nhds 0) := by
    simpa using hδ_zero.pow 2
  have hbeta_event : ∀ᶠ t : ℕ in atTop, 4 * (L : ℝ) * (δ t) ^ 2 < ε / 2 := by
    have hbeta_zero :
        Tendsto (fun t => 4 * (L : ℝ) * (δ t) ^ 2) atTop (nhds 0) := by
      simpa using hδsq_zero.const_mul (4 * (L : ℝ))
    exact hbeta_zero.eventually (Iio_mem_nhds hε2)
  have hstdconst_zero : Tendsto (fun t : ℕ => (4 * (L : ℝ) * Dsq) / (t + 2 : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_add_atTop_nhds_zero_nat (4 * (L : ℝ) * Dsq) 2
  have hstdconst_event : ∀ᶠ t : ℕ in atTop, stdConst t < ε / 2 := by
    have hmain := hstdconst_zero.eventually (Iio_mem_nhds hε2)
    filter_upwards [hmain] with t ht
    have hbound_t : stdConst t ≤ (4 * (L : ℝ) * Dsq) / (t + 2 : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (frankWolfe_openLoop_stdConst_bound
          (B := (L : ℝ) * Dsq) hB_nonneg t)
    exact lt_of_le_of_lt hbound_t ht
  have hall :
      ∀ᶠ t : ℕ in atTop,
        Ksmall * δ t < ε / 2 ∧
          4 * (L : ℝ) * (δ t) ^ 2 < ε / 2 ∧
          stdConst t < ε / 2 := by
    filter_upwards [hKsmall_event, hbeta_event, hstdconst_event] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  rcases Filter.Eventually.exists_forall_of_atTop hall with ⟨T, hT⟩
  have hstable :
      ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε := by
    intro t ht hle
    rcases hT t ht with ⟨hsmallT, hbetaT, hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
        change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
        have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
          exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
        rw [hcast]
      have hstep : h (t + 1) ≤ a t * h t + stdConst t := by
        have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + 3 : ℝ))
        calc
          h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + 3 : ℝ) *
                ((1 - 2 / (t + 2 : ℝ)) * F t +
                  ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq) := hmul
          _ = a t * h t + stdConst t := by
                simpa [a, h, stdConst, mul_assoc, mul_left_comm, mul_comm] using
                  (frankWolfe_openLoop_scaled_standard_eq
                    (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
      have hmain : h (t + 1) ≤ h t + stdConst t := by
        have ha_le_one : a t ≤ 1 := by
          simpa [a] using frankWolfe_openLoop_coeff_le_one t
        have hah : a t * h t ≤ h t := by
          simpa using mul_le_mul_of_nonneg_right ha_le_one (hnonneg_h t)
        linarith
      have hlt : h (t + 1) < ε := by
        linarith
      exact le_of_lt hlt
    · have hstep : h (t + 1) ≤ a t * h t + beta t := by
        have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
            exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + 3 : ℝ))
        calc
          h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + 3 : ℝ) *
                ((1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
          _ = a t * h t + beta t := by
                simpa [a, h, beta, mul_assoc, mul_left_comm, mul_comm] using
                  (frankWolfe_openLoop_scaled_refined_eq
                    (F := F) (δ := δ) (L := (L : ℝ)) t)
      have hbeta_le :
          beta t ≤ (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
        let c : ℝ := (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
        have hc_nonneg : 0 ≤ c := by
          dsimp [c]
          positivity
        have hbeta_base :
            (4 * (L : ℝ) * (δ t) ^ 2) * c ≤ (ε / 2) * c := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hbetaT) hc_nonneg
        have hbeta_eq :
            beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := by
          dsimp [beta, c]
          rw [div_eq_mul_inv]
          ring
        calc
          beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := hbeta_eq
          _ ≤ (ε / 2) * c := hbeta_base
          _ = (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
                dsimp [c]
                ring
      have hcoeff :
          a t * ε + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ ε := by
        have hcoeff_unit :
            a t + (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ 1 := by
          simpa [a] using frankWolfe_openLoop_refined_coeff_le_one t
        have hmul :
            ε * (a t + (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2) ≤ ε := by
          simpa using mul_le_mul_of_nonneg_left hcoeff_unit (le_of_lt hε)
        have hEq :
            ε * (a t + (1 / 2 : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2) =
              a t * ε + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
          ring
        rw [hEq] at hmul
        exact hmul
      have hmain :
          h (t + 1) ≤ a t * ε + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
        have ha_nonneg : 0 ≤ a t := by
          dsimp [a]
          positivity
        have hah : a t * h t ≤ a t * ε := by
          exact mul_le_mul_of_nonneg_left hle ha_nonneg
        linarith
      exact le_trans hmain hcoeff
  have habove_drop :
      ∀ N0 t, T ≤ N0 → N0 ≤ t → t ≤ 2 * N0 → ε < h t →
        h (t + 1) ≤ h t - ε / (4 * (N0 + 1 : ℝ)) := by
    intro N0 t hTN hN0 htN0 hgt
    rcases hT t (le_trans hTN hN0) with ⟨hsmallT, hbetaT, _hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · exfalso
      linarith [hleft, hsmallT, hgt]
    · have hstep : h (t + 1) ≤ a t * h t + beta t := by
        have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
            exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + 3 : ℝ))
        calc
          h (t + 1) = (t + 3 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + 3 : ℝ) *
                ((1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2) := hmul
          _ = a t * h t + beta t := by
                simpa [a, h, beta, mul_assoc, mul_left_comm, mul_comm] using
                  (frankWolfe_openLoop_scaled_refined_eq
                    (F := F) (δ := δ) (L := (L : ℝ)) t)
      have hbeta_le :
          beta t ≤ (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
        let c : ℝ := (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
        have hc_nonneg : 0 ≤ c := by
          dsimp [c]
          positivity
        have hbeta_base :
            (4 * (L : ℝ) * (δ t) ^ 2) * c ≤ (ε / 2) * c := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hbetaT) hc_nonneg
        have hbeta_eq :
            beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := by
          dsimp [beta, c]
          rw [div_eq_mul_inv]
          ring
        calc
          beta t = (4 * (L : ℝ) * (δ t) ^ 2) * c := hbeta_eq
          _ ≤ (ε / 2) * c := hbeta_base
          _ = (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
                dsimp [c]
                ring
      have hdrop :
          h (t + 1) ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
        have hdrop_aux :
            a t * h t + (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤
              h t - ε / (2 * (t + 2 : ℝ)) := by
          simpa [a] using
            frankWolfe_openLoop_drop_bound t (hε := le_of_lt hε) (hH := le_of_lt hgt)
        linarith
      have hfrac :
          ε / (4 * (N0 + 1 : ℝ)) ≤ ε / (2 * (t + 2 : ℝ)) := by
        exact frankWolfe_openLoop_blockFraction_bound
          (hε := le_of_lt hε) htN0
      have hsub :
          h t - ε / (2 * (t + 2 : ℝ)) ≤ h t - ε / (4 * (N0 + 1 : ℝ)) := by
        linarith
      exact le_trans hdrop hsub
  refine ⟨T, M, ε / 4, by linarith, hbounded T, hstable, ?_⟩
  have hNseq_succ : ∀ j, 2 ^ (j + 1) * (T + 1) - 1 = 2 * (2 ^ j * (T + 1) - 1) + 1 :=
    nseq_succ T
  have hNseq_ge : ∀ j, T ≤ 2 ^ j * (T + 1) - 1 :=
    nseq_ge T
  have htail_above : ∀ {p t : ℕ}, T ≤ t → t ≤ p → ε < h p → ε < h t :=
    fun htT htp hpgt => tail_above_of_stable hstable htT htp hpgt
  intro k n hkn hngt
  let Nk : ℕ := 2 ^ k * (T + 1) - 1
  have hNk_succ : 2 ^ (k + 1) * (T + 1) - 1 = 2 * Nk + 1 := hNseq_succ k
  have hNk_ge : T ≤ Nk := hNseq_ge k
  have hablock : ∀ t, Nk ≤ t → t ≤ 2 * Nk → ε < h t := by
    intro t hlow hhigh
    have htn : t ≤ n := by rw [hNk_succ] at hkn; omega
    exact htail_above (le_trans hNk_ge hlow) htn hngt
  have hstepblock :
      ∀ t, Nk ≤ t → t ≤ 2 * Nk →
        ε / (4 * (↑Nk + 1 : ℝ)) ≤ h t - h (t + 1) := by
    intro t hlow hhigh
    linarith [habove_drop Nk t hNk_ge hlow hhigh (hablock t hlow hhigh)]
  have hdrop' :=
    block_drop_of_step_drop (h := h) (ε := ε) (N := Nk) hstepblock
  simpa [hNk_succ] using hdrop'

/-- [FW-BOOST-FW-SET] The canonical fixed-step Frank-Wolfe sequence also
admits the full boosted `o(1/t)` conclusion without a uniqueness assumption,
by comparing the iterates to a varying nearest feasible minimizer sequence. -/
theorem frankWolfe_boosted_convergence_of_minimizer
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (frankWolfeSequence O f' x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := frankWolfeSequence O f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let M : Set E := C ∩ {y : E | f y = f x_star}
  have hcont : Continuous f :=
    continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  have hlevel_closed : IsClosed {y : E | f y = f x_star} :=
    isClosed_eq hcont continuous_const
  have hM_compact : IsCompact M := by
    simpa [M] using O.isCompact.inter_right hlevel_closed
  have hM_nonempty : M.Nonempty := by
    refine ⟨x_star, ?_⟩
    simp [M, hx_star]
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      frankWolfeSequence_mem
        (O := O)
        hC_convex f' hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      frankWolfe_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hConv hSmooth hx_star hmin hx0
  have hdist_zero :
      Tendsto (fun t => Metric.infDist (xSeq t) M) atTop (nhds 0) := by
    simpa [xSeq, M] using
      tendsto_infDist_minimizerSet_of_gap_tendsto_zero
        O.isCompact (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
        (by simpa [F] using hgap_zero)
  let pSeq : ℕ → E := nearestPoint hM_compact hM_nonempty ∘ xSeq
  have hpSeq_memM : ∀ t, pSeq t ∈ M :=
      fun t => nearestPoint_mem hM_compact hM_nonempty (xSeq t)
  have hpSeq_dist : ∀ t, Metric.infDist (xSeq t) M = dist (xSeq t) (pSeq t) :=
      fun t => infDist_nearestPoint hM_compact hM_nonempty (xSeq t)
  have hδ_zero' : Filter.Tendsto (fun t => dist (xSeq t) (pSeq t)) Filter.atTop (nhds 0) :=
      tendsto_dist_nearestPoint_of_tendsto_infDist hM_compact hM_nonempty hdist_zero
  have hpSeq_mem : ∀ t, pSeq t ∈ C := fun t => (hpSeq_memM t).1
  have hpSeq_val : ∀ t, f (pSeq t) = f x_star := fun t => (hpSeq_memM t).2
  have hpSeq_min : ∀ t, ∀ y ∈ C, f (pSeq t) ≤ f y := fun t y hy => by
    linarith [hmin y hy, hpSeq_val t]
  have hδ_zero : Tendsto (fun t => ‖xSeq t - pSeq t‖) atTop (nhds 0) :=
    hδ_zero'.congr (fun t => dist_eq_norm _ _)
  simpa [xSeq] using
    frankWolfe_boosted_convergence_of_minimizerSequence_tendsto_zero
      (O := O)
      hC_convex hSC f f' L hL hConv hSmooth x_star pSeq hpSeq_mem hpSeq_val hpSeq_min hx0 hδ_zero

/-- Backward-compatible wrapper for the older zero-gradient formulation of the
fixed-step set theorem. -/
theorem frankWolfe_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {μ : ℝ} (hSC : IsStronglyConvex C μ)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + 2 : ℝ) *
          (f (frankWolfeSequence O f' x0 t) - f x_star))
      atTop (nhds 0) := by
  exact
    frankWolfe_boosted_convergence_of_minimizer
      (O := O)
      hC_convex hSC f f' L hL hConv hSmooth hx_star
      (fun y _hy =>
        by
          have hgap_nonneg :=
            primalGap_nonneg_of_zero_gradient
              (f := f) (f' := f') hConv
              (x := y) (x_star := x_star) hgrad
          linarith)
      hx0

/-- [FW-BOOST-FW] Abstract boosted theorem for the canonical Frank-Wolfe
sequence `γ_t = 2 / (t + 2)`: if the reciprocal primal-gap increments diverge
along the iterates, then the primal gap is `o(1/t)`.

This remains available as an abstract bridge, even though the concrete fixed-step
route above is now closed directly by the block-drop argument. -/
theorem frank_wolfe_boosted_convergence
  (f : E → ℝ) (f' : E → E) (x_star x0 : E)
  (hgap_pos : ∀ t, 0 < primalGapSequence O f f' x_star x0 t)
  (hrecip :
    ReciprocalIncrementDiverges
      (primalGapSequence O f f' x_star x0)) :
  Tendsto
    (fun t : ℕ =>
      (t + 2 : ℝ) * (f (frankWolfeSequence O f' x0 t) - f x_star))
    atTop (nhds 0) := by
  simpa [primalGapSequence] using
    tendsto_mul_gap_of_increment_divergence
      (hF_pos := hgap_pos) hrecip

end BoostedConvergence

end Lemmata.FrankWolfeLDS
