module

public import Lemmata.FrankWolfeLDS.Proof.BoostedConvergence
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.FrankWolfeLDS

open InnerProductSpace Set Filter
local notation "inner" => inner ℝ

section UniformlyConvexGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E}

/-- A compact convex set is uniformly convex of power type `q` if every chord
admits the standard power-size bulge in each unit direction. -/
def IsUniformlyConvexPower (C : Set E) (α : ℝ) (q : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
    ∀ z : E, ‖z‖ = 1 →
      θ • x + (1 - θ) • y + (θ * (1 - θ) * α * ‖x - y‖ ^ q) • z ∈ C

/-- The midpoint-bulge formulation of uniform convexity yields the support
inequality actually used by the Frank-Wolfe argument. -/
lemma uniformlyConvex_support_lower_bound
    {α : ℝ} {q : ℝ} (hUC : IsUniformlyConvexPower C α q)
    {v x η : E} (hv : v ∈ C) (hx : x ∈ C)
    (hnormal : ∀ y ∈ C, inner η (y - v) ≥ (0 : ℝ)) :
    (α / 2) * ‖η‖ * ‖x - v‖ ^ q ≤ inner η (x - v) := by
  by_cases hη : η = 0
  · simp [hη]
  · let z : E := -((‖η‖)⁻¹) • η
    have hη_norm : ‖η‖ ≠ 0 := norm_ne_zero_iff.mpr hη
    have hz : ‖z‖ = 1 := by
      calc
        ‖z‖ = ‖-((‖η‖)⁻¹)‖ * ‖η‖ := by simp [z, norm_smul]
        _ = ((‖η‖)⁻¹) * ‖η‖ := by
              simp
        _ = 1 := by field_simp [hη_norm]
    have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    let y : E :=
      (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • v +
        (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) * α * ‖x - v‖ ^ q) • z)
    have hy : y ∈ C := by
      exact hUC x hx v hv (1 / 2 : ℝ) hhalf z hz
    have hy_nonneg : 0 ≤ (inner η (y - v) : ℝ) := hnormal y hy
    have hy_expand :
        (inner η (y - v) : ℝ) =
          (1 / 2 : ℝ) * inner η (x - v) -
            ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) * α * ‖x - v‖ ^ q) * ‖η‖ := by
      have hinner_z : (inner η z : ℝ) = -‖η‖ := by
        calc
          (inner η z : ℝ) = inner η (-((‖η‖)⁻¹) • η) := by rfl
          _ = -((‖η‖)⁻¹) * inner η η := by rw [inner_smul_right]
          _ = -((‖η‖)⁻¹) * ‖η‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
          _ = -((‖η‖)⁻¹) * (‖η‖ * ‖η‖) := by rw [sq]
          _ = -‖η‖ := by
                field_simp [hη_norm]
      dsimp [y]
      rw [inner_sub_right, inner_add_right, inner_add_right,
        inner_smul_right, inner_smul_right, inner_smul_right, hinner_z, inner_sub_right]
      ring
    rw [hy_expand] at hy_nonneg
    have hcoeff :
        ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) * α * ‖x - v‖ ^ q) = (α / 4) * ‖x - v‖ ^ q := by
      ring
    rw [hcoeff] at hy_nonneg
    linarith

/-- Power-type uniform convexity with `q = 2` recovers the strongly-convex-set
support inequality used by the existing quadratic route. -/
lemma uniformlyConvexPower_two_implies_stronglyConvex
    {α : ℝ} (hα : 0 < α) (hUC : IsUniformlyConvexPower C α (2 : ℝ)) :
    IsStronglyConvex C α :=
  ⟨hα, fun v hv η hnormal x hx => by
    simpa using
      (uniformlyConvex_support_lower_bound
        (C := C) (hUC := hUC) (v := v) (x := x) (η := η) hv hx hnormal)⟩

end UniformlyConvexGeometry

section UniformlyConvexBoostedConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} (O : Oracle C)

/-- [FW-UC-GEOM] Uniform convexity upgrades the LMO supporting-normal condition
into a power-type lower bound on the dual gap. -/
lemma uniformlyConvex_lmoGap_lower_bound
    {α : ℝ} {q : ℝ} (hUC : IsUniformlyConvexPower C α q)
    (g : E) {x : E} (hx : x ∈ C) :
    (α / 2) * ‖g‖ * ‖x - LMO O g‖ ^ q ≤
      (inner g (x - LMO O g) : ℝ) := by
  let s := LMO O g
  have hs : s ∈ C := LMO_mem O g
  have hnormal : ∀ y ∈ C, (inner g (y - s) : ℝ) ≥ (0 : ℝ) := by
    intro y hy
    simpa [s] using
      (lmo_normal_nonneg (O := O)
        (C := C) (g := g) (y := y) hy)
  have hbound :
      (α / 2) * ‖g‖ * ‖x - s‖ ^ q ≤ (inner g (x - s) : ℝ) :=
    uniformlyConvex_support_lower_bound
      (C := C) (hUC := hUC) (v := s) (x := x) (η := g) hs hx hnormal
  simpa [s] using hbound

/-- In the small-gap regime `g ≤ L d²`, universal decrease already gives a
reciprocal increment lower bound of order `1 / d²`. -/
lemma reciprocalIncrement_small_gap_universal_lower_bound
    {F Fnext g d L : ℝ}
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hd_pos : 0 < d) (hL : 0 < L)
    (hgap : F ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : g ≤ L * d ^ 2) :
    1 / (2 * L * d ^ 2) ≤ Fnext⁻¹ - F⁻¹ := by
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
      (F := F) (Fnext := Fnext) (a := g ^ 2 / (2 * L * d ^ 2))
      hF_pos hFnext_pos (by positivity) hdec'
  have hsq : F ^ 2 ≤ g ^ 2 := by
    nlinarith
  have hfront0 :
      F ^ 2 / (2 * L * d ^ 2 * F ^ 2) ≤ g ^ 2 / (2 * L * d ^ 2 * F ^ 2) := by
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hEqL : F ^ 2 / (2 * L * d ^ 2 * F ^ 2) = 1 / (2 * L * d ^ 2) := by
    field_simp [hL.ne', hd_pos.ne', hF_pos.ne']
  have hEqR :
      g ^ 2 / (2 * L * d ^ 2 * F ^ 2) = (g ^ 2 / (2 * L * d ^ 2)) / F ^ 2 := by
    field_simp [hL.ne', hd_pos.ne', hF_pos.ne']
  rw [hEqL, hEqR] at hfront0
  exact le_trans hfront0 hinc

/-- In the small-gap regime `g ≤ L d²`, universal decrease together with a
power-type geometric lower bound yields an additional reciprocal increment
estimate. -/
lemma reciprocalIncrement_small_gap_uniform_lower_bound
    {F Fnext g d δ L A : ℝ} {q : ℝ}
    (_hq : 1 ≤ q)
    (hF_pos : 0 < F) (hFnext_pos : 0 < Fnext)
    (hδ_pos : 0 < δ) (hd_pos : 0 < d) (hL : 0 < L) (hA : 0 < A)
    (hgap : F ≤ g)
    (hgeom : A * (F / δ) * d ^ q ≤ g)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)))
    (hcase : g ≤ L * d ^ 2) :
    A ^ 2 * (d ^ 2) ^ (q - 1) / (2 * L * δ ^ 2) ≤ Fnext⁻¹ - F⁻¹ := by
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
      (F := F) (Fnext := Fnext) (a := g ^ 2 / (2 * L * d ^ 2))
      hF_pos hFnext_pos (by positivity) hdec'
  have hratio_mul :
      (A * d ^ q / δ) * F ≤ g := by
    have hEq : (A * (F / δ) * d ^ q) = (A * d ^ q / δ) * F := by
      field_simp [hδ_pos.ne']
    simpa [hEq] using hgeom
  have hratio : A * d ^ q / δ ≤ g / F := by
    exact (_root_.le_div_iff₀ hF_pos).2 hratio_mul
  have hratio_nonneg : 0 ≤ A * d ^ q / δ := by positivity
  have hratio_rhs_nonneg : 0 ≤ g / F := by positivity
  have hsq :
      (A * d ^ q / δ) ^ 2 ≤ (g / F) ^ 2 := by
    nlinarith [hratio, hratio_nonneg, hratio_rhs_nonneg]
  have hfront0 :
      ((A * d ^ q / δ) ^ 2) / (2 * L * d ^ 2) ≤ ((g / F) ^ 2) / (2 * L * d ^ 2) := by
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hEqL :
      ((A * d ^ q / δ) ^ 2) / (2 * L * d ^ 2) =
        A ^ 2 * (d ^ 2) ^ (q - 1) / (2 * L * δ ^ 2) := by
    -- With q : ℝ, use rpow arithmetic: (d^q)^2 = d^(2q) = (d^2)^q,
    -- and (d^2)^q = (d^2)^(q-1) * (d^2)^1 by rpow_add.
    have hd_nonneg : 0 ≤ d := le_of_lt hd_pos
    have hpow : (d ^ q) ^ 2 = (d ^ 2) ^ q := by
      rw [← Real.rpow_natCast (d ^ q) 2, ← Real.rpow_natCast d 2,
          ← Real.rpow_mul hd_nonneg, ← Real.rpow_mul hd_nonneg]
      ring_nf
    have hpow_succ : (d ^ 2) ^ q = (d ^ 2) ^ (q - 1) * (d ^ 2) ^ (1 : ℝ) := by
      rw [← Real.rpow_add (pow_pos hd_pos 2)]
      congr 1
      linarith
    calc
      ((A * d ^ q / δ) ^ 2) / (2 * L * d ^ 2)
          = A ^ 2 * (d ^ q) ^ 2 / (2 * L * δ ^ 2 * d ^ 2) := by
            field_simp [hA.ne', hL.ne', hd_pos.ne', hδ_pos.ne']
      _ = A ^ 2 * (d ^ 2) ^ q / (2 * L * δ ^ 2 * d ^ 2) := by rw [hpow]
      _ = A ^ 2 * ((d ^ 2) ^ (q - 1) * (d ^ 2) ^ (1 : ℝ)) / (2 * L * δ ^ 2 * d ^ 2) := by
            rw [hpow_succ]
      _ = A ^ 2 * (d ^ 2) ^ (q - 1) / (2 * L * δ ^ 2) := by
            have hd2_rpow : (d ^ 2) ^ (1 : ℝ) = d ^ 2 := Real.rpow_one _
            rw [hd2_rpow]
            field_simp [hA.ne', hL.ne', hd_pos.ne', hδ_pos.ne']
  have hEqR :
      ((g / F) ^ 2) / (2 * L * d ^ 2) = (g ^ 2 / (2 * L * d ^ 2)) / F ^ 2 := by
    field_simp [hL.ne', hd_pos.ne', hF_pos.ne']
  rw [hEqL, hEqR] at hfront0
  exact le_trans hfront0 hinc

/-- The paper's universal decrease estimate together with the uniformly-convex
power-type geometry forces the reciprocal gap increments to diverge. -/
theorem reciprocalIncrementDiverges_of_decrease_and_uniformGeometry
    {F g δ d : ℕ → ℝ} {L A : ℝ} {q : ℝ}
    (hq : 2 ≤ q)
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_pos : ∀ t, 0 < d t)
    (hL : 0 < L) (hA : 0 < A)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    (hgap : ∀ t, F t ≤ g t)
    (hsmooth : ∀ t, F t ≤ (L / 2) * (δ t) ^ 2)
    (hgeom : ∀ t, A * (F t / δ t) * (d t) ^ q ≤ g t)
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
    let k : ℝ := 1 / (2 * L * b)
    let ε : ℝ :=
      min 1
        (min (1 / (L * b))
          (A ^ 2 * k ^ (q - 1) / (2 * L * b)))
    have hk_pos : 0 < k := by
      dsimp [k]
      positivity
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply lt_min
      · norm_num
      · apply lt_min
        · positivity
        · positivity
    have hnear : ∀ᶠ t in atTop, δ t < ε := by
      exact hδ_zero.eventually (Iio_mem_nhds hε_pos)
    filter_upwards [hnear] with t ht
    have hδ_lt_one : δ t < 1 := by
      exact lt_of_lt_of_le ht (by dsimp [ε]; exact min_le_left _ _)
    have hδ_lt_large : δ t < 1 / (L * b) := by
      exact lt_of_lt_of_le ht (by dsimp [ε]; exact le_trans (min_le_right _ _) (min_le_left _ _))
    have hδ_lt_geom : δ t < A ^ 2 * k ^ (q - 1) / (2 * L * b) := by
      exact lt_of_lt_of_le ht (by dsimp [ε]; exact le_trans (min_le_right _ _) (min_le_right _ _))
    have hδ_sq_lt_large : (δ t) ^ 2 < 1 / (L * b) := by
      nlinarith [hδ_pos t, hδ_lt_one, hδ_lt_large]
    have hδ_sq_lt_geom :
        (δ t) ^ 2 < A ^ 2 * k ^ (q - 1) / (2 * L * b) := by
      nlinarith [hδ_pos t, hδ_lt_one, hδ_lt_geom]
    by_cases hcase : L * (d t) ^ 2 ≤ g t
    · have hfront : b ≤ 1 / (L * (δ t) ^ 2) := by
        have hden_pos : 0 < L * (δ t) ^ 2 := mul_pos hL (sq_pos_of_pos (hδ_pos t))
        have hmul : b * (L * (δ t) ^ 2) < 1 := by
          have hprod : (δ t) ^ 2 * (L * b) < 1 := by
            exact (_root_.lt_div_iff₀ (mul_pos hL hb_pos)).1 hδ_sq_lt_large
          nlinarith [hprod]
        exact le_of_lt ((_root_.lt_div_iff₀ hden_pos).2 hmul)
      exact le_trans hfront
        (reciprocalIncrement_large_gap_lower_bound
          (hF_pos t) (hF_pos (t + 1)) (hd_pos t) hL
          (hgap t) (hsmooth t) (hdec t) hcase)
    · have hcase' : g t ≤ L * (d t) ^ 2 := le_of_not_ge hcase
      by_cases hd_small : (d t) ^ 2 ≤ k
      · have hfront : b ≤ 1 / (2 * L * (d t) ^ 2) := by
          have hden_pos : 0 < 2 * L * (d t) ^ 2 := by
            exact mul_pos (by positivity) (sq_pos_of_pos (hd_pos t))
          have hd_small' : (d t) ^ 2 ≤ 1 / (2 * L * b) := by
            simpa [k] using hd_small
          have hmul : b * (2 * L * (d t) ^ 2) ≤ 1 := by
            have hprod : (d t) ^ 2 * (2 * L * b) ≤ 1 := by
              exact (_root_.le_div_iff₀ (mul_pos (by positivity : 0 < 2 * L) hb_pos)).1 hd_small'
            nlinarith [hprod]
          refine (_root_.le_div_iff₀ hden_pos).2 ?_
          exact hmul
        exact le_trans hfront
          (reciprocalIncrement_small_gap_universal_lower_bound
            (hF_pos t) (hF_pos (t + 1)) (hd_pos t) hL
            (hgap t) (hdec t) hcase')
      · have hk_le : k ≤ (d t) ^ 2 := le_of_not_ge hd_small
        have hpow :
            k ^ (q - 1) ≤ ((d t) ^ 2) ^ (q - 1) := by
          exact Real.rpow_le_rpow hk_pos.le hk_le (by linarith)
        have hfront0 :
            A ^ 2 * k ^ (q - 1) / (2 * L * (δ t) ^ 2) ≤
              A ^ 2 * ((d t) ^ 2) ^ (q - 1) / (2 * L * (δ t) ^ 2) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ A ^ 2))
            (by positivity)
        have hfront1 :
            b ≤ A ^ 2 * k ^ (q - 1) / (2 * L * (δ t) ^ 2) := by
          have hden_pos : 0 < 2 * L * (δ t) ^ 2 := by
            exact mul_pos (by positivity) (sq_pos_of_pos (hδ_pos t))
          have hmul : b * (2 * L * (δ t) ^ 2) < A ^ 2 * k ^ (q - 1) := by
            have hprod : (δ t) ^ 2 * (2 * L * b) < A ^ 2 * k ^ (q - 1) := by
              exact (_root_.lt_div_iff₀ (mul_pos (by positivity : 0 < 2 * L) hb_pos)).1
                hδ_sq_lt_geom
            nlinarith [hprod]
          exact le_of_lt ((_root_.lt_div_iff₀ hden_pos).2 hmul)
        exact le_trans hfront1 <|
          le_trans hfront0 <|
            reciprocalIncrement_small_gap_uniform_lower_bound
              (q := q) (show 1 ≤ q by linarith)
              (hF_pos t) (hF_pos (t + 1)) (hδ_pos t) (hd_pos t) hL hA
              (hgap t) (hgeom t) (hdec t) hcase'

/-- [FW-BOOST-UC-CORE] Universal decrease together with the power-type
uniformly-convex-set geometry forces a positive gap sequence to be `o(1/t)`. -/
theorem tendsto_mul_gap_of_decrease_and_uniformGeometry
    {F g δ d : ℕ → ℝ} {L A : ℝ} {q : ℝ}
    (hq : 2 ≤ q)
    (hF_pos : ∀ t, 0 < F t)
    (hδ_pos : ∀ t, 0 < δ t)
    (hd_pos : ∀ t, 0 < d t)
    (hL : 0 < L) (hA : 0 < A)
    (hδ_zero : Tendsto δ atTop (nhds 0))
    (hgap : ∀ t, F t ≤ g t)
    (hsmooth : ∀ t, F t ≤ (L / 2) * (δ t) ^ 2)
    (hgeom : ∀ t, A * (F t / δ t) * (d t) ^ q ≤ g t)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    Tendsto (fun t : ℕ => (t + 2 : ℝ) * F t) atTop (nhds 0) := by
  have hdiv :
      ReciprocalIncrementDiverges F :=
    reciprocalIncrementDiverges_of_decrease_and_uniformGeometry
      (hq := hq) hF_pos hδ_pos hd_pos hL hA hδ_zero hgap hsmooth hgeom hdec
  exact tendsto_mul_gap_of_increment_divergence (hF_pos := hF_pos) hdiv

/-- A one-step linear contraction iterates to a geometric bound. -/
theorem gap_le_geometric_of_linear_contraction
    {F : ℕ → ℝ} {ρ : ℝ}
    (hρ_nonneg : 0 ≤ ρ)
    (hstep : ∀ t, F (t + 1) ≤ ρ * F t) :
    ∀ t : ℕ, F t ≤ ρ ^ t * F 0 := by
  intro t
  induction t with
  | zero =>
      simp
  | succ t ih =>
      calc
        F (t + 1) ≤ ρ * F t := hstep t
        _ ≤ ρ * (ρ ^ t * F 0) := by
              exact mul_le_mul_of_nonneg_left ih hρ_nonneg
        _ = ρ ^ (t + 1) * F 0 := by
              rw [pow_succ]
              ring

/-- The Polyak nondegenerate `q = 2` branch yields a one-step linear
contraction with explicit factor. -/
lemma polyak_linear_step_contraction
    {F Fnext g d L A G : ℝ}
    (hF_nonneg : 0 ≤ F)
    (hL : 0 < L) (hA : 0 < A) (hG : 0 < G)
    (hgap : F ≤ g)
    (hgeom : A * G * d ^ 2 ≤ g)
    (hzero : d = 0 → g = 0)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2))) :
    let κ : ℝ := (1 / 2) * min 1 (A * G / L)
    Fnext ≤ (1 - κ) * F := by
  let κ : ℝ := (1 / 2) * min 1 (A * G / L)
  have hκ_nonneg : 0 ≤ κ := by
    dsimp [κ]
    positivity
  by_cases hd0 : d = 0
  · have hg0 : g = 0 := hzero hd0
    have hF0 : F = 0 := by
      apply le_antisymm
      · simpa [hg0] using hgap
      · exact hF_nonneg
    have hnext_nonpos : Fnext ≤ 0 := by
      simpa [hg0, hd0, hF0] using hdec
    simpa [κ, hF0] using hnext_nonpos
  · have hd2_pos : 0 < d ^ 2 := by
      exact sq_pos_iff.mpr hd0
    have hg_nonneg : 0 ≤ g := le_trans hF_nonneg hgap
    have hLd2_pos : 0 < L * d ^ 2 := mul_pos hL hd2_pos
    have hratio :
        A * G / L ≤ g / (L * d ^ 2) := by
      refine (_root_.le_div_iff₀ hLd2_pos).2 ?_
      calc
        (A * G / L) * (L * d ^ 2) = A * G * d ^ 2 := by
          field_simp [hL.ne']
          
        _ ≤ g := hgeom
    have hmin_le_g : g * min 1 (A * G / L) ≤ g := by
      calc
        g * min 1 (A * G / L) ≤ g * 1 := by
              exact mul_le_mul_of_nonneg_left (min_le_left _ _) hg_nonneg
        _ = g := by ring
    have hmin_le_quad :
        g * min 1 (A * G / L) ≤ g ^ 2 / (L * d ^ 2) := by
      have hfront :
          min 1 (A * G / L) ≤ g / (L * d ^ 2) := by
        exact le_trans (min_le_right _ _) hratio
      have hscaled :
          g * min 1 (A * G / L) ≤ g * (g / (L * d ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hfront hg_nonneg
      have hEq : g * (g / (L * d ^ 2)) = g ^ 2 / (L * d ^ 2) := by
        ring
      simpa [hEq] using hscaled
    have hmin_lower :
        g * min 1 (A * G / L) ≤ min g (g ^ 2 / (L * d ^ 2)) := by
      exact le_min hmin_le_g hmin_le_quad
    have hstep' :
        Fnext ≤ F - (1 / 2) * (g * min 1 (A * G / L)) := by
      exact hdec.trans <| by
        gcongr
    have hFg :
        (1 / 2) * (F * min 1 (A * G / L)) ≤
          (1 / 2) * (g * min 1 (A * G / L)) := by
      have hmin_nonneg : 0 ≤ min 1 (A * G / L) := by positivity
      gcongr
    calc
      Fnext ≤ F - (1 / 2) * (g * min 1 (A * G / L)) := hstep'
      _ ≤ F - (1 / 2) * (F * min 1 (A * G / L)) := by linarith
      _ = (1 - κ) * F := by
            dsimp [κ]
            ring

/-- An abstract `q = 2` Polyak step bound iterates to a geometric primal-gap
estimate. -/
theorem gap_le_geometric_of_polyak_linear_step
    {F g d : ℕ → ℝ} {L A G : ℝ}
    (hF_nonneg : ∀ t, 0 ≤ F t)
    (hL : 0 < L) (hA : 0 < A) (hG : 0 < G)
    (hgap : ∀ t, F t ≤ g t)
    (hgeom : ∀ t, A * G * (d t) ^ 2 ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    let κ : ℝ := (1 / 2) * min 1 (A * G / L)
    ∀ t : ℕ, F t ≤ (1 - κ) ^ t * F 0 := by
  let κ : ℝ := (1 / 2) * min 1 (A * G / L)
  have hρ_nonneg : 0 ≤ 1 - κ := by
    dsimp [κ]
    nlinarith [min_le_left 1 (A * G / L)]
  have hstep :
      ∀ t, F (t + 1) ≤ (1 - κ) * F t := by
    intro t
    simpa [κ] using
      (polyak_linear_step_contraction
        (F := F t) (Fnext := F (t + 1)) (g := g t) (d := d t)
        (L := L) (A := A) (G := G)
        (hF_nonneg := hF_nonneg t)
        hL hA hG (hgap t) (hgeom t) (hzero t) (hdec t))
  simpa [κ] using
    (gap_le_geometric_of_linear_contraction
      (F := F) (ρ := 1 - κ) hρ_nonneg hstep)

/-- Raising a one-step power descent relation to an exponent `β ∈ [0,1]`
produces a quadratic recursion for the transformed sequence. -/
lemma powerDescent_rpow_step
    {x y β η : ℝ}
    (hβ_nonneg : 0 ≤ β) (hβ_le_one : β ≤ 1)
    (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hx_nonneg : 0 ≤ x) (hx_le_one : x ≤ 1)
    (hy_nonneg : 0 ≤ y)
    (hstep : y ≤ x - η * x ^ (1 + β)) :
    y ^ β ≤ x ^ β - (β * η) * (x ^ β) ^ 2 := by
  by_cases hx0 : x = 0
  · have hy0 : y = 0 := by
      have hpow0 : (0 : ℝ) ^ (1 + β) = 0 := by
        exact Real.zero_rpow (by linarith [hβ_nonneg])
      have hy_le_zero : y ≤ 0 := by
        simpa [hx0, hpow0] using hstep
      exact le_antisymm hy_le_zero hy_nonneg
    by_cases hβ0 : β = 0
    · simp [hx0, hy0, hβ0]
    · have hβ_pos : 0 < β := lt_of_le_of_ne hβ_nonneg (by simpa [eq_comm] using hβ0)
      have hzeroβ : (0 : ℝ) ^ β = 0 := Real.zero_rpow hβ0
      simp [hx0, hy0, hβ0]
  · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (by simpa [eq_comm] using hx0)
    have hxbeta_nonneg : 0 ≤ x ^ β := Real.rpow_nonneg hx_nonneg β
    have hxbeta_le_one : x ^ β ≤ 1 := Real.rpow_le_one hx_nonneg hx_le_one hβ_nonneg
    have hu_nonneg : 0 ≤ η * x ^ β := mul_nonneg hη_nonneg hxbeta_nonneg
    have hu_le_one : η * x ^ β ≤ 1 := by
      calc
        η * x ^ β ≤ 1 * x ^ β := by
          gcongr
        _ = x ^ β := by ring
        _ ≤ 1 := hxbeta_le_one
    have hs : -1 ≤ -(η * x ^ β) := by linarith
    have hfactor_nonneg : 0 ≤ 1 - η * x ^ β := by linarith
    have hxpow :
        x - η * x ^ (1 + β) = x * (1 - η * x ^ β) := by
      have hEq : x ^ (1 + β) = x * x ^ β := by
        rw [show 1 + β = β + 1 by ring]
        rw [Real.rpow_add_of_nonneg hx_nonneg hβ_nonneg (by positivity), Real.rpow_one]
        ring
      rw [hEq]
      ring
    have hy_bound :
        y ^ β ≤ (x * (1 - η * x ^ β)) ^ β := by
      have hupper_nonneg : 0 ≤ x * (1 - η * x ^ β) := mul_nonneg hx_nonneg hfactor_nonneg
      rw [hxpow] at hstep
      exact Real.rpow_le_rpow hy_nonneg hstep hβ_nonneg
    have hmul :
        (x * (1 - η * x ^ β)) ^ β = x ^ β * (1 - η * x ^ β) ^ β := by
      rw [Real.mul_rpow hx_nonneg hfactor_nonneg]
    have hbern :
        (1 - η * x ^ β) ^ β ≤ 1 - β * (η * x ^ β) := by
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        (rpow_one_add_le_one_add_mul_self
          (s := -(η * x ^ β)) hs hβ_nonneg hβ_le_one)
    have hscaled :
        x ^ β * (1 - η * x ^ β) ^ β ≤ x ^ β * (1 - β * (η * x ^ β)) := by
      exact mul_le_mul_of_nonneg_left hbern hxbeta_nonneg
    calc
      y ^ β ≤ (x * (1 - η * x ^ β)) ^ β := hy_bound
      _ = x ^ β * (1 - η * x ^ β) ^ β := hmul
      _ ≤ x ^ β * (1 - β * (η * x ^ β)) := hscaled
      _ = x ^ β - (β * η) * (x ^ β) ^ 2 := by ring

/-- A shifted power-descent recursion yields a shifted polynomial bound with the
sharp exponent `1 / β`. -/
theorem shifted_power_bound_of_powerDescent
    {F : ℕ → ℝ} {β η : ℝ} {T : ℕ}
    (hβ_pos : 0 < β) (hβ_le_one : β ≤ 1)
    (hη_pos : 0 < η) (hη_le_one : η ≤ 1)
    (hF_nonneg : ∀ t, 0 ≤ F t)
    (hFT_le_one : F T ≤ 1)
    (hstep : ∀ t, T ≤ t → F (t + 1) ≤ F t - η * F t ^ (1 + β)) :
    ∀ n : ℕ,
      F (T + n) ≤
        ((max 1 (1 / (β * η))) ^ (1 / β)) / (n + 1 : ℝ) ^ (1 / β) := by
  let p : ℝ := 1 / β
  let c : ℝ := β * η
  let B : ℕ → ℝ := fun n => F (T + n) ^ β
  let K : ℝ := (max 1 (1 / c)) ^ p
  have hβ_nonneg : 0 ≤ β := hβ_pos.le
  have hc_pos : 0 < c := by
    dsimp [c]
    exact mul_pos hβ_pos hη_pos
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hsmall : ∀ n : ℕ, F (T + n) ≤ 1 := by
    intro n
    induction n with
    | zero =>
        simpa using hFT_le_one
    | succ n ih =>
        have hstepn :
            F (T + n + 1) ≤ F (T + n) - η * F (T + n) ^ (1 + β) := by
          simpa [Nat.add_assoc] using hstep (T + n) (Nat.le_add_right T n)
        have hterm_nonneg : 0 ≤ η * F (T + n) ^ (1 + β) := by
          exact mul_nonneg hη_pos.le (Real.rpow_nonneg (hF_nonneg (T + n)) _)
        have hmono : F (T + n + 1) ≤ F (T + n) := by
          linarith
        exact hmono.trans ih
  have hB_nonneg : ∀ n, 0 ≤ B n := by
    intro n
    dsimp [B]
    exact Real.rpow_nonneg (hF_nonneg (T + n)) β
  have hB0_le_one : B 0 ≤ 1 := by
    dsimp [B]
    simpa using Real.rpow_le_one (hF_nonneg T) hFT_le_one hβ_nonneg
  have hB_step :
      ∀ n, B (n + 1) ≤ B n - c * (B n) ^ 2 := by
    intro n
    dsimp [B, c]
    have hstepn :
        F (T + n + 1) ≤ F (T + n) - η * F (T + n) ^ (1 + β) := by
      simpa [Nat.add_assoc] using hstep (T + n) (Nat.le_add_right T n)
    have hscalar :=
      powerDescent_rpow_step
        hβ_nonneg hβ_le_one hη_pos.le hη_le_one
        (hF_nonneg (T + n)) (hsmall n) (hF_nonneg (T + n + 1)) hstepn
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc] using hscalar
  have hquad :=
    quadraticDescent_bound
      (B := B) (c := c) hc_nonneg hB_nonneg hB_step
  have hK_ge_B0 : B 0 ≤ max 1 (1 / c) := by
    exact le_trans hB0_le_one (le_max_left _ _)
  have hKc_ge_one : 1 ≤ max 1 (1 / c) * c := by
    have hInv : 1 / c ≤ max 1 (1 / c) := le_max_right _ _
    calc
      1 = (1 / c) * c := by
            field_simp [hc_pos.ne']
      _ ≤ max 1 (1 / c) * c := by
            gcongr
  have hB_linear :
      ∀ n : ℕ, B n ≤ max 1 (1 / c) / (n + 1 : ℝ) := by
    intro n
    have hquadn := hquad n
    have hden_left : 0 < 1 + c * n * B 0 := by
      have hB0_nonneg : 0 ≤ B 0 := hB_nonneg 0
      positivity
    have hden_right : 0 < (n + 1 : ℝ) := by
      positivity
    refine hquadn.trans ?_
    refine (_root_.div_le_div_iff₀ hden_left hden_right).2 ?_
    have hmul_nonneg : 0 ≤ (n : ℝ) * B 0 := by
      exact mul_nonneg (by positivity : 0 ≤ (n : ℝ)) (hB_nonneg 0)
    have hscaled :
        (n : ℝ) * B 0 ≤ (n : ℝ) * B 0 * (max 1 (1 / c) * c) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hKc_ge_one hmul_nonneg)
    nlinarith [hK_ge_B0, hscaled]
  intro n
  let m : ℕ := T + n
  have hEq : F m = (B n) ^ p := by
    dsimp [m, B]
    calc
      F (T + n) = F (T + n) ^ (β * p) := by
        have hβp : β * p = 1 := by
          dsimp [p]
          field_simp [hβ_pos.ne']
        rw [hβp, Real.rpow_one]
      _ = (F (T + n) ^ β) ^ p := by
            rw [Real.rpow_mul (hF_nonneg (T + n))]
      _ = (B n) ^ p := by
            rfl
  have hK_nonneg : 0 ≤ max 1 (1 / c) := by
    positivity
  have hmain : F m ≤ K / (n + 1 : ℝ) ^ p := by
    calc
      F m = (B n) ^ p := hEq
      _ ≤ (max 1 (1 / c) / (n + 1 : ℝ)) ^ p := by
            exact Real.rpow_le_rpow (hB_nonneg n) (hB_linear n) hp_pos.le
      _ = K / (n + 1 : ℝ) ^ p := by
            dsimp [K]
            rw [Real.div_rpow hK_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) p]
  simpa [m, p, c, K] using hmain

/-- If a sequence satisfies a standard `M / (t + 2)` bound and `M ≤ t`, then `F t ≤ 1`. -/
lemma F_le_one_of_std_and_ceil_le
    {F : ℕ → ℝ} {M : ℝ} {t : ℕ}
    (hstd : ∀ s, F s ≤ M / (s + 2 : ℝ))
    (hMt : M ≤ (t : ℝ)) :
    F t ≤ 1 := by
  refine (hstd t).trans ?_
  rw [div_le_one (by positivity)]
  linarith

/-- Variant of `shifted_power_bound_of_powerDescent` for sequences satisfying a
standard `M / (t + 2)` bound, with the warmup length derived from `⌈M⌉`. -/
lemma shifted_power_bound_of_powerDescent_from_ceil
    {F : ℕ → ℝ} {β η M : ℝ}
    (hβ_pos : 0 < β) (hβ_le_one : β ≤ 1)
    (hη_pos : 0 < η) (hη_le_one : η ≤ 1)
    (hF_nonneg : ∀ t, 0 ≤ F t)
    (hstd : ∀ t, F t ≤ M / (t + 2 : ℝ))
    (hstep : ∀ t, Nat.ceil M ≤ t → F (t + 1) ≤ F t - η * F t ^ (1 + β)) :
    ∀ n : ℕ,
      F (Nat.ceil M + n) ≤
        ((max 1 (1 / (β * η))) ^ (1 / β)) / (n + 1 : ℝ) ^ (1 / β) :=
  shifted_power_bound_of_powerDescent hβ_pos hβ_le_one hη_pos hη_le_one hF_nonneg
    (F_le_one_of_std_and_ceil_le hstd (Nat.le_ceil M)) hstep

/-- The Polyak nondegenerate `q > 2` branch yields a one-step power descent
once the gap is already at most `1`. -/
lemma polyak_power_step
    {F Fnext g d L A G : ℝ} {q : ℝ}
    (hq : 2 < q)
    (hF_nonneg : 0 ≤ F) (hF_le_one : F ≤ 1) (hd_nonneg : 0 ≤ d)
    (hL : 0 < L) (hA : 0 < A) (hG : 0 < G)
    (hgap : F ≤ g)
    (hgeom : A * G * d ^ q ≤ g)
    (hzero : d = 0 → g = 0)
    (hdec : Fnext ≤ F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2))) :
    let β : ℝ := (q - 2 : ℝ) / q
    let η : ℝ := (1 / 2) * min 1 ((A * G) ^ ((2 : ℝ) / q) / L)
    Fnext ≤ F - η * F ^ (1 + β) := by
  let β : ℝ := (q - 2 : ℝ) / q
  let c : ℝ := (A * G) ^ ((2 : ℝ) / q) / L
  let η : ℝ := (1 / 2) * min 1 c
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hβ_eq : β = 1 - (2 : ℝ) / q := by
    dsimp [β]
    field_simp [hq_ne]
  have hq_gt_two : (2 : ℝ) < q := by linarith
  have hfrac_lt_one : (2 : ℝ) / q < 1 := by
    refine (_root_.div_lt_iff₀ hq_pos).2 ?_
    linarith
  have hβ_nonneg : 0 ≤ β := by
    rw [hβ_eq]
    linarith [hfrac_lt_one]
  have hβ_pos : 0 < β := by
    rw [hβ_eq]
    linarith [hfrac_lt_one]
  have h1β_nonneg : 0 ≤ 1 + β := by
    linarith
  have h1_le_1β : (1 : ℝ) ≤ 1 + β := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  by_cases hd0 : d = 0
  · have hg0 : g = 0 := hzero hd0
    have hF0 : F = 0 := by
      apply le_antisymm
      · simpa [hg0] using hgap
      · exact hF_nonneg
    have hnext_nonpos : Fnext ≤ 0 := by
      simpa [hg0, hd0, hF0] using hdec
    have hpow0 : (0 : ℝ) ^ (1 + β) = 0 := by
      exact Real.zero_rpow (by linarith [hβ_pos])
    have hrhs : F - η * F ^ (1 + β) = 0 := by
      rw [hF0, hpow0]
      ring
    have hgoal : Fnext ≤ F - η * F ^ (1 + β) := by
      simpa [hrhs] using hnext_nonpos
    simpa [η, β, c] using hgoal
  ·
    have hd2_pos : 0 < d ^ 2 := sq_pos_iff.mpr hd0
    have hAG_pos : 0 < A * G := mul_pos hA hG
    have hg_nonneg : 0 ≤ g := le_trans hF_nonneg hgap
    have hexp_pos : 0 < (2 : ℝ) / q := by positivity
    have hpow_geom :
        ((A * G) * d ^ q : ℝ) ^ ((2 : ℝ) / q) ≤ g ^ ((2 : ℝ) / q) := by
      exact Real.rpow_le_rpow
        (mul_nonneg hAG_pos.le (by positivity)) hgeom hexp_pos.le
    have hdq : (d ^ q : ℝ) ^ ((2 : ℝ) / q) = d ^ 2 := by
      calc
        (d ^ q : ℝ) ^ ((2 : ℝ) / q) = d ^ (q * ((2 : ℝ) / q)) := by
          rw [Real.rpow_mul hd_nonneg]
        _ = d ^ (2 : ℝ) := by
              congr 1
              field_simp [hq_ne]
        _ = d ^ 2 := by simp
    have hleft :
        ((A * G) * d ^ q : ℝ) ^ ((2 : ℝ) / q) =
          (A * G) ^ ((2 : ℝ) / q) * d ^ 2 := by
      rw [Real.mul_rpow hAG_pos.le (by positivity : 0 ≤ d ^ q), hdq]
    have hpow_d :
        (A * G) ^ ((2 : ℝ) / q) * d ^ 2 ≤ g ^ ((2 : ℝ) / q) := by
      simpa [hleft] using hpow_geom
    have hratio_raw :
        (A * G) ^ ((2 : ℝ) / q) ≤ g ^ ((2 : ℝ) / q) / d ^ 2 := by
      refine (_root_.le_div_iff₀ hd2_pos).2 ?_
      simpa [mul_assoc, mul_left_comm, mul_comm] using hpow_d
    have hratio :
        c ≤ g ^ ((2 : ℝ) / q) / (L * d ^ 2) := by
      have hscaled :
          (A * G) ^ ((2 : ℝ) / q) * (1 / L) ≤
            (g ^ ((2 : ℝ) / q) / d ^ 2) * (1 / L) := by
        exact mul_le_mul_of_nonneg_right hratio_raw (by positivity : 0 ≤ (1 / L : ℝ))
      simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hpow_mono :
        c * F ^ (1 + β) ≤ c * g ^ (1 + β) := by
      have hFg :
          F ^ (1 + β) ≤ g ^ (1 + β) := by
        exact Real.rpow_le_rpow hF_nonneg hgap h1β_nonneg
      exact mul_le_mul_of_nonneg_left hFg hc_nonneg
    have hgexp :
        g ^ ((2 : ℝ) / q) * g ^ (1 + β) = g ^ 2 := by
      have hsum : ((2 : ℝ) / q) + (1 + β) = 2 := by
        dsimp [β]
        field_simp [hq_ne]
        ring
      calc
        g ^ ((2 : ℝ) / q) * g ^ (1 + β) = g ^ (((2 : ℝ) / q) + (1 + β)) := by
          rw [← Real.rpow_add_of_nonneg hg_nonneg hexp_pos.le h1β_nonneg]
        _ = g ^ (2 : ℝ) := by rw [hsum]
        _ = g ^ 2 := by simp
    have hquad_lower :
        c * g ^ (1 + β) ≤ g ^ 2 / (L * d ^ 2) := by
      have hscaled :
          c * g ^ (1 + β) ≤ (g ^ ((2 : ℝ) / q) / (L * d ^ 2)) * g ^ (1 + β) := by
        exact mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hg_nonneg _)
      have hEq :
          (g ^ ((2 : ℝ) / q) / (L * d ^ 2)) * g ^ (1 + β) =
            g ^ 2 / (L * d ^ 2) := by
        calc
          (g ^ ((2 : ℝ) / q) / (L * d ^ 2)) * g ^ (1 + β)
              = (g ^ ((2 : ℝ) / q) * g ^ (1 + β)) / (L * d ^ 2) := by ring
          _ = g ^ 2 / (L * d ^ 2) := by rw [hgexp]
      exact hscaled.trans_eq hEq
    have hmin_mon :
        min F (c * F ^ (1 + β)) ≤ min g (g ^ 2 / (L * d ^ 2)) := by
      exact min_le_min hgap (hpow_mono.trans hquad_lower)
    have hstep' :
        Fnext ≤ F - (1 / 2) * min F (c * F ^ (1 + β)) := by
      have hcmp :
          F - (1 / 2) * min g (g ^ 2 / (L * d ^ 2)) ≤
            F - (1 / 2) * min F (c * F ^ (1 + β)) := by
        nlinarith [hmin_mon]
      exact hdec.trans hcmp
    have hpow_le :
        F ^ (1 + β) ≤ F := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge'
          hF_nonneg hF_le_one (by positivity : 0 ≤ (1 : ℝ)) h1_le_1β)
    have hsmall_lower :
        min 1 c * F ^ (1 + β) ≤ min F (c * F ^ (1 + β)) := by
      refine le_min ?_ ?_
      · calc
          min 1 c * F ^ (1 + β) ≤ 1 * F ^ (1 + β) := by
                exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hF_nonneg _)
          _ = F ^ (1 + β) := by ring
          _ ≤ F := hpow_le
      · exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hF_nonneg _)
    calc
      Fnext ≤ F - (1 / 2) * min F (c * F ^ (1 + β)) := hstep'
      _ ≤ F - (1 / 2) * (min 1 c * F ^ (1 + β)) := by
            exact sub_le_sub_left
              (mul_le_mul_of_nonneg_left hsmall_lower (by positivity : 0 ≤ (1 / 2 : ℝ)))
              F
      _ = F - η * F ^ (1 + β) := by
            have hEq :
                (1 / 2 : ℝ) * (min 1 c * F ^ (1 + β)) = η * F ^ (1 + β) := by
              dsimp [η]
              ring
            rw [hEq]

/-- An abstract `q > 2` Polyak step bound yields a shifted polynomial-rate
estimate with exponent `q / (q - 2)`. -/
theorem gap_shifted_power_bound_of_polyak_uniformGeometry
    {F g d : ℕ → ℝ} {L A G M : ℝ} {q : ℝ}
    (hq : 2 < q)
    (hF_nonneg : ∀ t, 0 ≤ F t)
    (hstd : ∀ t, F t ≤ M / (t + 2 : ℝ))
    (hL : 0 < L) (hA : 0 < A) (hG : 0 < G)
    (hd_nonneg : ∀ t, 0 ≤ d t)
    (hgap : ∀ t, F t ≤ g t)
    (hgeom : ∀ t, A * G * (d t) ^ q ≤ g t)
    (hzero : ∀ t, d t = 0 → g t = 0)
    (hdec : ∀ t, F (t + 1) ≤ F t - (1 / 2) * min (g t) (g t ^ 2 / (L * (d t) ^ 2))) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, F (T + n) ≤ K / (n + 1 : ℝ) ^ (q / (q - 2 : ℝ)) := by
  let β : ℝ := (q - 2 : ℝ) / q
  let η : ℝ := (1 / 2) * min 1 ((A * G) ^ ((2 : ℝ) / q) / L)
  let p : ℝ := q / (q - 2 : ℝ)
  let T : ℕ := Nat.ceil M
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hβ_eq : β = 1 - (2 : ℝ) / q := by
    dsimp [β]
    field_simp [hq_ne]
  have hq_sub_pos : 0 < (q - 2 : ℝ) := by linarith
  have hq_sub_ne : (q - 2 : ℝ) ≠ 0 := hq_sub_pos.ne'
  have hfrac_lt_one : (2 : ℝ) / q < 1 := by
    refine (_root_.div_lt_iff₀ hq_pos).2 ?_
    linarith
  have hβ_pos : 0 < β := by
    rw [hβ_eq]
    linarith [hfrac_lt_one]
  have hβ_le_one : β ≤ 1 := by
    have hfrac_nonneg : 0 ≤ (2 : ℝ) / q := by positivity
    rw [hβ_eq]
    linarith
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_le_one : η ≤ 1 := by
    dsimp [η]
    nlinarith [min_le_left 1 ((A * G) ^ ((2 : ℝ) / q) / L)]
  have hstep_pow :
      ∀ t, T ≤ t → F (t + 1) ≤ F t - η * F t ^ (1 + β) := by
    intro t ht
    have hFt_le_one : F t ≤ 1 :=
      F_le_one_of_std_and_ceil_le hstd (le_trans (Nat.le_ceil M) (by exact_mod_cast ht))
    have hpow :=
      polyak_power_step
        (q := q) hq
        (F := F t) (Fnext := F (t + 1)) (g := g t) (d := d t)
        (L := L) (A := A) (G := G)
        (hF_nonneg := hF_nonneg t) (hF_le_one := hFt_le_one) (hd_nonneg := hd_nonneg t)
        hL hA hG (hgap t) (hgeom t) (hzero t) (hdec t)
    simpa [η, β] using hpow
  have hshift :=
    shifted_power_bound_of_powerDescent_from_ceil
      (F := F) (β := β) (η := η) (M := M)
      hβ_pos hβ_le_one hη_pos hη_le_one hF_nonneg hstd hstep_pow
  have hp_eq : (1 / β : ℝ) = p := by
    dsimp [β, p]
    field_simp [hq_ne, hq_sub_ne]
  refine ⟨T, (max 1 (1 / (β * η))) ^ (1 / β), ?_, ?_⟩
  · positivity
  · intro n
    simpa [p, hp_eq, β, η] using hshift n

/-- A quadratic curvature term minus a `q`-power correction is bounded by an
explicit `r`-free residual once `q > 2`. -/
lemma quadraticMinusPower_residual_bound
    {q : ℝ} (hq : 2 < q) {A B r : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hr : 0 ≤ r) :
    A * r ^ 2 - B * r ^ q ≤
      ((q - 2 : ℝ) / q) * A * (4 * A / (q * B)) ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
  by_cases hA0 : A = 0
  · have hBr_nonneg : 0 ≤ B * r ^ q := mul_nonneg hB.le (by positivity)
    simp [hA0, hBr_nonneg]
  let p : ℝ := q / 2
  let p' : ℝ := p / (p - 1)
  let lam : ℝ := 4 * A / (q * B)
  have hq_pos : 0 < q := by linarith
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hq_sub_pos : 0 < (q - 2 : ℝ) := by linarith
  have hq_sub_ne : (q - 2 : ℝ) ≠ 0 := hq_sub_pos.ne'
  have hp : 1 < p := by
    dsimp [p]
    linarith [hq_sub_pos]
  have hpq : p.HolderConjugate p' := by
    dsimp [p']
    exact Real.HolderConjugate.conjExponent hp
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    positivity
  have hyoung : (r ^ 2) * lam ≤ (r ^ 2) ^ p / p + lam ^ p' / p' := by
    exact Real.young_inequality_of_nonneg
      (a := r ^ 2) (b := lam) (by positivity) hlam_pos.le hpq
  have hscaled := mul_le_mul_of_nonneg_left hyoung (by positivity : 0 ≤ q * B / 4)
  have hrpow : (r ^ 2 : ℝ) ^ p = r ^ q := by
    calc
      (r ^ 2 : ℝ) ^ p = r ^ ((2 : ℝ) * p) := by
        simpa using (Real.rpow_mul hr (2 : ℝ) p).symm
      _ = r ^ q := by
        congr 1
        dsimp [p]
        ring
  have hp'_eq : p' = q / (q - 2 : ℝ) := by
    dsimp [p', p]
    field_simp [hq_ne]
  have hbeta : p' = 1 + (2 : ℝ) / (q - 2 : ℝ) := by
    rw [hp'_eq]
    field_simp [hq_ne, hq_sub_ne]
    nlinarith
  have hlam_expand : lam ^ p' = lam * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
    rw [hbeta]
    simpa [Real.one_rpow, mul_comm, mul_left_comm, mul_assoc] using
      (Real.rpow_add hlam_pos 1 ((2 : ℝ) / (q - 2 : ℝ)))
  have hcoeff_left : (q * B / 4) * lam = A := by
    dsimp [lam]
    field_simp [hB.ne', hq_ne]
  have hcoeff_right : (q * B / 4) / p = B / 2 := by
    dsimp [p]
    field_simp [hq_ne]
    norm_num
  have hcoeff_last : (q * B / 4) / p' * lam = ((q - 2 : ℝ) / q) * A := by
    dsimp [lam]
    rw [hp'_eq]
    field_simp [hB.ne', hq_ne, hq_sub_ne]
  have hmain :
      A * r ^ 2 ≤
        (B / 2) * r ^ q +
          ((q - 2 : ℝ) / q) * A * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
    calc
      A * r ^ 2 = ((q * B / 4) * lam) * r ^ 2 := by rw [hcoeff_left]
      _ = (q * B / 4) * (r ^ 2 * lam) := by ring
      _ ≤ (q * B / 4) * ((r ^ 2) ^ p / p + lam ^ p' / p') := hscaled
      _ =
          ((q * B / 4) / p) * (r ^ 2) ^ p +
            ((q * B / 4) / p') * lam ^ p' := by
              ring
      _ =
          (B / 2) * r ^ q +
            ((q * B / 4) / p') *
              (lam * lam ^ ((2 : ℝ) / (q - 2 : ℝ))) := by
                rw [hcoeff_right, hrpow, hlam_expand]
      _ =
          (B / 2) * r ^ q +
            (((q * B / 4) / p') * lam) *
              lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
                ring
      _ =
          (B / 2) * r ^ q +
            ((q - 2 : ℝ) / q) * A * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
              rw [hcoeff_last]
  have hrq_nonneg : 0 ≤ r ^ q := by positivity
  have hsub :
      A * r ^ 2 - B * r ^ q ≤
        (B / 2) * r ^ q +
          ((q - 2 : ℝ) / q) * A * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) -
            B * r ^ q := by
    linarith
  have htail :
      (B / 2) * r ^ q +
          ((q - 2 : ℝ) / q) * A * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) -
            B * r ^ q ≤
        ((q - 2 : ℝ) / q) * A * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
    nlinarith [hB.le, hrq_nonneg]
  exact le_trans hsub htail

/-- Abstract one-step gap kernel for the power-q (`q > 2`) geometry correction.
Given a geometry lower bound `A * ‖f' x‖ * r ^ q ≤ ⟨f'(x), x_star - s⟩`, the
Frank-Wolfe step satisfies the standard power-q tail bound with the `lam`-dependent
curvature term. -/
lemma frankWolfeStep_gap_bound_power_kernel
    {q : ℝ} (hq : 2 < q) {A : ℝ} (hA : 0 < A)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E}
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hγ_pos : 0 < γ)
    (hF_pos : 0 < f x - f x_star) (hδ_pos : 0 < ‖x - x_star‖)
    (h_corr : A * ‖f' x‖ * ‖x_star - LMO O (f' x)‖ ^ q ≤
                (inner (f' x) (x_star - LMO O (f' x)) : ℝ)) :
    let δ : ℝ := ‖x - x_star‖
    let lam : ℝ := 4 * (L : ℝ) * γ * δ / (q * A * (f x - f x_star))
    f (frankWolfeStep O f' x γ) - f x_star ≤
      (1 - γ) * (f x - f x_star) +
        (L : ℝ) * γ ^ 2 * δ ^ 2 +
        ((q - 2 : ℝ) / q) * (L : ℝ) * γ ^ 2 * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
  let s := LMO O (f' x)
  let d : ℝ := ‖s - x‖
  let r : ℝ := ‖x_star - s‖
  let δ : ℝ := ‖x - x_star‖
  let lam : ℝ := 4 * (L : ℝ) * γ * δ / (q * A * (f x - f x_star))
  have hlinear :
      f (frankWolfeStep O f' x γ) - f x_star ≤
        (1 - γ) * (f x - f x_star) -
          γ * (inner (f' x) (x_star - s) : ℝ) +
          (L / 2 : ℝ) * γ ^ 2 * d ^ 2 := by
    have hsmooth0 := hSmooth x (frankWolfeStep O f' x γ)
    have hsmooth' :
        f (frankWolfeStep O f' x γ) ≤
          f x + γ * inner (f' x) (s - x) + (L / 2 : ℝ) * γ ^ 2 * d ^ 2 := by
      simpa [frankWolfeStep, s, d, inner_smul_right, norm_smul, Real.norm_of_nonneg hγ.1, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsmooth0
    have hfirst :
        (inner (f' x) (x_star - x) : ℝ) ≤ f x_star - f x := by
      linarith [hConv x x_star]
    have hexpand :
        (inner (f' x) (s - x) : ℝ) =
          (inner (f' x) (x_star - x) : ℝ) -
            (inner (f' x) (x_star - s) : ℝ) := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      ring
    rw [hexpand] at hsmooth'
    have hscaled :
        γ * (inner (f' x) (x_star - x) : ℝ) ≤ γ * (f x_star - f x) := by
      exact mul_le_mul_of_nonneg_left hfirst hγ.1
    linarith
  have hucorr : A * ‖f' x‖ * r ^ q ≤ (inner (f' x) (x_star - s) : ℝ) := by
    simpa [s, r, norm_sub_rev] using h_corr
  have hdist :
      d ^ 2 ≤ 2 * δ ^ 2 + 2 * r ^ 2 := by
    have hdecomp : s - x = (s - x_star) + (x_star - x) := by
      abel
    have htri : d ≤ δ + r := by
      calc
        d = ‖s - x‖ := by rfl
        _ = ‖(s - x_star) + (x_star - x)‖ := by rw [hdecomp]
        _ ≤ ‖s - x_star‖ + ‖x_star - x‖ := norm_add_le _ _
        _ = δ + r := by simp [δ, r, norm_sub_rev, add_comm]
    have hsq : d ^ 2 ≤ (δ + r) ^ 2 := by
      have hd_nonneg : 0 ≤ d := by dsimp [d]; positivity
      have hδ_nonneg : 0 ≤ δ := by dsimp [δ]; positivity
      have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
      nlinarith [htri, hd_nonneg, hδ_nonneg, hr_nonneg]
    have hsum : (δ + r) ^ 2 ≤ 2 * δ ^ 2 + 2 * r ^ 2 := by
      nlinarith [sq_nonneg (δ - r)]
    exact le_trans hsq hsum
  have hcurv :
      (L / 2 : ℝ) * γ ^ 2 * d ^ 2 ≤
        (L : ℝ) * γ ^ 2 * δ ^ 2 + (L : ℝ) * γ ^ 2 * r ^ 2 := by
    have hbase :
        (L / 2 : ℝ) * γ ^ 2 * d ^ 2 ≤
          (L / 2 : ℝ) * γ ^ 2 * (2 * δ ^ 2 + 2 * r ^ 2) := by
      exact mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ (L / 2 : ℝ) * γ ^ 2)
    linarith
  have hgradbound : (f x - f x_star) / δ ≤ ‖f' x‖ := by
    have hgradbound_t :
        f x - f x_star ≤ ‖f' x‖ * ‖x - x_star‖ := by
      simpa using
        (primalGap_le_gradNorm_mul_dist
          (f := f) (f' := f') hConv (x := x) (x_star := x_star))
    exact (_root_.div_le_iff₀ hδ_pos).2 <| by simpa [δ] using hgradbound_t
  have hres_front :
      (L : ℝ) * γ ^ 2 * r ^ 2 - γ * A * ((f x - f x_star) / δ) * r ^ q ≤
        ((q - 2 : ℝ) / q) * (L : ℝ) * γ ^ 2 * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
    have hB_pos : 0 < γ * A * ((f x - f x_star) / δ) := by
      have hδdiv_pos : 0 < (f x - f x_star) / δ := by
        exact (_root_.div_pos hF_pos hδ_pos)
      have hA0_pos : 0 < A := hA
      have hfront_pos : 0 < γ * A := mul_pos hγ_pos hA0_pos
      exact mul_pos hfront_pos hδdiv_pos
    have hquad :=
      quadraticMinusPower_residual_bound
        (q := q) hq
        (A := (L : ℝ) * γ ^ 2)
        (B := γ * A * ((f x - f x_star) / δ))
        (r := r)
        (by positivity) hB_pos (by positivity)
    have hlam_eq :
        4 * ((L : ℝ) * γ ^ 2) / (q * (γ * A * ((f x - f x_star) / δ))) = lam := by
      dsimp [lam, δ]
      field_simp [hγ_pos.ne', hδ_pos.ne', hF_pos.ne',
        show q ≠ 0 by positivity,
        show (A : ℝ) ≠ 0 by linarith [hA]]

    have hquad' :
        (L : ℝ) * γ ^ 2 * r ^ 2 - γ * A * ((f x - f x_star) / δ) * r ^ q ≤
          ((q - 2 : ℝ) / q) * ((L : ℝ) * γ ^ 2) *
            (4 * ((L : ℝ) * γ ^ 2) / (q * (γ * A * ((f x - f x_star) / δ)))) ^
              ((2 : ℝ) / (q - 2 : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hquad
    rw [hlam_eq] at hquad'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hquad'
  have hres :
      (L : ℝ) * γ ^ 2 * r ^ 2 - γ * A * ‖f' x‖ * r ^ q ≤
        ((q - 2 : ℝ) / q) * (L : ℝ) * γ ^ 2 * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
    have hneg_compare :
        -γ * A * ‖f' x‖ * r ^ q ≤ -γ * A * ((f x - f x_star) / δ) * r ^ q := by
      have hfac_nonneg : 0 ≤ γ * A * r ^ q := by
        positivity
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (neg_le_neg <| mul_le_mul_of_nonneg_left hgradbound hfac_nonneg)
    linarith [hres_front]
  have hinner_scaled :
      -γ * (inner (f' x) (x_star - s) : ℝ) ≤ -γ * A * ‖f' x‖ * r ^ q := by
    have hscaled :
        γ * A * ‖f' x‖ * r ^ q ≤ γ * (inner (f' x) (x_star - s) : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hucorr hγ.1)
    linarith
  linarith [hlinear, hcurv, hres, hinner_scaled]

/-- One canonical Frank-Wolfe step on a `q`-uniformly convex set, with `q > 2`,
admits a refined gap recursion whose residual is expressed through the
dimensionless ratio `lam`. -/
lemma frankWolfeStep_gap_bound_with_uniformCorrection
    {α : ℝ} {q : ℝ} (hq : 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
    (f : E → ℝ) (f' : E → E) (L : NNReal)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x x_star : E} (hx_star : x_star ∈ C)
    {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hγ_pos : 0 < γ)
    (hF_pos : 0 < f x - f x_star) (hδ_pos : 0 < ‖x - x_star‖) :
    let δ : ℝ := ‖x - x_star‖
    let A0 : ℝ := α / 2
    let lam : ℝ := 4 * (L : ℝ) * γ * δ / (q * A0 * (f x - f x_star))
    f (frankWolfeStep O f' x γ) - f x_star ≤
      (1 - γ) * (f x - f x_star) +
        (L : ℝ) * γ ^ 2 * δ ^ 2 +
        ((q - 2 : ℝ) / q) * (L : ℝ) * γ ^ 2 * lam ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
  exact frankWolfeStep_gap_bound_power_kernel
    O hq (by linarith) f f' L hConv hSmooth hγ hγ_pos hF_pos hδ_pos
    (A := α / 2)
    (by simpa [norm_sub_rev] using
        uniformlyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hUC := hUC) (q := q) (g := f' x) (x := x_star) hx_star)

set_option maxHeartbeats 600000 in
/-- [FW-BOOST-UC-OL-SEQ] The canonical open-loop Frank-Wolfe sequence
`γ_t = 2/(t+2)` also satisfies the uniformly-convex boosted theorem once the
iterates approach a varying feasible minimizer sequence. -/
theorem frankWolfe_uc_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
  rcases hq with rfl | hq3
  · simpa using
      frankWolfe_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
        hC_convex
        (uniformlyConvexPower_two_implies_stronglyConvex (C := C) hα (hUC := hUC))
        f f' L hL hConv hSmooth x_star xStarSeq hxStarSeq hvalSeq hminSeq hx0 hδ_zero
  ·
    let xSeq : ℕ → E := frankWolfeSequence O f' x0
    let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
    let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
    let h : ℕ → ℝ := fun t => (t + 2 : ℝ) * F t
    let Dsq : ℝ := (Metric.diam C) ^ 2
    let M : ℝ := 2 * max (f x0 - f x_star) ((L : ℝ) * Dsq)
    let a : ℕ → ℝ := fun t => (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
    let c : ℕ → ℝ := fun t => (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
    let stdConst : ℕ → ℝ :=
      fun t => 2 * (L : ℝ) * Dsq * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2
    let betaExp : ℝ := 2 / (q - 2 : ℝ)
    let A0 : ℝ := α / 2
    have hA0_pos : 0 < A0 := by
      dsimp [A0]
      linarith
    have hq_pos : 0 < q := by linarith
    have hq_sub_pos : 0 < (q - 2 : ℝ) := by linarith
    have hbeta_nonneg : 0 ≤ betaExp := by
      dsimp [betaExp]
      positivity
    have hbeta_pos : 0 < betaExp := by
      dsimp [betaExp]
      positivity
    have hF_nonneg : ∀ t, 0 ≤ F t := by
      intro t
      have hgap_t :
          0 ≤ f (xSeq t) - f (xStarSeq t) := by
        exact
          primalGap_nonneg_of_isMinOn
            (C := C) (f := f)
            (frankWolfeSequence_mem
              (O := O)
              hC_convex f' hx0 t)
            (hminSeq t)
      simpa [F, hvalSeq t] using hgap_t
    have hstd_step :
        ∀ t,
          F (t + 1) ≤
            (1 - 2 / (t + 2 : ℝ)) * F t +
              ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
      intro t
      have href :
          f (frankWolfeStep O f'
                (xSeq t) (2 / (t + 2 : ℝ))) -
              f (xStarSeq t) ≤
            (1 - 2 / (t + 2 : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
              ((L : ℝ) / 2) * (2 / (t + 2 : ℝ)) ^ 2 * Dsq := by
        simpa [xSeq, Dsq] using
          (frankWolfeStep_gap_bound
            (O := O)
            (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
            (x := xSeq t) (x_star := xStarSeq t)
            (frankWolfeSequence_mem
              (O := O)
              hC_convex f' hx0 t)
            (hxStarSeq t)
            (γ := 2 / (t + 2 : ℝ))
            (standardStepSize_mem_Icc t))
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
      simpa [B, M, Dsq, F, xSeq, hvalSeq 0] using hfw
    have hbounded : ∀ t, h t ≤ M := by
      intro t
      calc
        h t = (t + 2 : ℝ) * F t := by rfl
        _ ≤ (t + 2 : ℝ) * (M / (t + 2 : ℝ)) := by
              gcongr
              exact hstd_bound t
        _ = M := by field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
    have hnonneg_h : ∀ t, 0 ≤ h t := by
      intro t
      dsimp [h]
      exact mul_nonneg (by positivity) (hF_nonneg t)
    apply boosted_convergence_kernel hnonneg_h
    intro ε hε
    let Csmall : ℝ := 16 * (L : ℝ) / (q * A0 * ε)
    let Rconst : ℝ := ((q - 2 : ℝ) / q) * (L : ℝ) * Csmall ^ betaExp
    let coeff : ℕ → ℝ :=
      fun t => 4 * (L : ℝ) * (δ t) ^ 2 + 4 * Rconst * (δ t) ^ betaExp
    have hε2 : 0 < ε / 2 := by linarith
    have hδsq_zero : Tendsto (fun t => (δ t) ^ 2) atTop (nhds 0) := by
      simpa using hδ_zero.pow 2
    have hδbeta_zero : Tendsto (fun t => (δ t) ^ betaExp) atTop (nhds 0) :=
      tendsto_rpow_const_zero hδ_zero hbeta_pos
    have hcoeff_zero : Tendsto coeff atTop (nhds 0) := by
      have hleft :
          Tendsto (fun t => 4 * (L : ℝ) * (δ t) ^ 2) atTop (nhds 0) := by
        simpa using hδsq_zero.const_mul (4 * (L : ℝ))
      have hright :
          Tendsto (fun t => 4 * Rconst * (δ t) ^ betaExp) atTop (nhds 0) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          hδbeta_zero.const_mul (4 * Rconst)
      simpa [coeff] using hleft.add hright
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
    have hcoeff_event : ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 := by
      exact hcoeff_zero.eventually (Iio_mem_nhds hε2)
    have hall :
        ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 ∧ stdConst t < ε / 2 := by
      filter_upwards [hcoeff_event, hstdconst_event] with t h1 h2
      exact ⟨h1, h2⟩
    rcases Filter.Eventually.exists_forall_of_atTop hall with ⟨T, hT⟩
    have hsmall_or_refined :
        ∀ t,
          h t ≤ ε / 2 ∨
            F (t + 1) ≤
              (1 - 2 / (t + 2 : ℝ)) * F t +
                (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                Rconst * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ betaExp := by
      intro t
      by_cases hFt0 : F t = 0
      · left
        have hnonneg : 0 ≤ ε / 2 := by linarith
        simpa [h, hFt0] using hnonneg
      · have hF_pos_t : 0 < F t := lt_of_le_of_ne (hF_nonneg t) (by simpa [eq_comm] using hFt0)
        have hδ_pos_t : 0 < δ t := by
          by_contra hδt
          have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
          have hxeq : xSeq t = xStarSeq t := by
            exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
          have : F t = 0 := by simp [F, hxeq, hvalSeq t]
          exact hFt0 this
        let γt : ℝ := 2 / (t + 2 : ℝ)
        let lamT : ℝ := 4 * (L : ℝ) * γt * δ t / (q * A0 * F t)
        have hγ_mem : γt ∈ Set.Icc (0 : ℝ) 1 := standardStepSize_mem_Icc t
        have hγ_pos : 0 < γt := by
          dsimp [γt]
          positivity
        by_cases hcase : lamT ≤ Csmall * δ t
        · right
          have hF_seq_pos : 0 < f (xSeq t) - f (xStarSeq t) := by
            simpa [F, hvalSeq t] using hF_pos_t
          have href :
              f (frankWolfeStep O f' (xSeq t) γt) - f (xStarSeq t) ≤
                (1 - γt) * (f (xSeq t) - f (xStarSeq t)) +
                  (L : ℝ) * γt ^ 2 * ‖xSeq t - xStarSeq t‖ ^ 2 +
                  ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                    lamT ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
            simpa [xSeq, γt, δ, F, A0, lamT, hvalSeq t] using
              (frankWolfeStep_gap_bound_with_uniformCorrection
                (O := O)
                (C := C) (hq := hq3) hα hUC
                f f' L hConv hSmooth
                (x := xSeq t) (x_star := xStarSeq t)
                (hxStarSeq t) hγ_mem hγ_pos hF_seq_pos hδ_pos_t)
          have hlam_pow :
              lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := by
            exact Real.rpow_le_rpow (by positivity) hcase hbeta_nonneg
          have hlam_pow' :
              lamT ^ betaExp ≤ Csmall ^ betaExp * (δ t) ^ betaExp := by
            calc
              lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := hlam_pow
              _ = Csmall ^ betaExp * (δ t) ^ betaExp := by
                    exact Real.mul_rpow (by positivity) (by positivity)
          have hres_le :
              ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp ≤
                Rconst * γt ^ 2 * (δ t) ^ betaExp := by
            calc
              ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp
                  ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                      (Csmall ^ betaExp * (δ t) ^ betaExp) := by
                        exact mul_le_mul_of_nonneg_left hlam_pow'
                          (by positivity :
                            0 ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2)
              _ = Rconst * γt ^ 2 * (δ t) ^ betaExp := by
                    dsimp [Rconst]
                    ring
          have href' :
              F (t + 1) ≤
                (1 - 2 / (t + 2 : ℝ)) * F t +
                  (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                  ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp := by
            simpa [F, xSeq, frankWolfeSequence, γt, δ, hvalSeq t, frankWolfeOpenLoopSequence, openLoopStepSize] using href
          linarith
        · left
          have hcase' : Csmall * δ t < lamT := lt_of_not_ge hcase
          have hlam_repr :
              lamT = (4 * (L : ℝ) * γt / (q * A0 * F t)) * δ t := by
            dsimp [lamT]
            field_simp [hF_pos_t.ne']
          rw [hlam_repr] at hcase'
          have hdiv :
              Csmall < 4 * (L : ℝ) * γt / (q * A0 * F t) := by
            exact lt_of_mul_lt_mul_right hcase' hδ_pos_t.le
          have hF_bound :
              F t < 4 * (L : ℝ) * γt / (q * A0 * Csmall) := by
            have hden_pos : 0 < q * A0 * Csmall := by
              dsimp [Csmall]
              positivity
            have hmul : F t * (q * A0 * Csmall) < 4 * (L : ℝ) * γt := by
              have hmul' : Csmall * (q * A0 * F t) < 4 * (L : ℝ) * γt := by
                exact (_root_.lt_div_iff₀ (show 0 < q * A0 * F t by positivity)).1 hdiv
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
            exact (_root_.lt_div_iff₀ hden_pos).2 hmul
          have hEq :
              4 * (L : ℝ) * γt / (q * A0 * Csmall) = ε / (2 * (t + 2 : ℝ)) := by
            dsimp [γt, Csmall, A0]
            field_simp [hε.ne', hA0_pos.ne', hq_pos.ne']
            ring
          have hh_small : h t < ε / 2 := by
            have htmp : F t < ε / (2 * (t + 2 : ℝ)) := by simpa [hEq] using hF_bound
            dsimp [h]
            have hmul := mul_lt_mul_of_pos_left htmp (by positivity : 0 < (t + 2 : ℝ))
            have hneq : (t + 2 : ℝ) ≠ 0 := by positivity
            have hcalc :
                (t + 2 : ℝ) * (ε / (2 * (t + 2 : ℝ))) = ε / 2 := by
              field_simp [hneq]
              
            simpa [hcalc] using hmul
          exact le_of_lt hh_small
    have hstable :
        ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε := by
      intro t ht hle
      rcases hT t ht with ⟨hcoeffT, hstdT⟩
      rcases hsmall_or_refined t with hleft | hright
      · have hstep : h (t + 1) ≤ a t * h t + stdConst t := by
          have hh_succ : h (t + 1) = (t + 3 : ℝ) * F (t + 1) := by
            change ((((t + 1 : ℕ) : ℝ) + 2) * F (t + 1) = (t + 3 : ℝ) * F (t + 1))
            have hcast : (((t + 1 : ℕ) : ℝ) + 2) = (t + 3 : ℝ) := by
              exact_mod_cast (show t + 1 + 2 = t + 3 by omega)
            rw [hcast]
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
        have ha_le_one : a t ≤ 1 := by
          simpa [a] using frankWolfe_openLoop_coeff_le_one t
        have hah : a t * h t ≤ h t := by
          simpa using mul_le_mul_of_nonneg_right ha_le_one (hnonneg_h t)
        have hlt : h (t + 1) < ε := by
          linarith
        exact le_of_lt hlt
      · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
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
                    (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                    Rconst * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
            _ = a t * h t + c t * coeff t := by
                  dsimp [a, h, c, coeff]
                  field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
                  ring
        have hc_nonneg : 0 ≤ c t := by
          dsimp [c]
          exact div_nonneg (by positivity) (by positivity)
        have hc_le : c t ≤ 1 - a t := by
          dsimp [c, a]
          have hnum : (t + 3 : ℝ) ≤ (t + 4 : ℝ) := by nlinarith
          have hfrac : (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 ≤ (t + 4 : ℝ) / (t + 2 : ℝ) ^ 2 := by
            exact (_root_.div_le_div_of_nonneg_right hnum (by positivity))
          have hEq : (t + 4 : ℝ) / (t + 2 : ℝ) ^ 2 = 1 - a t := by
            dsimp [a]
            field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
            ring
          simpa [hEq] using hfrac
        have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
        have hmain : h (t + 1) ≤ a t * ε + c t * (ε / 2) := by
          have ha_nonneg : 0 ≤ a t := by
            dsimp [a]
            positivity
          have hah : a t * h t ≤ a t * ε := by
            exact mul_le_mul_of_nonneg_left hle ha_nonneg
          calc
            h (t + 1) ≤ a t * h t + c t * coeff t := hstep
            _ ≤ a t * ε + c t * coeff t := by linarith [hah]
            _ ≤ a t * ε + c t * (ε / 2) := by linarith [hbeta_le]
        have hfinal : a t * ε + c t * (ε / 2) ≤ ε := by
          have hhalf : c t * (ε / 2) ≤ c t * ε := by
            exact mul_le_mul_of_nonneg_left (by linarith) hc_nonneg
          have hfull : c t * ε ≤ (1 - a t) * ε := by
            exact mul_le_mul_of_nonneg_right hc_le (le_of_lt hε)
          linarith
        exact le_trans hmain hfinal
    have habove_drop :
        ∀ N0 t, T ≤ N0 → N0 ≤ t → t ≤ 2 * N0 → ε < h t →
          h (t + 1) ≤ h t - ε / (4 * (N0 + 1 : ℝ)) := by
      intro N0 t hTN hN0 htN0 hgt
      rcases hT t (le_trans hTN hN0) with ⟨hcoeffT, _hstdT⟩
      rcases hsmall_or_refined t with hleft | hright
      · exfalso
        linarith
      · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
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
                    (L : ℝ) * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ 2 +
                    Rconst * (2 / (t + 2 : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
            _ = a t * h t + c t * coeff t := by
                  dsimp [a, h, c, coeff]
                  field_simp [show (t + 2 : ℝ) ≠ 0 by positivity]
                  ring
        have hc_nonneg : 0 ≤ c t := by
          dsimp [c]
          positivity
        have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
        have hdrop :
            h (t + 1) ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
          have hdrop_aux :
              a t * h t + c t * (ε / 2) ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
            calc
              a t * h t + c t * (ε / 2)
                  = (t : ℝ) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 * h t +
                      (ε / 2) * (t + 3 : ℝ) / (t + 2 : ℝ) ^ 2 := by
                        dsimp [a, c]
                        ring
              _ ≤ h t - ε / (2 * (t + 2 : ℝ)) := by
                    exact frankWolfe_openLoop_drop_bound t
                      (hε := le_of_lt hε) (hH := le_of_lt hgt)
          have hmain : h (t + 1) ≤ a t * h t + c t * (ε / 2) := by
            calc
              h (t + 1) ≤ a t * h t + c t * coeff t := hstep
              _ ≤ a t * h t + c t * (ε / 2) := by linarith [hbeta_le]
          exact le_trans hmain hdrop_aux
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

set_option maxHeartbeats 600000 in
/-- [FW-BOOST-UC-OL-SEQ-FAM] The open-loop Frank-Wolfe sequence
`γ_t = ell / (t + ell)` with `ell ≥ 2` satisfies the uniformly-convex boosted
theorem once the iterates approach a varying feasible minimizer sequence. -/
theorem frankWolfe_uc_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {α : ℝ} {q : ℝ} (hq : 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
        (fun t => ‖frankWolfeOpenLoopSequence O ell f' x0 t - xStarSeq t‖)
        atTop (nhds 0)) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  let xSeq : ℕ → E := frankWolfeOpenLoopSequence O ell f' x0
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let δ : ℕ → ℝ := fun t => ‖xSeq t - xStarSeq t‖
  let h : ℕ → ℝ := fun t => (t + ell : ℝ) * F t
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let M : ℝ := (ell : ℝ) * max (f x0 - f x_star) ((L : ℝ) * Dsq)
  let a : ℕ → ℝ := fun t => (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let c : ℕ → ℝ := fun t => (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let stdConst : ℕ → ℝ :=
    fun t => (((ell : ℝ) ^ 2) / 2) * (L : ℝ) * Dsq * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2
  let betaExp : ℝ := 2 / (q - 2 : ℝ)
  let A0 : ℝ := α / 2
  have hell1 : 1 ≤ ell := by omega
  have hell_pos : (0 : ℝ) < ell := by
    exact_mod_cast (show 0 < ell by omega)
  have hA0_pos : 0 < A0 := by
    dsimp [A0]
    linarith
  have hq_pos : 0 < q := by linarith
  have hq_sub_pos : 0 < (q - 2 : ℝ) := by linarith
  have hbeta_nonneg : 0 ≤ betaExp := by
    dsimp [betaExp]
    positivity
  have hbeta_pos : 0 < betaExp := by
    dsimp [betaExp]
    positivity
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    have hgap_t :
        0 ≤ f (xSeq t) - f (xStarSeq t) := by
      exact
        primalGap_nonneg_of_isMinOn
          (C := C) (f := f)
          (frankWolfeOpenLoopSequence_mem
            (O := O)
            hC_convex hell1 f' hx0 t)
          (hminSeq t)
    simpa [F, hvalSeq t] using hgap_t
  have hstd_step :
      ∀ t,
        F (t + 1) ≤
          (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
            ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq := by
    intro t
    have href :
        f (frankWolfeStep O f'
              (xSeq t) (openLoopStepSize ell t)) -
            f (xStarSeq t) ≤
          (1 - (ell : ℝ) / (t + ell : ℝ)) * (f (xSeq t) - f (xStarSeq t)) +
            ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq := by
      simpa [xSeq, Dsq, openLoopStepSize] using
        (frankWolfeStep_gap_bound
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth hConv
          (x := xSeq t) (x_star := xStarSeq t)
          (frankWolfeOpenLoopSequence_mem
            (O := O)
            hC_convex hell1 f' hx0 t)
          (hxStarSeq t)
          (γ := openLoopStepSize ell t)
          (openLoopStepSize_mem_Icc hell1 t))
    simpa [F, xSeq, frankWolfeOpenLoopSequence, hvalSeq t] using href
  have hstd_bound :
      ∀ t, F t ≤ M / (t + ell : ℝ) := by
    intro t
    let B : ℝ := max (f x0 - f (xStarSeq 0)) ((L : ℝ) * Dsq)
    have hB_nonneg : 0 ≤ B := by
      have hgap0_nonneg : 0 ≤ f x0 - f (xStarSeq 0) := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 (hminSeq 0)
      exact le_trans hgap0_nonneg (le_max_left _ _)
    have hfw :=
      open_loop_convergence_of_initialGap_le
        (O := O)
        (C := C) hC_convex (ell := ell) hell
        f f' L hSmooth hConv (hx_star := hxStarSeq 0) hx0
        hB_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [B, M, Dsq, F, xSeq, hvalSeq 0] using hfw
  have hbounded : ∀ t, h t ≤ M := by
    intro t
    calc
      h t = (t + ell : ℝ) * F t := by rfl
      _ ≤ (t + ell : ℝ) * (M / (t + ell : ℝ)) := by
            gcongr
            exact hstd_bound t
      _ = M := by
            have hneq : (t + ell : ℝ) ≠ 0 := by
              have hpos : (0 : ℝ) < t + ell := by
                exact_mod_cast (show 0 < t + ell by omega)
              exact ne_of_gt hpos
            field_simp [hneq]
  have hnonneg_h : ∀ t, 0 ≤ h t := by
    intro t
    dsimp [h]
    exact mul_nonneg (by positivity) (hF_nonneg t)
  apply boosted_convergence_kernel hnonneg_h
  intro ε hε
  let Csmall : ℝ := 8 * (ell : ℝ) * (L : ℝ) / (q * A0 * ε)
  let Rconst : ℝ := ((q - 2 : ℝ) / q) * (L : ℝ) * Csmall ^ betaExp
  let coeff : ℕ → ℝ :=
    fun t => ((ell : ℝ) ^ 2) * (L : ℝ) * (δ t) ^ 2 + ((ell : ℝ) ^ 2) * Rconst * (δ t) ^ betaExp
  have hε2 : 0 < ε / 2 := by linarith
  have hδsq_zero : Tendsto (fun t => (δ t) ^ 2) atTop (nhds 0) := by
    simpa using hδ_zero.pow 2
  have hδbeta_zero : Tendsto (fun t => (δ t) ^ betaExp) atTop (nhds 0) :=
    tendsto_rpow_const_zero hδ_zero hbeta_pos
  have hcoeff_zero : Tendsto coeff atTop (nhds 0) := by
    have hleft :
        Tendsto (fun t => ((ell : ℝ) ^ 2) * (L : ℝ) * (δ t) ^ 2) atTop (nhds 0) := by
      convert hδsq_zero.const_mul (((ell : ℝ) ^ 2) * (L : ℝ)) using 1
      · ext t
        ring_nf
    have hright :
        Tendsto (fun t => ((ell : ℝ) ^ 2) * Rconst * (δ t) ^ betaExp) atTop (nhds 0) := by
      convert hδbeta_zero.const_mul (((ell : ℝ) ^ 2) * Rconst) using 1
      · ext t
        ring_nf
    simpa [coeff] using hleft.add hright
  have hstdconst_zero : Tendsto (fun t : ℕ => (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) / (t + ell : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_add_atTop_nhds_zero_nat (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) ell
  have hstdconst_event : ∀ᶠ t : ℕ in atTop, stdConst t < ε / 2 := by
    have hmain := hstdconst_zero.eventually (Iio_mem_nhds hε2)
    filter_upwards [hmain] with t ht
    have hbound_t : stdConst t ≤ (((ell : ℝ) ^ 2) * (L : ℝ) * Dsq) / (t + ell : ℝ) := by
      have hB_nonneg : 0 ≤ (L : ℝ) * Dsq := by positivity
      simpa [stdConst, mul_assoc, mul_left_comm, mul_comm] using
        (openLoop_stdConst_bound hell1 (B := (L : ℝ) * Dsq) hB_nonneg t)
    exact lt_of_le_of_lt hbound_t ht
  have hcoeff_event : ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 := by
    exact hcoeff_zero.eventually (Iio_mem_nhds hε2)
  have hall :
      ∀ᶠ t : ℕ in atTop, coeff t < ε / 2 ∧ stdConst t < ε / 2 := by
    filter_upwards [hcoeff_event, hstdconst_event] with t h1 h2
    exact ⟨h1, h2⟩
  rcases Filter.Eventually.exists_forall_of_atTop hall with ⟨T, hT⟩
  have hsmall_or_refined :
      ∀ t,
        h t ≤ ε / 2 ∨
          F (t + 1) ≤
            (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
              (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
              Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp := by
    intro t
    by_cases hFt0 : F t = 0
    · left
      have hnonneg : 0 ≤ ε / 2 := by linarith
      simpa [h, hFt0] using hnonneg
    · have hF_pos_t : 0 < F t := lt_of_le_of_ne (hF_nonneg t) (by simpa [eq_comm] using hFt0)
      have hδ_pos_t : 0 < δ t := by
        by_contra hδt
        have hδ0 : δ t = 0 := le_antisymm (not_lt.mp hδt) (norm_nonneg _)
        have hxeq : xSeq t = xStarSeq t := by
          exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [δ] using hδ0))
        have : F t = 0 := by simp [F, hxeq, hvalSeq t]
        exact hFt0 this
      let γt : ℝ := openLoopStepSize ell t
      let lamT : ℝ := 4 * (L : ℝ) * γt * δ t / (q * A0 * F t)
      have hγ_mem : γt ∈ Set.Icc (0 : ℝ) 1 := openLoopStepSize_mem_Icc hell1 t
      have hγ_pos : 0 < γt := by
        dsimp [γt, openLoopStepSize]
        have hden : (0 : ℝ) < t + ell := by
          exact_mod_cast (show 0 < t + ell by omega)
        exact div_pos hell_pos hden
      by_cases hcase : lamT ≤ Csmall * δ t
      · right
        have hF_seq_pos : 0 < f (xSeq t) - f (xStarSeq t) := by
          simpa [F, hvalSeq t] using hF_pos_t
        have href :
            f (frankWolfeStep O f' (xSeq t) γt) - f (xStarSeq t) ≤
              (1 - γt) * (f (xSeq t) - f (xStarSeq t)) +
                (L : ℝ) * γt ^ 2 * ‖xSeq t - xStarSeq t‖ ^ 2 +
                ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                  lamT ^ ((2 : ℝ) / (q - 2 : ℝ)) := by
          simpa [xSeq, γt, δ, F, A0, lamT, hvalSeq t] using
            (frankWolfeStep_gap_bound_with_uniformCorrection
              (O := O)
              (C := C) (hq := hq) hα hUC
              f f' L hConv hSmooth
              (x := xSeq t) (x_star := xStarSeq t)
              (hxStarSeq t) hγ_mem hγ_pos hF_seq_pos hδ_pos_t)
        have hlam_pow :
            lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := by
          exact Real.rpow_le_rpow (by positivity) hcase hbeta_nonneg
        have hlam_pow' :
            lamT ^ betaExp ≤ Csmall ^ betaExp * (δ t) ^ betaExp := by
          calc
            lamT ^ betaExp ≤ (Csmall * δ t) ^ betaExp := hlam_pow
            _ = Csmall ^ betaExp * (δ t) ^ betaExp := by
                  exact Real.mul_rpow (by positivity) (by positivity)
        have hres_le :
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp ≤
              Rconst * γt ^ 2 * (δ t) ^ betaExp := by
          calc
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp
                ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 *
                    (Csmall ^ betaExp * (δ t) ^ betaExp) := by
                      exact mul_le_mul_of_nonneg_left hlam_pow'
                        (by positivity :
                          0 ≤ ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2)
            _ = Rconst * γt ^ 2 * (δ t) ^ betaExp := by
                  dsimp [Rconst]
                  ring
        have href' :
            F (t + 1) ≤
              (1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
                ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp := by
          simpa [F, xSeq, frankWolfeOpenLoopSequence, γt, openLoopStepSize, δ, hvalSeq t] using href
        have hres_le' :
            ((q - 2 : ℝ) / q) * (L : ℝ) * γt ^ 2 * lamT ^ betaExp ≤
              Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp := by
          simpa [γt, openLoopStepSize] using hres_le
        linarith
      · left
        have hcase' : Csmall * δ t < lamT := lt_of_not_ge hcase
        have hlam_repr :
            lamT = (4 * (L : ℝ) * γt / (q * A0 * F t)) * δ t := by
          dsimp [lamT]
          field_simp [hF_pos_t.ne']
        rw [hlam_repr] at hcase'
        have hdiv :
            Csmall < 4 * (L : ℝ) * γt / (q * A0 * F t) := by
          exact lt_of_mul_lt_mul_right hcase' hδ_pos_t.le
        have hF_bound :
            F t < 4 * (L : ℝ) * γt / (q * A0 * Csmall) := by
          have hden_pos : 0 < q * A0 * Csmall := by
            dsimp [Csmall]
            positivity
          have hmul : F t * (q * A0 * Csmall) < 4 * (L : ℝ) * γt := by
            have hmul' : Csmall * (q * A0 * F t) < 4 * (L : ℝ) * γt := by
              exact (_root_.lt_div_iff₀ (show 0 < q * A0 * F t by positivity)).1 hdiv
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
          exact (_root_.lt_div_iff₀ hden_pos).2 hmul
        have hEq :
            4 * (L : ℝ) * γt / (q * A0 * Csmall) = ε / (2 * (t + ell : ℝ)) := by
          dsimp [γt, Csmall, openLoopStepSize, A0]
          field_simp [hε.ne', hA0_pos.ne', hq_pos.ne', hell_pos.ne']
          ring
        have hh_small : h t < ε / 2 := by
          have htmp : F t < ε / (2 * (t + ell : ℝ)) := by simpa [hEq] using hF_bound
          dsimp [h]
          have hmul := mul_lt_mul_of_pos_left htmp (by positivity : 0 < (t + ell : ℝ))
          have hneq : (t + ell : ℝ) ≠ 0 := by
            have hpos : (0 : ℝ) < t + ell := by
              exact_mod_cast (show 0 < t + ell by omega)
            exact ne_of_gt hpos
          have hcalc :
              (t + ell : ℝ) * (ε / (2 * (t + ell : ℝ))) = ε / 2 := by
            field_simp [hneq]
            
          simpa [hcalc] using hmul
        exact le_of_lt hh_small
  have hstable :
      ∀ t ≥ T, h t ≤ ε → h (t + 1) ≤ ε := by
    intro t ht hle
    rcases hT t ht with ⟨hcoeffT, hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · have hstep : h (t + 1) ≤ a t * h t + stdConst t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left (hstd_step t) (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  ((L : ℝ) / 2) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * Dsq) := hmul
          _ = a t * h t + stdConst t := by
                simpa [a, h, stdConst, mul_assoc, mul_left_comm, mul_comm] using
                  (openLoop_scaled_standard_eq hell1 (F := F) (Dsq := Dsq) (L := (L : ℝ)) t)
      have ha_le_one : a t ≤ 1 := by
        simpa [a] using openLoop_coeff_le_one hell1 t
      have hah : a t * h t ≤ h t := by
        simpa using mul_le_mul_of_nonneg_right ha_le_one (hnonneg_h t)
      have hlt : h (t + 1) < ε := by
        linarith
      exact le_of_lt hlt
    · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
                  Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
          _ = a t * h t + c t * coeff t := by
                dsimp [a, h, c, coeff]
                have hneq : (t + ell : ℝ) ≠ 0 := by
                  have hpos : (0 : ℝ) < t + ell := by
                    exact_mod_cast (show 0 < t + ell by omega)
                  exact ne_of_gt hpos
                field_simp [hneq]
                ring
      have hc_nonneg : 0 ≤ c t := by
        dsimp [c]
        exact div_nonneg (by positivity) (by positivity)
      have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
      have hmain : h (t + 1) ≤ a t * ε + c t * (ε / 2) := by
        have ha_nonneg : 0 ≤ a t := by
          dsimp [a]
          positivity
        have hah : a t * h t ≤ a t * ε := by
          exact mul_le_mul_of_nonneg_left hle ha_nonneg
        calc
          h (t + 1) ≤ a t * h t + c t * coeff t := hstep
          _ ≤ a t * ε + c t * coeff t := by linarith [hah]
          _ ≤ a t * ε + c t * (ε / 2) := by linarith [hbeta_le]
      have hcoeff_le_one :
          a t + (1 / 2 : ℝ) * c t ≤ 1 := by
        have hcoeff_le_one' :
            (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 +
              (1 / 2 : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 ≤ 1 := by
          exact openLoop_refined_coeff_le_one hell t
        dsimp [a, c]
        (convert hcoeff_le_one' using 1; ring)
      have hfinal : a t * ε + c t * (ε / 2) ≤ ε := by
        have hscaled' : ε * (a t + (1 / 2 : ℝ) * c t) ≤ ε * 1 := by
          exact mul_le_mul_of_nonneg_left hcoeff_le_one (le_of_lt hε)
        have hscaled : ε * (a t + (1 / 2 : ℝ) * c t) ≤ ε := by
          simpa using hscaled'
        have hEq : a t * ε + c t * (ε / 2) = ε * (a t + (1 / 2 : ℝ) * c t) := by
          ring
        rw [hEq]
        exact hscaled
      exact le_trans hmain hfinal
  have habove_drop :
      ∀ N0 t, T ≤ N0 → N0 ≤ t → t ≤ 2 * N0 → ε < h t →
        h (t + 1) ≤ h t - ε / (4 * (N0 + ell : ℝ)) := by
    intro N0 t hTN hN0 htN0 hgt
    rcases hT t (le_trans hTN hN0) with ⟨hcoeffT, _hstdT⟩
    rcases hsmall_or_refined t with hleft | hright
    · exfalso
      linarith
    · have hstep : h (t + 1) ≤ a t * h t + c t * coeff t := by
        have hh_succ : h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := by
          change ((((t + 1 : ℕ) : ℝ) + ell) * F (t + 1) = (t + ell + 1 : ℝ) * F (t + 1))
          have hcast : (((t + 1 : ℕ) : ℝ) + ell) = (t + ell + 1 : ℝ) := by
            exact_mod_cast (show t + 1 + ell = t + ell + 1 by omega)
          rw [hcast]
        have hmul := mul_le_mul_of_nonneg_left hright (by positivity : 0 ≤ (t + ell + 1 : ℝ))
        calc
          h (t + 1) = (t + ell + 1 : ℝ) * F (t + 1) := hh_succ
          _ ≤ (t + ell + 1 : ℝ) *
                ((1 - (ell : ℝ) / (t + ell : ℝ)) * F t +
                  (L : ℝ) * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ 2 +
                  Rconst * ((ell : ℝ) / (t + ell : ℝ)) ^ 2 * (δ t) ^ betaExp) := hmul
          _ = a t * h t + c t * coeff t := by
                dsimp [a, h, c, coeff]
                have hneq : (t + ell : ℝ) ≠ 0 := by
                  have hpos : (0 : ℝ) < t + ell := by
                    exact_mod_cast (show 0 < t + ell by omega)
                  exact ne_of_gt hpos
                field_simp [hneq]
                ring
      have hc_nonneg : 0 ≤ c t := by
        dsimp [c]
        exact div_nonneg (by positivity) (by positivity)
      have hbeta_le : c t * coeff t ≤ c t * (ε / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hcoeffT) hc_nonneg
      have hdrop :
          h (t + 1) ≤ h t - ε / (2 * (t + ell : ℝ)) := by
        have hdrop_aux :
            a t * h t + c t * (ε / 2) ≤ h t - ε / (2 * (t + ell : ℝ)) := by
          calc
            a t * h t + c t * (ε / 2)
                = (t : ℝ) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 * h t +
                    (ε / 2) * (t + ell + 1 : ℝ) / (t + ell : ℝ) ^ 2 := by
                      dsimp [a, c]
                      ring
            _ ≤ h t - ε / (2 * (t + ell : ℝ)) := by
                  exact openLoop_drop_bound hell t
                    (heps := le_of_lt hε) (hH := le_of_lt hgt)
        have hmain : h (t + 1) ≤ a t * h t + c t * (ε / 2) := by
          calc
            h (t + 1) ≤ a t * h t + c t * coeff t := hstep
            _ ≤ a t * h t + c t * (ε / 2) := by linarith [hbeta_le]
        exact le_trans hmain hdrop_aux
      have hfrac :
          ε / (4 * (N0 + ell : ℝ)) ≤ ε / (2 * (t + ell : ℝ)) := by
        exact openLoop_blockFraction_bound hell1
          (heps := le_of_lt hε) htN0
      have hsub :
          h t - ε / (2 * (t + ell : ℝ)) ≤ h t - ε / (4 * (N0 + ell : ℝ)) := by
        linarith
      exact le_trans hdrop hsub
  refine ⟨T, M, ε / (4 * ell : ℝ), by exact div_pos hε (by positivity), hbounded T, hstable, ?_⟩
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
  have hablock :
      ∀ t, Nk ≤ t → t ≤ 2 * Nk → ε < h t := by
    intro t hlow hhigh
    have htn : t ≤ n := by rw [hNk_succ] at hkn; omega
    exact htail_above (le_trans hNk_ge hlow) htn hngt
  have hdrop :=
    block_drop_of_step_drop_openLoop (h := h) (N := Nk) hell1 (le_of_lt hε)
      (fun t hlow hhigh => by
        linarith [habove_drop Nk t hNk_ge hlow hhigh (hablock t hlow hhigh)])
  simpa [hNk_succ] using hdrop

/-- [FW-BOOST-UC-OL-SET-FAM] The open-loop Frank-Wolfe family
`γ_t = ell / (t + ell)` with `ell ≥ 2` satisfies the boosted `o(1/t)` theorem
under power-type uniform convexity for exponents `q > 2`, without a
uniqueness assumption, by comparing to a varying nearest minimizer sequence. -/
theorem frankWolfe_uc_openLoop_boosted_convergence_of_minimizer
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {α : ℝ} {q : ℝ} (hq : 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  have hell1 : 1 ≤ ell := by omega
  let xSeq : ℕ → E := frankWolfeOpenLoopSequence O ell f' x0
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
      frankWolfeOpenLoopSequence_mem
        (O := O)
        hC_convex hell1 f' hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    let B : ℝ := max (f x0 - f x_star) ((L : ℝ) * (Metric.diam C) ^ 2)
    have hB_nonneg : 0 ≤ B := by
      have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
      exact le_trans hgap0_nonneg (le_max_left _ _)
    have hnonneg : ∀ t, 0 ≤ F t := by
      intro t
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
    have hbound :
        ∀ t, F t ≤ ((ell : ℝ) * B) / (t + ell : ℝ) := by
      intro t
      simpa [F, xSeq, B] using
        (open_loop_convergence_of_initialGap_le
          (O := O)
          (C := C) hC_convex (ell := ell) hell
          f f' L hSmooth hConv hx_star hx0
          hB_nonneg (le_max_left _ _) (le_max_right _ _) t)
    exact squeeze_zero hnonneg hbound
      (tendsto_const_div_add_atTop_nhds_zero_nat ((ell : ℝ) * B) ell)
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
    frankWolfe_uc_openLoop_boosted_convergence_of_minimizerSequence_tendsto_zero
      (O := O)
      hC_convex hell hq hα hUC f f' L hL hConv hSmooth x_star pSeq hpSeq_mem hpSeq_val hpSeq_min
      hx0 hδ_zero

/-- Zero-gradient wrapper for the family open-loop uniformly-convex set
theorem. -/
theorem frankWolfe_uc_openLoop_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {ell : ℕ} (hell : 2 ≤ ell)
    {α : ℝ} {q : ℝ} (hq : 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    {x_star : E} (hx_star : x_star ∈ C) (hgrad : f' x_star = 0)
    {x0 : E} (hx0 : x0 ∈ C) :
    Tendsto
      (fun t : ℕ =>
        (t + ell : ℝ) *
          (f (frankWolfeOpenLoopSequence O ell f' x0 t) - f x_star))
      atTop (nhds 0) := by
  exact
    frankWolfe_uc_openLoop_boosted_convergence_of_minimizer
      (O := O)
      hC_convex hell hq hα hUC f f' L hL hConv hSmooth hx_star
      (fun y _hy =>
        by
          have hgap_nonneg :=
            primalGap_nonneg_of_zero_gradient
              (f := f) (f' := f') hConv
              (x := y) (x_star := x_star) hgrad
          linarith)
      hx0

/-- [FW-BOOST-UC-OL-SET] Canonical open-loop Frank-Wolfe also satisfies the
boosted `o(1/t)` theorem under power-type uniform convexity, without a
uniqueness assumption, by comparing to a varying nearest minimizer sequence. -/
theorem frankWolfe_uc_boosted_convergence_of_minimizer
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
    frankWolfe_uc_boosted_convergence_of_minimizerSequence_tendsto_zero
      (O := O)
      hC_convex hq hα hUC f f' L hL hConv hSmooth x_star pSeq hpSeq_mem hpSeq_val hpSeq_min hx0
      hδ_zero

/-- Backward-compatible wrapper for the older zero-gradient formulation of the
uniformly-convex open-loop set theorem. -/
theorem frankWolfe_uc_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : q = 2 ∨ 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
    frankWolfe_uc_boosted_convergence_of_minimizer
      (O := O)
      hC_convex hq hα hUC f f' L hL hConv hSmooth hx_star
      (fun y _hy =>
        by
          have hgap_nonneg :=
            primalGap_nonneg_of_zero_gradient
              (f := f) (f' := f') hConv
              (x := y) (x_star := x_star) hgrad
          linarith)
      hx0

/-- [FW-BOOST-UC-SS-SEQ] The abstract uniformly-convex boosted short-step proof
applies when the comparison minimizer may vary with `t`, provided every
comparison point has the same optimal value and zero gradient. -/
theorem globalShortStep_uc_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 ≤ q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
  have hgeom : ∀ t, (α / 2) * (F t / δ t) * (d t) ^ q ≤ g t := by
    intro t
    have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
      have hgradbound_t :
          f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
        simpa [xSeq] using
          (primalGap_le_gradNorm_mul_dist
            (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t))
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by simpa [F, δ, hvalSeq t] using hgradbound_t
    let coeff : ℝ := (α / 2) * (d t) ^ q
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
    have huc :
        (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (uniformlyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hUC := hUC) (q := q)
          (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
    have hscaled' :
        (α / 2) * (F t / δ t) * (d t) ^ q ≤
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' huc
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
    tendsto_mul_gap_of_decrease_and_uniformGeometry
      (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
      (hL := hL_real) (hA := by positivity) (hδ_zero := by simpa [δ, xSeq] using hδ_zero)
      (hgap := hgap) (hsmooth := hsmooth) (hgeom := hgeom) (hdec := hdec)
  simpa [F, xSeq] using hcore

/-- [FW-BOOST-UC-SS-SET] Global short-step Frank-Wolfe also satisfies the
boosted `o(1/t)` theorem under power-type uniform convexity, without a
uniqueness assumption, by comparing to a varying nearest minimizer sequence. -/
theorem globalShortStep_uc_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 ≤ q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
          (C := C) O.isCompact
          (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
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
      globalShortStep_uc_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
        hC_convex hq hα hUC f f' L hL hConv hSmooth x_star pSeq hpSeq_mem hpSeq_val hpSeq_grad hx0
        (by simpa [F, xSeq] using hgap_pos) hδ_zero

/-- [FW-BOOST-UC-LS-SEQ] Exact line-search Frank-Wolfe also satisfies the
uniformly-convex boosted theorem once the iterates approach a varying
zero-gradient minimizer sequence. -/
theorem exactLineSearch_uc_boosted_convergence_of_minimizerSequence_tendsto_zero
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 ≤ q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
  have hgeom : ∀ t, (α / 2) * (F t / δ t) * (d t) ^ q ≤ g t := by
    intro t
    have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
      have hgradbound_t :
          f (xSeq t) - f (xStarSeq t) ≤ ‖f' (xSeq t)‖ * ‖xSeq t - xStarSeq t‖ := by
        simpa [xSeq] using
          (primalGap_le_gradNorm_mul_dist
            (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := xStarSeq t))
      exact (_root_.div_le_iff₀ (hδ_pos t)).2 <| by simpa [F, δ, hvalSeq t] using hgradbound_t
    let coeff : ℝ := (α / 2) * (d t) ^ q
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
    have huc :
        (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (uniformlyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hUC := hUC) (q := q)
          (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
    have hscaled' :
        (α / 2) * (F t / δ t) * (d t) ^ q ≤
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' huc
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
    tendsto_mul_gap_of_decrease_and_uniformGeometry
      (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
      (hL := hL_real) (hA := by positivity) (hδ_zero := by simpa [δ, xSeq] using hδ_zero)
      (hgap := hgap) (hsmooth := hsmooth) (hgeom := hgeom) (hdec := hdec)
  simpa [F, xSeq] using hcore

/-- [FW-BOOST-UC-LS-SET] Exact line-search Frank-Wolfe also satisfies the
boosted `o(1/t)` theorem under power-type uniform convexity, without a
uniqueness assumption, by comparing to a varying nearest minimizer sequence. -/
theorem exactLineSearch_uc_boosted_convergence_of_zeroGradient_minimizer
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 ≤ q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
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
          (C := C) O.isCompact
          (f := f) (f' := f') (L := L) hConv hSmooth x_star xSeq hxSeq
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
      exactLineSearch_uc_boosted_convergence_of_minimizerSequence_tendsto_zero
        (O := O)
        hC_convex hq hα hUC f f' L hL hConv hSmooth x_star pSeq hpSeq_mem hpSeq_val hpSeq_grad hLS hx0
        (by simpa [F, xSeq] using hgap_pos) hδ_zero

/-- [FW-POLYAK-UC-SS] On a compact power-type uniformly convex set, the global
short-step rule satisfies the Polyak-type `o(1/t)` conclusion whenever the
gradient norm is bounded below on the whole feasible set. -/
theorem globalShortStep_uc_polyak_convergence
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 ≤ q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
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
  let δ : ℕ → ℝ := fun t => max (Real.sqrt (2 * F t / (L : ℝ))) (F t / G)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      globalShortStep_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' L hL hConv hSmooth hx_star hmin hx0
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    let y : E := xSeq t0
    have hy : y ∈ C := by
      simpa [y] using hxSeq t0
    have hyval : f y = f x_star := by
      exact sub_eq_zero.mp (by simpa [F, y] using ht0)
    have hymin : ∀ z ∈ C, f y ≤ f z := by
      intro z hz
      linarith [hmin z hz, hyval]
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
            _ = y := by
                  exact
                    globalShortStep_eq_self_of_isMinOn
                      (O := O)
                      (C := C) hC_convex f f' L hL hSmooth hy hymin
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
  · have hF_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hδ_pos : ∀ t, 0 < δ t := by
      intro t
      dsimp [δ]
      exact lt_max_of_lt_right (div_pos (hF_pos t) hG)
    have hd_pos : ∀ t, 0 < d t := by
      intro t
      have hgap_le : F t ≤ g t := by
        have hgap_le' :
            f (xSeq t) - f x_star ≤ g t := by
          simpa [g, xSeq, s] using
            primalGap_le_lmoGap
              (O := O)
              (C := C) (f := f) (f' := f') hConv
              (x := xSeq t) (x_star := x_star) hx_star
        simpa [F] using hgap_le'
      have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
      by_contra hdt
      have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
      have hsx : s t = xSeq t := by
        exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
      have : g t = 0 := by simp [g, hsx]
      exact hg_pos.ne' this
    have hδ_zero :
        Tendsto δ atTop (nhds 0) := by
      simpa [δ] using
        tendsto_polyakScale_zero (F := F) (L := (L : ℝ)) (G := G) hgap_zero
    have hgap : ∀ t, F t ≤ g t := by
      intro t
      have hgap_le' :
          f (xSeq t) - f x_star ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := x_star) hx_star
      simpa [F] using hgap_le'
    have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      intro t
      have hsqrt_nonneg : 0 ≤ 2 * F t / (L : ℝ) := by
        have hnum_nonneg : 0 ≤ 2 * F t := by
          exact mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (le_of_lt (hF_pos t))
        exact div_nonneg hnum_nonneg hL_real.le
      have hsqrt_le : Real.sqrt (2 * F t / (L : ℝ)) ≤ δ t := by
        dsimp [δ]
        exact le_max_left _ _
      have hsqrt_sq_le :
          (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 ≤ (δ t) ^ 2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
      have hrewrite : ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) = F t := by
        field_simp [hL_real.ne']
        
      calc
        F t = ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) := by rw [hrewrite]
        _ = ((L : ℝ) / 2) * (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 := by
              rw [Real.sq_sqrt hsqrt_nonneg]
        _ ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
              gcongr
    have hgeom : ∀ t, (α / 2) * (F t / δ t) * (d t) ^ q ≤ g t := by
      intro t
      have hgap_grad : F t / δ t ≤ G := by
        have hδ_ge : F t / G ≤ δ t := by
          dsimp [δ]
          exact le_max_right _ _
        have hprod : F t ≤ δ t * G := by
          exact (_root_.div_le_iff₀ hG).1 hδ_ge
        exact (_root_.div_le_iff₀ (hδ_pos t)).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hprod)
      have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
        exact le_trans hgap_grad (hgrad_lb (xSeq t) (hxSeq t))
      let coeff : ℝ := (α / 2) * (d t) ^ q
      have hcoeff_nonneg : 0 ≤ coeff := by
        dsimp [coeff]
        positivity
      have hscaled : coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
        exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
      have huc :
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
        simpa [g, d, xSeq, s, norm_sub_rev] using
          (uniformlyConvex_lmoGap_lower_bound
            (O := O)
            (C := C) (hUC := hUC) (q := q)
            (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
      have hscaled' :
          (α / 2) * (F t / δ t) * (d t) ^ q ≤
            (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q := by
        simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
      exact le_trans hscaled' huc
    have hdec :
        ∀ t,
          F (t + 1) ≤
            F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
      intro t
      have hstep :
          (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
            f (xSeq t) - f (xSeq (t + 1)) := by
        simpa [xSeq, s, g, d, globalShortStepSequence] using
          (globalShortStep_decrease
            (O := O)
            (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) (hxSeq t))
      linarith [hstep]
    have hcore :=
      tendsto_mul_gap_of_decrease_and_uniformGeometry
        (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
        (hL := hL_real) (hA := by positivity) (hδ_zero := hδ_zero)
        (hgap := hgap) (hsmooth := hsmooth) (hgeom := hgeom) (hdec := hdec)
    simpa [F, xSeq] using hcore

/-- [FW-POLYAK-UC-SS-LIN] In the Polyak regime on a power-type uniformly convex
set with `q = 2`, global short step satisfies an explicit geometric bound. -/
theorem globalShortStep_uc_polyak_linear_rate
    (hC_convex : Convex ℝ C)
    {α : ℝ} (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α 2)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    let κ : ℝ := (1 / 2) * min 1 (((α / 2) * G) / (L : ℝ))
    ∀ t : ℕ,
      f (globalShortStepSequence O f' L x0 t) - f x_star ≤
        (1 - κ) ^ t * (f x0 - f x_star) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f x_star ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    simpa [F] using hgap_le'
  have hgeom : ∀ t, (α / 2) * G * (d t) ^ 2 ≤ g t := by
    intro t
    let coeff : ℝ := (α / 2) * (d t) ^ 2
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * G ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left (hgrad_lb (xSeq t) (hxSeq t)) hcoeff_nonneg
    have huc :
        (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (uniformlyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hUC := hUC) (q := 2)
          (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
    have hscaled' :
        (α / 2) * G * (d t) ^ 2 ≤
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' huc
  have hzero : ∀ t, d t = 0 → g t = 0 := by
    intro t hd0
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    simp [g, hsx]
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, globalShortStepSequence] using
        (globalShortStep_decrease
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) (hxSeq t))
    linarith [hstep]
  have hcore :=
    gap_le_geometric_of_polyak_linear_step
      (F := F) (g := g) (d := d) (L := (L : ℝ)) (A := α / 2) (G := G)
      hF_nonneg hL_real (by positivity) hG hgap hgeom hzero hdec
  simpa [F, xSeq, globalShortStepSequence] using hcore

/-- [FW-POLYAK-UC-SS-POW] In the Polyak regime on a power-type uniformly convex
set with `q > 2`, global short step satisfies a shifted polynomial rate with
exponent `q / (q - 2)`. -/
theorem globalShortStep_uc_polyak_power_rate
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    {x0 : E} (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f (globalShortStepSequence O f' L x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ (q / (q - 2 : ℝ)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let xSeq : ℕ → E := globalShortStepSequence O f' L x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      globalShortStepSequence_mem
        (O := O)
        hC_convex f' L hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hBstd_nonneg : 0 ≤ Bstd := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hstd : ∀ t, F t ≤ (2 * Bstd) / (t + 2 : ℝ) := by
    intro t
    have hfw :=
      global_short_step_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' L hL hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [F, xSeq, Bstd, Dsq] using hfw
  have hd_nonneg : ∀ t, 0 ≤ d t := by
    intro t
    dsimp [d]
    positivity
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f x_star ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    simpa [F] using hgap_le'
  have hgeom : ∀ t, (α / 2) * G * (d t) ^ q ≤ g t := by
    intro t
    let coeff : ℝ := (α / 2) * (d t) ^ q
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * G ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left (hgrad_lb (xSeq t) (hxSeq t)) hcoeff_nonneg
    have huc :
        (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (uniformlyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hUC := hUC) (q := q)
          (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
    have hscaled' :
        (α / 2) * G * (d t) ^ q ≤
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' huc
  have hzero : ∀ t, d t = 0 → g t = 0 := by
    intro t hd0
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    simp [g, hsx]
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, globalShortStepSequence] using
        (globalShortStep_decrease
          (O := O)
          (C := C) (f := f) (f' := f') (L := L) hSmooth (x := xSeq t) (hxSeq t))
    linarith [hstep]
  have hcore :=
    gap_shifted_power_bound_of_polyak_uniformGeometry
      (F := F) (g := g) (d := d) (L := (L : ℝ)) (A := α / 2) (G := G) (M := 2 * Bstd)
      (q := q) hq hF_nonneg hstd hL_real (by positivity) hG
      hd_nonneg hgap hgeom hzero hdec
  simpa [F, xSeq] using hcore

/-- [FW-POLYAK-UC-LS] On a compact power-type uniformly convex set, exact line
search satisfies the same Polyak-type `o(1/t)` conclusion whenever the
gradient norm is bounded below on the whole feasible set. -/
theorem exactLineSearch_uc_polyak_convergence
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 ≤ q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C) :
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
  let δ : ℕ → ℝ := fun t => max (Real.sqrt (2 * F t / (L : ℝ))) (F t / G)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hgap_zero :
      Tendsto F atTop (nhds 0) := by
    simpa [F, xSeq] using
      exactLineSearch_gap_tendsto_zero_of_isMinOn
        (O := O)
        hC_convex f f' hLS L hConv hSmooth hx_star hmin hx0
  by_cases hzero : ∃ t, F t = 0
  · rcases hzero with ⟨t0, ht0⟩
    let y : E := xSeq t0
    have hyval : f y = f x_star := by
      exact sub_eq_zero.mp (by simpa [F, y] using ht0)
    have htail_val : ∀ n, f (xSeq (t0 + n)) = f x_star := by
      intro n
      induction n with
      | zero =>
          exact hyval
      | succ n ih =>
          have hmin_n : ∀ z ∈ C, f (xSeq (t0 + n)) ≤ f z := by
            intro z hz
            linarith [hmin z hz, ih]
          have hstep_val :
              f (xSeq (t0 + (n + 1))) = f (xSeq (t0 + n)) := by
            simpa [xSeq, exactLineSearchSequence, Nat.add_assoc] using
              (exactLineSearch_value_eq_of_isMinOn
                (O := O)
                (C := C) hC_convex (f := f) (f' := f') hLS
                (hx := hxSeq (t0 + n)) hmin_n)
          exact hstep_val.trans ih
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
  · have hF_pos : ∀ t, 0 < F t := by
      intro t
      have hnonneg : 0 ≤ F t := by
        exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
      have hne : F t ≠ 0 := fun ht => hzero ⟨t, ht⟩
      exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
    have hδ_pos : ∀ t, 0 < δ t := by
      intro t
      dsimp [δ]
      exact lt_max_of_lt_right (div_pos (hF_pos t) hG)
    have hd_pos : ∀ t, 0 < d t := by
      intro t
      have hgap_le : F t ≤ g t := by
        have hgap_le' :
            f (xSeq t) - f x_star ≤ g t := by
          simpa [g, xSeq, s] using
            primalGap_le_lmoGap
              (O := O)
              (C := C) (f := f) (f' := f') hConv
              (x := xSeq t) (x_star := x_star) hx_star
        simpa [F] using hgap_le'
      have hg_pos : 0 < g t := lt_of_lt_of_le (hF_pos t) hgap_le
      by_contra hdt
      have hd0 : d t = 0 := le_antisymm (not_lt.mp hdt) (norm_nonneg _)
      have hsx : s t = xSeq t := by
        exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
      have : g t = 0 := by simp [g, hsx]
      exact hg_pos.ne' this
    have hδ_zero :
        Tendsto δ atTop (nhds 0) := by
      simpa [δ] using
        tendsto_polyakScale_zero (F := F) (L := (L : ℝ)) (G := G) hgap_zero
    have hgap : ∀ t, F t ≤ g t := by
      intro t
      have hgap_le' :
          f (xSeq t) - f x_star ≤ g t := by
        simpa [g, xSeq, s] using
          primalGap_le_lmoGap
            (O := O)
            (C := C) (f := f) (f' := f') hConv
            (x := xSeq t) (x_star := x_star) hx_star
      simpa [F] using hgap_le'
    have hsmooth : ∀ t, F t ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
      intro t
      have hsqrt_nonneg : 0 ≤ 2 * F t / (L : ℝ) := by
        have hnum_nonneg : 0 ≤ 2 * F t := by
          exact mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (le_of_lt (hF_pos t))
        exact div_nonneg hnum_nonneg hL_real.le
      have hsqrt_le : Real.sqrt (2 * F t / (L : ℝ)) ≤ δ t := by
        dsimp [δ]
        exact le_max_left _ _
      have hsqrt_sq_le :
          (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 ≤ (δ t) ^ 2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
      have hrewrite : ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) = F t := by
        field_simp [hL_real.ne']
        
      calc
        F t = ((L : ℝ) / 2) * (2 * F t / (L : ℝ)) := by rw [hrewrite]
        _ = ((L : ℝ) / 2) * (Real.sqrt (2 * F t / (L : ℝ))) ^ 2 := by
              rw [Real.sq_sqrt hsqrt_nonneg]
        _ ≤ ((L : ℝ) / 2) * (δ t) ^ 2 := by
              gcongr
    have hgeom : ∀ t, (α / 2) * (F t / δ t) * (d t) ^ q ≤ g t := by
      intro t
      have hgap_grad : F t / δ t ≤ G := by
        have hδ_ge : F t / G ≤ δ t := by
          dsimp [δ]
          exact le_max_right _ _
        have hprod : F t ≤ δ t * G := by
          exact (_root_.div_le_iff₀ hG).1 hδ_ge
        exact (_root_.div_le_iff₀ (hδ_pos t)).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hprod)
      have hgradbound : F t / δ t ≤ ‖f' (xSeq t)‖ := by
        exact le_trans hgap_grad (hgrad_lb (xSeq t) (hxSeq t))
      let coeff : ℝ := (α / 2) * (d t) ^ q
      have hcoeff_nonneg : 0 ≤ coeff := by
        dsimp [coeff]
        positivity
      have hscaled : coeff * (F t / δ t) ≤ coeff * ‖f' (xSeq t)‖ := by
        exact mul_le_mul_of_nonneg_left hgradbound hcoeff_nonneg
      have huc :
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
        simpa [g, d, xSeq, s, norm_sub_rev] using
          (uniformlyConvex_lmoGap_lower_bound
            (O := O)
            (C := C) (hUC := hUC) (q := q)
            (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
      have hscaled' :
          (α / 2) * (F t / δ t) * (d t) ^ q ≤
            (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q := by
        simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
      exact le_trans hscaled' huc
    have hdec :
        ∀ t,
          F (t + 1) ≤
            F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
      intro t
      have hstep :
          (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
            f (xSeq t) - f (xSeq (t + 1)) := by
        simpa [xSeq, s, g, d, exactLineSearchSequence] using
          (exactLineSearch_decrease
            (O := O)
            (f := f) (f' := f') (L := L) hLS hSmooth (x := xSeq t) (hxSeq t))
      linarith [hstep]
    have hcore :=
      tendsto_mul_gap_of_decrease_and_uniformGeometry
        (hq := hq) (hF_pos := hF_pos) (hδ_pos := hδ_pos) (hd_pos := hd_pos)
        (hL := hL_real) (hA := by positivity) (hδ_zero := hδ_zero)
        (hgap := hgap) (hsmooth := hsmooth) (hgeom := hgeom) (hdec := hdec)
    simpa [F, xSeq] using hcore

/-- [FW-POLYAK-UC-LS-LIN] In the Polyak regime on a power-type uniformly convex
set with `q = 2`, exact line search satisfies an explicit geometric bound. -/
theorem exactLineSearch_uc_polyak_linear_rate
    (hC_convex : Convex ℝ C)
    {α : ℝ} (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α 2)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C) :
    let κ : ℝ := (1 / 2) * min 1 (((α / 2) * G) / (L : ℝ))
    ∀ t : ℕ,
      f
        (exactLineSearchSequence O f f'
          hLS
          x0 t) - f x_star ≤
        (1 - κ) ^ t * (f x0 - f x_star) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f x_star ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    simpa [F] using hgap_le'
  have hgeom : ∀ t, (α / 2) * G * (d t) ^ 2 ≤ g t := by
    intro t
    let coeff : ℝ := (α / 2) * (d t) ^ 2
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * G ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left (hgrad_lb (xSeq t) (hxSeq t)) hcoeff_nonneg
    have huc :
        (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (uniformlyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hUC := hUC) (q := 2)
          (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
    have hscaled' :
        (α / 2) * G * (d t) ^ 2 ≤
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ 2 := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' huc
  have hzero : ∀ t, d t = 0 → g t = 0 := by
    intro t hd0
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    simp [g, hsx]
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, exactLineSearchSequence] using
        (exactLineSearch_decrease
          (O := O)
          (f := f) (f' := f') (L := L) hLS hSmooth (x := xSeq t) (hxSeq t))
    linarith [hstep]
  have hcore :=
    gap_le_geometric_of_polyak_linear_step
      (F := F) (g := g) (d := d) (L := (L : ℝ)) (A := α / 2) (G := G)
      hF_nonneg hL_real (by positivity) hG hgap hgeom hzero hdec
  simpa [F, xSeq, exactLineSearchSequence] using hcore

/-- [FW-POLYAK-UC-LS-POW] In the Polyak regime on a power-type uniformly convex
set with `q > 2`, exact line search satisfies a shifted polynomial rate with
exponent `q / (q - 2)`. -/
theorem exactLineSearch_uc_polyak_power_rate
    (hC_convex : Convex ℝ C)
    {α : ℝ} {q : ℝ} (hq : 2 < q) (hα : 0 < α)
    (hUC : IsUniformlyConvexPower C α q)
    (f : E → ℝ) (f' : E → E) (L : NNReal) (hL : 0 < L)
    (hConv : IsFirstOrderConvex f f')
    (hSmooth : IsLipschitzSmoothUpperBound f L f')
    (G : ℝ) (hG : 0 < G)
    (hgrad_lb : ∀ x ∈ C, G ≤ ‖f' x‖)
    {x_star : E} (hx_star : x_star ∈ C)
    (hmin : ∀ y ∈ C, f x_star ≤ f y)
    (hLS : LineSearch O f f')
    {x0 : E} (hx0 : x0 ∈ C) :
    ∃ T : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ,
        f
          (exactLineSearchSequence O f f'
            hLS
            x0 (T + n)) - f x_star ≤
          K / (n + 1 : ℝ) ^ (q / (q - 2 : ℝ)) := by
  have hL_real : 0 < (L : ℝ) := NNReal.coe_pos.mpr hL
  let hfc : Continuous f := continuous_of_isFirstOrderConvex_isLipschitzSmoothUpperBound (f := f) (f' := f') (L := L) hConv hSmooth
  let xSeq : ℕ → E := exactLineSearchSequence O f f' hLS x0
  let s : ℕ → E := fun t => LMO O (f' (xSeq t))
  let F : ℕ → ℝ := fun t => f (xSeq t) - f x_star
  let g : ℕ → ℝ := fun t => inner (f' (xSeq t)) (xSeq t - s t)
  let d : ℕ → ℝ := fun t => ‖s t - xSeq t‖
  let Dsq : ℝ := (Metric.diam C) ^ 2
  let Bstd : ℝ := max (f x0 - f x_star) ((L : ℝ) * Dsq)
  have hxSeq : ∀ t, xSeq t ∈ C := by
    intro t
    simpa [xSeq] using
      exactLineSearchSequence_mem
        (O := O)
        hC_convex f f' hLS hx0 t
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact primalGap_nonneg_of_isMinOn (C := C) (f := f) (hxSeq t) hmin
  have hBstd_nonneg : 0 ≤ Bstd := by
    have hgap0_nonneg : 0 ≤ f x0 - f x_star := by
      exact primalGap_nonneg_of_isMinOn (C := C) (f := f) hx0 hmin
    exact le_trans hgap0_nonneg (le_max_left _ _)
  have hstd : ∀ t, F t ≤ (2 * Bstd) / (t + 2 : ℝ) := by
    intro t
    have hfw :=
      exact_line_search_convergence_of_initialGap_le
        (O := O)
        hC_convex f f' hLS L hSmooth hConv hx_star hx0
        (B := Bstd) hBstd_nonneg (le_max_left _ _) (le_max_right _ _) t
    simpa [F, xSeq, Bstd, Dsq] using hfw
  have hd_nonneg : ∀ t, 0 ≤ d t := by
    intro t
    dsimp [d]
    positivity
  have hgap : ∀ t, F t ≤ g t := by
    intro t
    have hgap_le' :
        f (xSeq t) - f x_star ≤ g t := by
      simpa [g, xSeq, s] using
        primalGap_le_lmoGap
          (O := O)
          (C := C) (f := f) (f' := f') hConv
          (x := xSeq t) (x_star := x_star) hx_star
    simpa [F] using hgap_le'
  have hgeom : ∀ t, (α / 2) * G * (d t) ^ q ≤ g t := by
    intro t
    let coeff : ℝ := (α / 2) * (d t) ^ q
    have hcoeff_nonneg : 0 ≤ coeff := by
      dsimp [coeff]
      positivity
    have hscaled : coeff * G ≤ coeff * ‖f' (xSeq t)‖ := by
      exact mul_le_mul_of_nonneg_left (hgrad_lb (xSeq t) (hxSeq t)) hcoeff_nonneg
    have huc :
        (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q ≤ g t := by
      simpa [g, d, xSeq, s, norm_sub_rev] using
        (uniformlyConvex_lmoGap_lower_bound
          (O := O)
          (C := C) (hUC := hUC) (q := q)
          (g := f' (xSeq t)) (x := xSeq t) (hx := hxSeq t))
    have hscaled' :
        (α / 2) * G * (d t) ^ q ≤
          (α / 2) * ‖f' (xSeq t)‖ * (d t) ^ q := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans hscaled' huc
  have hzero : ∀ t, d t = 0 → g t = 0 := by
    intro t hd0
    have hsx : s t = xSeq t := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [d] using hd0))
    simp [g, hsx]
  have hdec :
      ∀ t,
        F (t + 1) ≤
          F t - (1 / 2) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) := by
    intro t
    have hstep :
        (1 / 2 : ℝ) * min (g t) (g t ^ 2 / ((L : ℝ) * (d t) ^ 2)) ≤
          f (xSeq t) - f (xSeq (t + 1)) := by
      simpa [xSeq, s, g, d, exactLineSearchSequence] using
        (exactLineSearch_decrease
          (O := O)
          (f := f) (f' := f') (L := L) hLS hSmooth (x := xSeq t) (hxSeq t))
    linarith [hstep]
  have hcore :=
    gap_shifted_power_bound_of_polyak_uniformGeometry
      (F := F) (g := g) (d := d) (L := (L : ℝ)) (A := α / 2) (G := G) (M := 2 * Bstd)
      (q := q) hq hF_nonneg hstd hL_real (by positivity) hG
      hd_nonneg hgap hgeom hzero hdec
  simpa [F, xSeq] using hcore

end UniformlyConvexBoostedConvergence

end Lemmata.FrankWolfeLDS
