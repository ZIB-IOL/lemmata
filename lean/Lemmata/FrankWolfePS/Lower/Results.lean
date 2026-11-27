module

public import Lemmata.FrankWolfePS.Lower.Scaling
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

namespace Lemmata.FrankWolfePS
open MeasureTheory Finset
open scoped RealInnerProductSpace BigOperators Pointwise

section Quadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def quadratic (L : ℝ) (c z : E) := L / 2 * ‖z‖ ^ 2 + ⟪c, z⟫
def grad (L : ℝ) (c z : E) := L • z + c

theorem quadratic_derivative (L : ℝ) (c z : E) :
    HasFDerivAt (quadratic L c) (innerSL ℝ (grad L c z)) z := by
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (L / 2)).add
    (innerSL ℝ c).hasFDerivAt
  convert h using 1
  · ext v; simp [quadratic]
  · ext v; simp [grad, innerSL_apply_apply, two_smul]; ring

theorem quadratic_hessian (L : ℝ) (c z : E) :
    HasFDerivAt (grad L c) (L • ContinuousLinearMap.id ℝ E) z :=
  ((hasFDerivAt_id z).const_smul L).add_const c

theorem quadratic_taylor (L : ℝ) (c x y : E) :
    quadratic L c y = quadratic L c x + ⟪grad L c x, y - x⟫ + (L / 2) * ‖y - x‖ ^ 2 := by
  simp only [quadratic, grad, inner_add_left, inner_sub_right, real_inner_smul_left,
    norm_sub_sq_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm x y]
  ring

end Quadratic

variable {ι Ω : Type*} [Fintype ι]

theorem objective_as_quadratic (L r : ℝ) (z : Pt ι) :
    L * obj r z = quadratic L (embed (fun _ : ι => 0, 32 * L * r)) (embed z) := by
  have hn := EuclideanSpace.norm_sq_eq (embed z)
  rw [Fintype.sum_option] at hn
  simp [embed, Real.norm_eq_abs, sq_abs] at hn
  change ‖embed z‖ ^ 2 = z.2 ^ 2 + ∑ i, z.1 i ^ 2 at hn
  rw [quadratic, inner_embed, hn]
  simp [obj, sq, embed]
  ring

/-- The hard objective `L ‖z‖² / 2 + 32 L r z_vert` on the ambient space (`r = 1/β` is the
rounding radius). It is `L`-smooth and `L`-strongly convex, with Hessian `L Id`. -/
noncomputable def hardObjective (L r : ℝ) (z : Ambient ι) : ℝ :=
  quadratic L (embed (fun _ : ι => 0, 32 * L * r)) z

theorem hardObjective_coords (L r : ℝ) (z : Ambient ι) :
    hardObjective L r z = L * obj r (coords z) := by
  rw [objective_as_quadratic, embed_coords, hardObjective]

theorem hardObjective_continuous (L r : ℝ) : Continuous (hardObjective (ι := ι) L r) := by
  unfold hardObjective quadratic; fun_prop

omit [Fintype ι] in
theorem scalePt_cont (a : ℝ) : Continuous (scalePt (ι := ι) a) := by unfold scalePt; fun_prop

section
variable [LinearOrder ι]

omit [LinearOrder ι] in
theorem physical_body_compact_convex {a r : ℝ} (I : Finset ι) :
    IsCompact (physicalBody a r I) ∧ Convex ℝ (physicalBody a r I) := by
  obtain ⟨hc, hv⟩ := body_compact_convex I (r / a)
  exact ⟨hc.image (continuous_const_smul a), hv.smul a⟩

omit [LinearOrder ι] in
theorem physical_compact_points {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (I : Finset ι) :
    IsCompact {z : Pt ι | embed z ∈ physicalBody a r I} := by
  have eq : {z : Pt ι | embed z ∈ physicalBody a r I} =
      scalePt a '' {z | Feasible (r / a) I z} := by
    ext z
    rw [Set.mem_ofPred_eq, physical_feasible_iff ha hr]
    constructor
    · intro h; exact ⟨_, h, by simp [ha.ne']⟩
    · rintro ⟨w, hw, rfl⟩; simpa [ha.ne'] using hw
  rw [eq]; exact (feasible_compact I (div_pos hr ha)).image (scalePt_cont a)

omit [LinearOrder ι] in
theorem physicalOpt_eq_sInf (L a r : ℝ) (I : Finset ι) :
    physicalOpt L a r I = sInf (hardObjective L r '' physicalBody a r I) := by
  unfold physicalOpt
  congr 1
  ext v; constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨embed z, hz, by rw [hardObjective_coords, coords_embed]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨coords x, ?_, by rw [hardObjective_coords]⟩
    show embed (coords x) ∈ physicalBody a r I
    rwa [embed_coords]

variable [MeasurableSpace Ω]

omit [LinearOrder ι] in
theorem bad_measurable {a r L : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) (I : Finset ι)
    (z : Ω → Pt ι) (hz : Measurable z) : MeasurableSet {ω | physicalFailure L a r k I (z ω)} := by
  have hc := (physical_compact_points ha hr I).isClosed
  exact ((hc.measurableSet.preimage hz).compl).union (measurableSet_le measurable_const
    ((measurable_const.mul ((obj_continuous r).measurable.comp hz)).sub measurable_const))

omit [LinearOrder ι] in
/-- With measurable returns that are feasible on the body of `I`, a failure probability of at
least `p` gives expected gap at least `p L a² / (16 k)`. The gap is bounded on the compact body,
so it is integrable. -/
theorem expected_gap_of_fraction (k : ℕ) {L a r p : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {I : Finset ι} (hne : I.Nonempty)
    (z : Ω → Pt ι) (meas : Measurable z) (feas : ∀ ω, embed (z ω) ∈ physicalBody a r I)
    (hp : p ≤ μ.real {ω | physicalFailure L a r k I (z ω)}) :
    p * (L * a ^ 2 / (16 * (k : ℝ))) ≤ ∫ ω, L * obj r (z ω) - physicalOpt L a r I ∂μ := by
  classical
  let loss := fun y : Pt ι => L * obj r y - physicalOpt L a r I
  let e := {ω | physicalFailure L a r k I (z ω)}
  let b : ℝ := L * a ^ 2 / (16 * (k : ℝ))
  have he : MeasurableSet e := bad_measurable ha hr _ _ _ meas
  have h0 (ω : Ω) : 0 ≤ loss (z ω) := by
    have hz := (physical_feasible_iff ha hr I (z ω)).mp (feas ω)
    have H : optimum (r / a) I ≤ obj (r / a) (scalePt a⁻¹ (z ω)) :=
      csInf_le (objective_bddBelow (div_pos hr ha) I) ⟨_, hz, rfl⟩
    have eq := obj_scale a r ha (scalePt a⁻¹ (z ω))
    simp only [scale_scale, mul_inv_cancel₀ ha.ne', scale_one] at eq
    dsimp only [loss]
    rw [physicalOpt_eq hL ha hr hne, eq, ← mul_assoc]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left H (by positivity))
  have hl : Continuous loss := (continuous_const.mul (obj_continuous r)).sub continuous_const
  obtain ⟨M, hM⟩ := (physical_compact_points ha hr I).bddAbove_image hl.continuousOn
  have hInt : Integrable (fun ω => loss (z ω)) μ :=
    (integrable_const M).mono' ((hl.measurable.comp meas).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]; exact hM ⟨_, feas ω, rfl⟩))
  have major (ω : Ω) : e.indicator (fun _ => b) ω ≤ loss (z ω) := by
    by_cases h : ω ∈ e
    · rw [Set.indicator_of_mem h]
      exact (show physicalFailure L a r k I (z ω) from h).resolve_left (not_not.mpr (feas ω))
    · rw [Set.indicator_of_notMem h]; exact h0 ω
  have H := integral_mono ((integrable_const b).indicator he) hInt major
  rw [integral_indicator_const b he, smul_eq_mul] at H
  have hb : 0 ≤ b := by dsimp [b]; positivity
  exact (mul_le_mul_of_nonneg_right hp hb).trans H
end

theorem prescribed_parameters {β D L : ℝ} (hβ : 0 < β) (hD : 2 < β * D) (k : ℕ) :
    let r := 1 / β
    let a := (D - 2 / β) / Real.sqrt 2
    0 < r ∧ 0 < a ∧ 1 / r = β ∧ 2 * r + Real.sqrt 2 * a = D ∧
    L * a ^ 2 / (16 * (k : ℝ)) = L * (D - 2 / β) ^ 2 / (32 * (k : ℝ)) ∧
    L * a ^ 2 / (64 * (k : ℝ)) = L * (D - 2 / β) ^ 2 / (128 * (k : ℝ)) := by
  dsimp only
  have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hdiff : 0 < D - 2 / β := sub_pos.mpr ((div_lt_iff₀ hβ).mpr (by linarith))
  refine ⟨by positivity, div_pos hdiff h2, by field_simp, ?_, ?_, ?_⟩
  · field_simp; ring
  · rw [div_pow, hroot]; ring
  · rw [div_pow, hroot]; ring
end Lemmata.FrankWolfePS
