module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.MainLowerBound
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

/-!
# Positive rescaling

This module formalizes Lemma `lem:rescaling-paper`: set curvature, diameter,
first-order quadratic models, objective gaps, and linear minimizers under the
map `x ↦ α x`.
-/

open Set InnerProductSpace
local notation "inner" => inner ℝ

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Set divided by a positive spatial scale. -/
def scaledSet (S : Set E) (alpha : ℝ) : Set E := {x | alpha • x ∈ S}

lemma scaledSet_eq_image {S : Set E} {alpha : ℝ} (ha : alpha ≠ 0) :
    scaledSet S alpha = (fun x : E => alpha⁻¹ • x) '' S := by
  ext x
  constructor
  · intro hx
    refine ⟨alpha • x, hx, ?_⟩
    change alpha⁻¹ • (alpha • x) = x
    rw [← mul_smul, inv_mul_cancel₀ ha, one_smul]
  · rintro ⟨y, hy, rfl⟩
    change alpha • (alpha⁻¹ • y) ∈ S
    rw [← mul_smul, mul_inv_cancel₀ ha, one_smul]
    exact hy

/-- Exact diameter scaling under a positive scalar. -/
theorem diam_scaledSet {S : Set E} {alpha : ℝ}
    (ha : 0 < alpha) (hS : Bornology.IsBounded S) :
    Metric.diam (scaledSet S alpha) = Metric.diam S / alpha := by
  let Kinv : NNReal := NNReal.mk alpha⁻¹ (inv_nonneg.mpr ha.le)
  let K : NNReal := NNReal.mk alpha ha.le
  have hinvLip : LipschitzWith Kinv (fun x : E => alpha⁻¹ • x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    rfl
  have hLip : LipschitzWith K (fun x : E => alpha • x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos ha]
    rfl
  have hscaledEq := scaledSet_eq_image (S := S) ha.ne'
  have hupper0 := hinvLip.diam_image_le S hS
  have hupper : Metric.diam (scaledSet S alpha) ≤
      alpha⁻¹ * Metric.diam S := by
    rw [hscaledEq]
    simpa [Kinv] using hupper0
  have hscaledBdd : Bornology.IsBounded (scaledSet S alpha) := by
    rw [hscaledEq]
    exact hinvLip.isBounded_image hS
  have himage : (fun x : E => alpha • x) '' scaledSet S alpha = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨alpha⁻¹ • y, ?_, ?_⟩
      · change alpha • (alpha⁻¹ • y) ∈ S
        rw [← mul_smul, mul_inv_cancel₀ ha.ne', one_smul]
        exact hy
      · change alpha • (alpha⁻¹ • y) = y
        rw [← mul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hlower0 := hLip.diam_image_le (scaledSet S alpha) hscaledBdd
  rw [himage] at hlower0
  have hlower : Metric.diam S / alpha ≤ Metric.diam (scaledSet S alpha) := by
    apply (div_le_iff₀ ha).2
    simpa [K, mul_comm] using hlower0
  have hupper' : Metric.diam (scaledSet S alpha) ≤ Metric.diam S / alpha := by
    simpa [div_eq_inv_mul] using hupper
  exact le_antisymm hupper' hlower

/-- A paired first-order lower and upper quadratic model. -/
def HasQuadraticModel (f : E → ℝ) (grad : E → E) (mu L : ℝ) : Prop :=
  (∀ x y, f x + inner (grad x) (y - x) + (mu / 2) * ‖y - x‖ ^ 2 ≤ f y) ∧
  (∀ x y, f y ≤ f x + inner (grad x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)

/-- Objective and gradient after the paper's positive rescaling. -/
noncomputable def scaledObjective (f : E → ℝ) (L alpha : ℝ) (x : E) : ℝ :=
  (L / alpha ^ 2) * f (alpha • x)

noncomputable def scaledGradient (grad : E → E) (L alpha : ℝ) (x : E) : E :=
  (L / alpha) • grad (alpha • x)

/-- A base `(1,1)` quadratic model becomes an `(L,L)` model. -/
theorem hasQuadraticModel_scaled
    {f : E → ℝ} {grad : E → E} {L alpha : ℝ}
    (hmodel : HasQuadraticModel f grad 1 1)
    (hL : 0 < L) (ha : 0 < alpha) :
    HasQuadraticModel (scaledObjective f L alpha)
      (scaledGradient grad L alpha) L L := by
  constructor
  · intro x y
    have hbase := hmodel.1 (alpha • x) (alpha • y)
    have hscale : 0 < L / alpha ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hbase hscale.le
    unfold scaledObjective scaledGradient
    have hsub : alpha • y - alpha • x = alpha • (y - x) := by module
    calc
      L / alpha ^ 2 * f (alpha • x) +
          inner ((L / alpha) • grad (alpha • x)) (y - x) +
          L / 2 * ‖y - x‖ ^ 2 =
          (L / alpha ^ 2) *
            (f (alpha • x) + inner (grad (alpha • x))
              (alpha • y - alpha • x) +
              (1 / 2 : ℝ) * ‖alpha • y - alpha • x‖ ^ 2) := by
                rw [hsub, inner_smul_left, inner_smul_right, norm_smul,
                  Real.norm_eq_abs, abs_of_pos ha]
                simp only [starRingEnd_apply, star_trivial]
                field_simp [ha.ne']
      _ ≤ (L / alpha ^ 2) * f (alpha • y) := hscaled
  · intro x y
    have hbase := hmodel.2 (alpha • x) (alpha • y)
    have hscale : 0 < L / alpha ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hbase hscale.le
    unfold scaledObjective scaledGradient
    have hsub : alpha • y - alpha • x = alpha • (y - x) := by module
    calc
      (L / alpha ^ 2) * f (alpha • y) ≤
          (L / alpha ^ 2) *
            (f (alpha • x) + inner (grad (alpha • x))
              (alpha • y - alpha • x) +
              (1 / 2 : ℝ) * ‖alpha • y - alpha • x‖ ^ 2) := hscaled
      _ = L / alpha ^ 2 * f (alpha • x) +
          inner ((L / alpha) • grad (alpha • x)) (y - x) +
          L / 2 * ‖y - x‖ ^ 2 := by
                rw [hsub, inner_smul_left, inner_smul_right, norm_smul,
                  Real.norm_eq_abs, abs_of_pos ha]
                simp only [starRingEnd_apply, star_trivial]
                field_simp [ha.ne']

/-- Objective gaps scale by `L/alpha²`. -/
lemma scaledObjective_gap (f : E → ℝ) {L alpha : ℝ} (x xstar : E) :
    scaledObjective f L alpha x - scaledObjective f L alpha xstar =
      (L / alpha ^ 2) * (f (alpha • x) - f (alpha • xstar)) := by
  simp [scaledObjective]
  ring

/-- Predicate saying that `z` minimizes a linear functional over `S`. -/
def IsLinearMinimizer (S : Set E) (p z : E) : Prop :=
  z ∈ S ∧ ∀ y ∈ S, inner p z ≤ inner p y

/-- Linear minimizers correspond under positive spatial scaling. -/
theorem isLinearMinimizer_scaled {S : Set E} {p z : E} {alpha : ℝ}
    (ha : 0 < alpha) (hz : IsLinearMinimizer S p z) :
    IsLinearMinimizer (scaledSet S alpha) p (alpha⁻¹ • z) := by
  constructor
  · change alpha • (alpha⁻¹ • z) ∈ S
    rw [← mul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    exact hz.1
  · intro y hy
    have hmin := hz.2 (alpha • y) hy
    rw [inner_smul_right]
    have halpha : inner p y = alpha⁻¹ * inner p (alpha • y) := by
      rw [inner_smul_right]
      field_simp [ha.ne']
    rw [halpha]
    exact mul_le_mul_of_nonneg_left hmin (inv_nonneg.mpr ha.le)

/-- Paper-facing bundled rescaling endpoint. -/
theorem rescaling_bundle {S : Set E} {f : E → ℝ} {grad : E → E}
    {L alpha : ℝ}
    (ha : 0 < alpha) (hL : 0 < L)
    (hS : Bornology.IsBounded S)
    (hSC : IsStronglyConvexBall S 1)
    (hmodel : HasQuadraticModel f grad 1 1) :
    IsStronglyConvexBall (scaledSet S alpha) alpha ∧
    Metric.diam (scaledSet S alpha) = Metric.diam S / alpha ∧
    HasQuadraticModel (scaledObjective f L alpha)
      (scaledGradient grad L alpha) L L := by
  refine ⟨?_, diam_scaledSet ha hS, hasQuadraticModel_scaled hmodel hL ha⟩
  simpa [scaledSet] using hSC.preimage_smul ha

end Lemmata.DistributionalLowerBounds.Core.Distributional
