module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.UnconditionalController
public import Lemmata.DistributionalLowerBounds.Core.Distributional.ControllerTransport
public import Lemmata.DistributionalLowerBounds.Core.Distributional.Scaling

@[expose] public section

/-!
# Actual positive-rescaling simulation and the general fixed-budget bound

Directions are unchanged; objective points are multiplied by alpha. Returned
values, gradients, and atoms are multiplied by L/alpha², L/alpha, and 1/alpha.
The simulated base controller outputs alpha times the original output.
-/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory

noncomputable def scaleQuery {d : ℕ} (alpha : ℝ) (q : PairedQuery d) : PairedQuery d :=
  (alpha • q.1, q.2)

noncomputable def scaleAnswer {d : ℕ} (L alpha : ℝ) (a : PairedAnswer d) : PairedAnswer d :=
  (L/alpha^2*a.1, (L/alpha) • a.2.1, alpha⁻¹ • a.2.2)

noncomputable def scaledConcreteOracle (d : ℕ) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) (q : PairedQuery d) : PairedAnswer d :=
  scaleAnswer L alpha (concreteOracle d rho π (scaleQuery alpha q))

noncomputable def scaledFamilyLoss (d : ℕ) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) (x : Fin d → ℝ) : ℝ :=
  (L/alpha^2)*hardFamilyLoss d rho π (alpha • x)

lemma scaleQuery_measurable (d : ℕ) (alpha : ℝ) :
    Measurable (scaleQuery (d := d) alpha) := by unfold scaleQuery; fun_prop

lemma scaleAnswer_measurable (d : ℕ) (L alpha : ℝ) :
    Measurable (scaleAnswer (d := d) L alpha) := by unfold scaleAnswer; fun_prop

lemma scaledConcreteOracle_measurable (d : ℕ) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) : Measurable (scaledConcreteOracle d rho L alpha π) :=
  (scaleAnswer_measurable d L alpha).comp
    ((concreteOracle_measurable d rho π).comp (scaleQuery_measurable d alpha))

lemma scaledFamilyLoss_measurable (d : ℕ) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) : Measurable (scaledFamilyLoss d rho L alpha π) := by
  unfold scaledFamilyLoss hardFamilyLoss
  have h := (continuous_coordinateObjective d (objectiveCenter rho (hardTopWeight d))).measurable
  exact measurable_const.mul ((h.comp (by fun_prop)).sub measurable_const)

/-- Pointwise feasibility is stated in the original scaled set, not as an
additional transport certificate. -/
def ScaledFeasible {d : ℕ} (alpha : ℝ) (π : Equiv.Perm (Fin d)) (x : Fin d → ℝ) : Prop :=
  coordinateEnergy (permutedHardWeight d π) (alpha • x) ≤ hardC d^2

lemma scaledFeasible_zero {d : ℕ} (alpha : ℝ) (π : Equiv.Perm (Fin d)) :
    ScaledFeasible alpha π 0 := by
  simp only [ScaledFeasible, smul_zero, coordinateEnergy, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, abs_zero, add_zero, Finset.sum_const_zero]
  positivity

noncomputable def baseSimulation {d : ℕ}
    (s : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) (Fin d → ℝ))
    (L alpha : ℝ) := s.transport (scaleQuery alpha) (scaleAnswer L alpha) (fun x => alpha • x)

lemma baseSimulation_run {d : ℕ}
    (s : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) (Fin d → ℝ))
    (rho L alpha : ℝ) (π : Equiv.Perm (Fin d)) (T : ℕ) :
    (baseSimulation s L alpha).run (concreteOracle d rho) π T =
      alpha • s.run (scaledConcreteOracle d rho L alpha) π T :=
  s.transport_run _ _ _ _ _ _

lemma baseSimulation_measurable {Seed : Type} [MeasurableSpace Seed] {d T : ℕ}
    {s : Seed → DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) (Fin d → ℝ)}
    (hs : MeasurableStrategy s T) (L alpha : ℝ) :
    MeasurableStrategy (fun seed => baseSimulation (s seed) L alpha) T :=
  hs.transport _ _ _ (scaleQuery_measurable d alpha) (scaleAnswer_measurable d L alpha)
    (by fun_prop)

noncomputable def scaledThreshold (T : ℕ) (L alpha : ℝ) : ℝ :=
  (L/alpha^2)*(hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2))

theorem scaled_controller_sharp_lower_bounds
    {Seed : Type} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (s : Seed → DeterministicAdaptiveStrategy (PairedQuery (linearProofDimension T))
      (PairedAnswer (linearProofDimension T)) (Fin (linearProofDimension T) → ℝ))
    (hs : MeasurableStrategy s T)
    (hFeas : ∀ seed π, ScaledFeasible alpha π
      ((s seed).run (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π T)) :
    let P := FinitePMF.uniform (Equiv.Perm (Fin (linearProofDimension T)))
    let G := fun seed π => scaledFamilyLoss (linearProofDimension T) (hardRho T) L alpha π
      ((s seed).run (scaledConcreteOracle (linearProofDimension T) (hardRho T) L alpha) π T)
    scaledThreshold T L alpha ≤ P.expect (fun π => ∫ seed, G seed π ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | scaledThreshold T L alpha ≤ G seed π}) := by
  dsimp only
  have hk : 0 < L/alpha^2 := by positivity
  have hf : ∀ seed π, coordinateEnergy (permutedHardWeight (linearProofDimension T) π)
      ((baseSimulation (s seed) L alpha).run (concreteOracle _ (hardRho T)) π T) ≤
        hardC (linearProofDimension T)^2 := by
    intro seed π
    simpa only [baseSimulation_run, ScaledFeasible] using hFeas seed π
  have hb := baseFamily_sharp_lower_bounds μ T (fun seed => baseSimulation (s seed) L alpha)
    (baseSimulation_measurable hs L alpha) hf
  simp only [baseSimulation_run] at hb
  constructor
  · simpa only [scaledThreshold, scaledFamilyLoss, integral_const_mul,
      FinitePMF.expect_const_mul] using mul_le_mul_of_nonneg_left hb.1 hk.le
  · simpa only [scaledThreshold, scaledFamilyLoss, mul_le_mul_iff_right₀ hk] using hb.2

lemma concreteHardSet_isBounded (d : ℕ) (π : Equiv.Perm (Fin d)) :
    Bornology.IsBounded (weightedHardSet (hardC d) (permutedHardWeight d π)) := by
  rw [Metric.isBounded_iff]
  refine ⟨2*hardRadius d, ?_⟩
  intro x hx y hy
  calc
    dist x y ≤ ‖x‖+‖y‖ := by simpa [dist_eq_norm] using norm_sub_le x y
    _ ≤ 2*hardRadius d := by
      linarith [concreteHardSet_norm_le_radius π hx, concreteHardSet_norm_le_radius π hy]

lemma scaledThreshold_eq_diameter (T : ℕ) (L alpha : ℝ) (ha : 0 < alpha)
    (π : Equiv.Perm (Fin (linearProofDimension T))) :
    scaledThreshold T L alpha = sharpConstant * L *
      (Metric.diam (scaledSet (weightedHardSet (hardC (linearProofDimension T))
        (permutedHardWeight (linearProofDimension T) π)) alpha))^2/(T+1 : ℝ)^2 := by
  rw [diam_scaledSet ha (concreteHardSet_isBounded _ π)]
  unfold scaledThreshold
  rw [sharp_threshold_eq_diameter T π]
  ring

/-- The coordinate predicate is exactly membership in the scaled Euclidean set. -/
lemma scaledFeasible_iff_mem {d : ℕ} (alpha : ℝ) (π : Equiv.Perm (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    ScaledFeasible alpha π (fun i => x i) ↔
      x ∈ scaledSet (weightedHardSet (hardC d) (permutedHardWeight d π)) alpha := by
  exact (mem_weightedHardSet_iff_coordinateEnergy _ _ (alpha • x)).symm

lemma scaledHardSet_stronglyConvex (d : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (π : Equiv.Perm (Fin d)) :
    IsStronglyConvexBall (scaledSet (weightedHardSet (hardC d)
      (permutedHardWeight d π)) alpha) alpha := by
  simpa [scaledSet] using (concreteHardSet_isStronglyConvexBall d π).preimage_smul ha

lemma scaledConcreteOracle_zero (d : ℕ) (rho L alpha : ℝ)
    (π : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    (scaledConcreteOracle d rho L alpha π (x, 0)).2.2 = 0 := by
  simp [scaledConcreteOracle, scaleAnswer, scaleQuery, concreteOracle, concreteLMO_zero]

lemma scaledConcreteOracle_LMO {d : ℕ} (rho L alpha : ℝ) (ha : 0 < alpha)
    (π : Equiv.Perm (Fin d)) (q : PairedQuery d) :
    let z := (scaledConcreteOracle d rho L alpha π q).2.2
    ScaledFeasible alpha π z ∧ ∀ x, ScaledFeasible alpha π x →
      (∑ i, q.2 i*z i) ≤ ∑ i, q.2 i*x i := by
  dsimp only [scaledConcreteOracle, scaleAnswer, concreteOracle, scaleQuery]
  have hz := concreteLMO_correct d π q.2
  constructor
  · simpa only [ScaledFeasible, smul_smul, mul_inv_cancel₀ ha.ne', one_smul] using hz.1
  · intro x hx
    have h := mul_le_mul_of_nonneg_left (hz.2 (alpha • x) hx) (inv_nonneg.mpr ha.le)
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul] at h ⊢
    convert h using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> field_simp

noncomputable def scaledCoordinateObjective (d : ℕ) (rho L alpha : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  (L/alpha^2)*coordinateObjective (objectiveCenter rho (hardTopWeight d)) (alpha • x)

lemma scaledCoordinateObjective_hasFDerivAt (d : ℕ) (rho L alpha : ℝ)
    (x : Fin d → ℝ) :
    HasFDerivAt (scaledCoordinateObjective d rho L alpha)
      ((L/alpha^2) • (coordinateObjectiveDifferential
        (objectiveCenter rho (hardTopWeight d)) (alpha • x)).comp
          (alpha • ContinuousLinearMap.id ℝ (Fin d → ℝ))) x := by
  exact ((coordinateObjective_hasFDerivAt _ _).comp x
    (alpha • ContinuousLinearMap.id ℝ (Fin d → ℝ)).hasFDerivAt).const_mul _

lemma scaledConcreteOracle_first_order {d : ℕ} (rho L alpha : ℝ) (ha : 0 < alpha)
    (π : Equiv.Perm (Fin d)) (q : PairedQuery d) (v : Fin d → ℝ) :
    (scaledConcreteOracle d rho L alpha π q).1 = scaledCoordinateObjective d rho L alpha q.1 ∧
    ((L/alpha^2) • (coordinateObjectiveDifferential
      (objectiveCenter rho (hardTopWeight d)) (alpha • q.1)).comp
        (alpha • ContinuousLinearMap.id ℝ (Fin d → ℝ))) v =
      ∑ i, (scaledConcreteOracle d rho L alpha π q).2.1 i*v i := by
  constructor
  · rfl
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, coordinateObjectiveDifferential_apply,
      scaledConcreteOracle, scaleAnswer, scaleQuery, concreteOracle, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp

lemma scaledFamilyLoss_eq_gap (d : ℕ) (rho L alpha : ℝ) (ha : 0 < alpha)
    (π : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    scaledFamilyLoss d rho L alpha π x = scaledCoordinateObjective d rho L alpha x -
      scaledCoordinateObjective d rho L alpha
        (alpha⁻¹ • optimizerPoint rho (hardTopWeight d) (permutedHardWeight d π)) := by
  simp only [scaledFamilyLoss, hardFamilyLoss, scaledCoordinateObjective, smul_smul,
    mul_inv_cancel₀ ha.ne', one_smul]
  ring

lemma scaled_optimizer (T : ℕ) (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha)
    (π : Equiv.Perm (Fin (linearProofDimension T))) :
    let xstar := alpha⁻¹ • optimizerPoint (hardRho T) (hardTopWeight (linearProofDimension T))
      (permutedHardWeight (linearProofDimension T) π)
    ScaledFeasible alpha π xstar ∧ ∀ y, ScaledFeasible alpha π y →
      scaledCoordinateObjective (linearProofDimension T) (hardRho T) L alpha xstar ≤
        scaledCoordinateObjective (linearProofDimension T) (hardRho T) L alpha y := by
  have h := concrete_optimizerPoint_unique_minimizer π (hardRho_spec T).1 (hardRho_spec T).2
  dsimp only
  constructor
  · simp only [ScaledFeasible, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    exact h.1.le
  · intro y hy
    simp only [scaledCoordinateObjective, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    exact mul_le_mul_of_nonneg_left (h.2 (alpha • y) hy).1 (by positivity)

lemma coordinateObjective_eq_norm (d : ℕ) (M : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    coordinateObjective M (fun i => x i) =
      (1/2 : ℝ)*‖x - WithLp.toLp 2 (fun _ : Fin d => M)‖^2 := by
  simp [coordinateObjective, EuclideanSpace.norm_sq_eq, Finset.mul_sum]

lemma commonQuadratic_model (d : ℕ) (M : ℝ) :
    HasQuadraticModel (fun x : EuclideanSpace ℝ (Fin d) => coordinateObjective M (fun i => x i))
      (fun x => x-WithLp.toLp 2 (fun _ : Fin d => M)) 1 1 := by
  constructor <;> intro x y
  all_goals
    simp only [coordinateObjective_eq_norm, one_div]
    have h := quadratic_gap_identity y x (WithLp.toLp 2 (fun _ : Fin d => M))
    linarith

lemma scaledQuadratic_model (d : ℕ) (rho L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha) :
    HasQuadraticModel
      (fun x : EuclideanSpace ℝ (Fin d) => scaledCoordinateObjective d rho L alpha (fun i => x i))
      (scaledGradient (fun x => x-WithLp.toLp 2
        (fun _ : Fin d => objectiveCenter rho (hardTopWeight d))) L alpha) L L :=
  hasQuadraticModel_scaled (commonQuadratic_model d _) hL ha

lemma concreteLMO_unique {d : ℕ} (π : Equiv.Perm (Fin d)) (p : Fin d → ℝ)
    (hp : ∃ i, p i ≠ 0) (x : Fin d → ℝ)
    (hx : coordinateEnergy (permutedHardWeight d π) x ≤ hardC d^2)
    (hv : (∑ i, p i*x i) = ∑ i, p i*concreteLMO d π p i) : x = concreteLMO d π p := by
  exact explicitLMO_unique p _ _ (hardC_pos d) (fun i => hardWeight_nonneg d (π i))
    (fun i => by dsimp [permutedRank]; positivity) (permutedHardWeight_sq_rank π) hp hx hv

lemma scaledConcreteOracle_LMO_unique {d : ℕ} (rho L alpha : ℝ) (ha : 0 < alpha)
    (π : Equiv.Perm (Fin d)) (q : PairedQuery d) (hp : ∃ i, q.2 i ≠ 0)
    (x : Fin d → ℝ) (hx : ScaledFeasible alpha π x)
    (hv : (∑ i, q.2 i*x i) = ∑ i, q.2 i*(scaledConcreteOracle d rho L alpha π q).2.2 i) :
    x = (scaledConcreteOracle d rho L alpha π q).2.2 := by
  have hval : (∑ i, q.2 i*(alpha • x) i) = ∑ i, q.2 i*concreteLMO d π q.2 i := by
    calc
      _ = alpha*(∑ i, q.2 i*x i) := by
        simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = alpha*(∑ i, q.2 i*(scaledConcreteOracle d rho L alpha π q).2.2 i) := congrArg _ hv
      _ = _ := by
        simp only [scaledConcreteOracle, scaleQuery, scaleAnswer, concreteOracle, Finset.mul_sum,
          Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
  have he := concreteLMO_unique π q.2 hp (alpha • x) hx hval
  have hh := congrArg (fun v : Fin d → ℝ => alpha⁻¹ • v) he
  simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul,
    scaledConcreteOracle, scaleQuery, scaleAnswer, concreteOracle] using hh

lemma scaledGradient_norm_sub {d : ℕ} (center : EuclideanSpace ℝ (Fin d))
    (L alpha : ℝ) (hL : 0 < L) (ha : 0 < alpha) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖scaledGradient (fun x => x-center) L alpha x -
        scaledGradient (fun x => x-center) L alpha y‖ = L*‖x-y‖ := by
  have hscalar : (L/alpha)*alpha = L := by field_simp
  have he : scaledGradient (fun x => x-center) L alpha x -
      scaledGradient (fun x => x-center) L alpha y = L • (x-y) := by
    simp only [scaledGradient, ← smul_sub, sub_sub_sub_cancel_right, ← mul_smul, hscalar]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hL]

end Lemmata.DistributionalLowerBounds.Core.Distributional
