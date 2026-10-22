module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.MeasurableSeed
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

/-!
# Regularity of the actual terminal hard-family loss

Feasibility is required for every seed, not merely almost everywhere. For a
measurable output, the concrete quadratic loss is bounded and measurable, so
integrability and every non-strict threshold event follow. The final endpoint
removes `hInt` and `hMeas` from the certified-strategy application. Constructing
that certificate and proving output measurability from an oracle controller
are still separate, explicitly documented obligations.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory

lemma coordinateObjective_nonneg {d : ℕ} (M : ℝ) (x : Fin d → ℝ) :
    0 ≤ coordinateObjective M x := by
  unfold coordinateObjective
  exact Finset.sum_nonneg (fun i _ => by positivity)

lemma coordinateEnergy_sq_bound {d : ℕ} {C : ℝ} (w x : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : coordinateEnergy w x ≤ C^2) :
    (∑ i, x i^2) ≤ 2*C^2 := by
  have h : (1/2 : ℝ)*(∑ i, x i^2) ≤ coordinateEnergy w x := by
    rw [Finset.mul_sum]
    unfold coordinateEnergy
    apply Finset.sum_le_sum
    intro i _
    exact le_add_of_nonneg_right (mul_nonneg (hw i) (abs_nonneg _))
  linarith

/-- A deliberately loose bound: no optimization of this constant is needed
for integrability. The case of an empty coordinate type is included. -/
lemma coordinateObjective_le_of_feasible {d : ℕ} {C : ℝ} (w x : Fin d → ℝ)
    (M : ℝ) (hw : ∀ i, 0 ≤ w i) (hx : coordinateEnergy w x ≤ C^2) :
    coordinateObjective M x ≤ 2*C^2 + (d : ℝ)*M^2 := by
  have hs := coordinateEnergy_sq_bound w x hw hx
  have h : coordinateObjective M x ≤ (∑ i, x i^2) + (d : ℝ)*M^2 := by
    calc
      coordinateObjective M x ≤ ∑ i, (x i^2 + M^2) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (x i + M)]
      _ = _ := by simp [Finset.sum_add_distrib]
  linarith

lemma coordinate_loss_abs_bound {d : ℕ} {C : ℝ} (w x : Fin d → ℝ)
    (M opt : ℝ) (hw : ∀ i, 0 ≤ w i) (hx : coordinateEnergy w x ≤ C^2) :
    |coordinateObjective M x - opt| ≤ 2*C^2 + (d : ℝ)*M^2 + |opt| := by
  calc
    |coordinateObjective M x - opt| ≤ |coordinateObjective M x| + |opt| := abs_sub _ _
    _ = coordinateObjective M x + |opt| := by rw [abs_of_nonneg (coordinateObjective_nonneg M x)]
    _ ≤ _ := by linarith [coordinateObjective_le_of_feasible w x M hw hx]

lemma continuous_coordinateObjective (d : ℕ) (M : ℝ) :
    Continuous (coordinateObjective (d := d) M) := by
  unfold coordinateObjective
  fun_prop

/-- General weighted-set regularity, proved rather than taken as an integral
hypothesis. The optimum is any fixed real constant; the specialization below
uses the actual hard-family optimizer's objective. -/
theorem coordinate_loss_regular {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsFiniteMeasure μ] {d : ℕ} (C M opt : ℝ)
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : Seed → Fin d → ℝ) (hMeas : Measurable x)
    (hFeas : ∀ seed, coordinateEnergy w (x seed) ≤ C^2) :
    Measurable (fun seed => coordinateObjective M (x seed) - opt) ∧
    Integrable (fun seed => coordinateObjective M (x seed) - opt) μ ∧
    ∀ threshold : ℝ, MeasurableSet {seed | threshold ≤ coordinateObjective M (x seed) - opt} := by
  have hm : Measurable (fun seed => coordinateObjective M (x seed) - opt) :=
    ((continuous_coordinateObjective d M).measurable.comp hMeas).sub measurable_const
  refine ⟨hm, ?_, fun threshold => measurableSet_le measurable_const hm⟩
  apply Integrable.of_bound hm.aestronglyMeasurable (2*C^2 + (d : ℝ)*M^2 + |opt|)
  exact Filter.Eventually.of_forall (fun seed => by
    simpa only [Real.norm_eq_abs] using coordinate_loss_abs_bound w (x seed) M opt hw (hFeas seed))

noncomputable def hardFamilyLoss (d : ℕ) (rho : ℝ) (π : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) : ℝ :=
  coordinateObjective (objectiveCenter rho (hardTopWeight d)) x -
    coordinateObjective (objectiveCenter rho (hardTopWeight d))
      (optimizerPoint rho (hardTopWeight d) (permutedHardWeight d π))

theorem hardFamilyLoss_regular {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsFiniteMeasure μ] (d : ℕ) (rho : ℝ)
    (π : Equiv.Perm (Fin d)) (x : Seed → Fin d → ℝ) (hMeas : Measurable x)
    (hFeas : ∀ seed, coordinateEnergy (permutedHardWeight d π) (x seed) ≤ (hardC d)^2) :
    Measurable (fun seed => hardFamilyLoss d rho π (x seed)) ∧
    Integrable (fun seed => hardFamilyLoss d rho π (x seed)) μ ∧
    ∀ threshold : ℝ, MeasurableSet {seed | threshold ≤ hardFamilyLoss d rho π (x seed)} := by
  exact coordinate_loss_regular μ (hardC d) _ _ (permutedHardWeight d π)
    (fun i => hardWeight_nonneg d (π i)) x hMeas hFeas

/-- The main averaging endpoint now needs feasible measurable outputs, not
separate `hInt`/`hMeas` assumptions about their losses. It STILL requires the
raw-transcript certificate and deficit-to-loss bound; it is not the final
unrestricted-method theorem. -/
theorem measurableSeed_feasible_strategy_sharp_lower_bounds
    {Seed Query Answer : Type} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (T : ℕ)
    (P : FinitePMF (Equiv.Perm (Fin (linearProofDimension T))))
    (strategy : Seed → DeterministicAdaptiveStrategy Query Answer (Fin (linearProofDimension T) → ℝ))
    (oracle : Equiv.Perm (Fin (linearProofDimension T)) → Query → Answer)
    (deficit : Seed → ℕ → Equiv.Perm (Fin (linearProofDimension T)) → ℝ)
    (certificate : ∀ seed, CertifiedStrategy (linearProofDimension T) T P
      (strategy seed) oracle (deficit seed))
    {rho : ℝ} (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq : rhoLHS (hardWeight (linearProofDimension T))
      (hardTopWeight (linearProofDimension T)) rho = hardC (linearProofDimension T)^2)
    (hzero : ∀ seed, P.expect (deficit seed 0) = initialDeficit (linearProofDimension T))
    (hcap : ∀ seed π, deficit seed T π ≤ initialDeficit (linearProofDimension T))
    (hloss : ∀ seed π, rho^2*hardC (linearProofDimension T)^2*deficit seed T π^2 /
      (48*(linearProofDimension T : ℝ)^2) ≤
        hardFamilyLoss (linearProofDimension T) rho π ((strategy seed).run oracle π T))
    (hOutput : ∀ π, Measurable (fun seed => (strategy seed).run oracle π T))
    (hFeas : ∀ seed π, coordinateEnergy (permutedHardWeight (linearProofDimension T) π)
      ((strategy seed).run oracle π T) ≤ hardC (linearProofDimension T)^2) :
    let threshold := hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2)
    threshold ≤ P.expect (fun π => ∫ seed,
      hardFamilyLoss (linearProofDimension T) rho π ((strategy seed).run oracle π T) ∂μ) ∧
    (3 : ℝ)/4 ≤ P.expect (fun π => μ.real {seed | threshold ≤
      hardFamilyLoss (linearProofDimension T) rho π ((strategy seed).run oracle π T)}) := by
  apply measurableSeed_strategy_sharp_lower_bounds μ P strategy oracle
    (hardFamilyLoss (linearProofDimension T) rho) deficit T certificate hrho hrhoEq hzero hcap hloss
  · intro π
    exact (hardFamilyLoss_regular μ _ rho π _ (hOutput π) (fun seed => hFeas seed π)).2.1
  · intro π
    exact (hardFamilyLoss_regular μ _ rho π _ (hOutput π) (fun seed => hFeas seed π)).2.2 _

end Lemmata.DistributionalLowerBounds.Core.Distributional
