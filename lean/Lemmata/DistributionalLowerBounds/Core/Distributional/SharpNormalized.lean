module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.TerminalLoss

@[expose] public section

/-!
# Exact diameter-normalized sharp constant

This packages expectation and probability at the same numerical threshold.
It inherits the explicit `CertifiedStrategy` and terminal-loss interface; it
is not an unconditional theorem for an unformalized numerical-oracle model.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

noncomputable def sharpConstant : ℝ := (3+2*Real.sqrt 2)/(6144*64^2)

lemma sharpConstant_pos : 0 < sharpConstant := by
  unfold sharpConstant
  positivity

lemma sharp_threshold_identity (T : ℕ) (C : ℝ) :
    C^2/(768*(linearProofDimension T : ℝ)^2) =
      sharpConstant*(2*C*(2-Real.sqrt 2))^2/(T+1 : ℝ)^2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hfactor : (3+2*Real.sqrt 2)*(2-Real.sqrt 2)^2 = 2 := by
    calc
      (3+2*Real.sqrt 2)*(2-Real.sqrt 2)^2 =
          2*Real.sqrt 2*((Real.sqrt 2)^2-2)-5*((Real.sqrt 2)^2-2)+2 := by ring
      _ = 2 := by rw [hs]; ring
  rw [linearProofDimension_cast]
  unfold sharpConstant
  have ht : (T : ℝ)+1 ≠ 0 := by positivity
  field_simp
  have h := congrArg (fun x : ℝ => C^2*x) hfactor
  nlinarith [h]

/-- The exact constant in the paper, using the proved diameter of every
permutation instance. -/
theorem sharp_threshold_eq_diameter (T : ℕ)
    (π : Equiv.Perm (Fin (linearProofDimension T))) :
    hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2) =
      sharpConstant * (Metric.diam (weightedHardSet (hardC (linearProofDimension T))
        (permutedHardWeight (linearProofDimension T) π)))^2/(T+1 : ℝ)^2 := by
  rw [concreteHardSet_diameter π (by have := linearProofDimension_ge_three T; omega)]
  exact sharp_threshold_identity T _

/-- Both lower bounds, with exactly the same constant and threshold.
The process certificate, optimizer equation, initial deficit, cap, and
terminal loss comparison are intentionally visible in this signature. -/
theorem finiteSeed_strategy_sharp_lower_bounds
    {Seed Ω Query Answer Output : Type} [Fintype Seed] [Fintype Ω]
    (seedLaw : FinitePMF Seed) (instanceLaw : FinitePMF Ω)
    (strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Ω → Query → Answer) (loss : Ω → Output → ℝ)
    (deficit : Seed → ℕ → Ω → ℝ) (T : ℕ)
    (π : Equiv.Perm (Fin (linearProofDimension T)))
    (certificate : ∀ seed, CertifiedStrategy (linearProofDimension T) T instanceLaw
      (strategy seed) oracle (deficit seed))
    {rho : ℝ} (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq : rhoLHS (hardWeight (linearProofDimension T))
      (hardTopWeight (linearProofDimension T)) rho = hardC (linearProofDimension T)^2)
    (hzero : ∀ seed, instanceLaw.expect (deficit seed 0) = initialDeficit (linearProofDimension T))
    (hcap : ∀ seed ω, deficit seed T ω ≤ initialDeficit (linearProofDimension T))
    (hloss : ∀ seed ω, rho^2*hardC (linearProofDimension T)^2*deficit seed T ω^2 /
      (48*(linearProofDimension T : ℝ)^2) ≤ loss ω ((strategy seed).run oracle ω T)) :
    let threshold := sharpConstant * (Metric.diam (weightedHardSet (hardC (linearProofDimension T))
      (permutedHardWeight (linearProofDimension T) π)))^2/(T+1 : ℝ)^2
    threshold ≤ (seedLaw.product instanceLaw).expect
        (fun pair => loss pair.2 ((strategy pair.1).run oracle pair.2 T)) ∧
    (3 : ℝ)/4 ≤ (seedLaw.product instanceLaw).prob
        (fun pair => threshold ≤ loss pair.2 ((strategy pair.1).run oracle pair.2 T)) := by
  dsimp only
  rw [← sharp_threshold_eq_diameter T π]
  exact ⟨finiteSeed_strategy_distributional_lower_bound_linear seedLaw instanceLaw
    strategy oracle loss deficit T certificate hrhoIoo hrhoEq hzero hloss,
    finiteSeed_strategy_probability_lower_bound_linear seedLaw instanceLaw
      strategy oracle loss deficit T certificate hrhoIoo hrhoEq hzero hcap hloss⟩

end Lemmata.DistributionalLowerBounds.Core.Distributional
