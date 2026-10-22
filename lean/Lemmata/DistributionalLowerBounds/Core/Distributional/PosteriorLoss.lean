module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FerrersReduction

@[expose] public section

/-!
# Terminal loss from the actual reduced posterior

The variance bound is instantiated with the actual remaining ranks and feasible
outputs. The deficit, its initial value/cap, and terminal loss are constructed
from numerical histories; no next-query certificate is used here.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

lemma concrete_quadratic_growth {d : ℕ} (π : Equiv.Perm (Fin d)) {rho : ℝ}
    (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (heq : rhoLHS (hardWeight d) (hardTopWeight d) rho = hardC d ^ 2)
    (y : Fin d → ℝ) (hy : coordinateEnergy (permutedHardWeight d π) y ≤ hardC d ^ 2) :
    (1/2 : ℝ) * ∑ i, (y i - optimizerPoint rho (hardTopWeight d) (permutedHardWeight d π) i)^2 ≤
      hardFamilyLoss d rho π y := by
  let w := permutedHardWeight d π
  let xs := optimizerPoint rho (hardTopWeight d) w
  let M := objectiveCenter rho (hardTopWeight d)
  have hb : coordinateEnergy w xs = hardC d^2 :=
    (concrete_optimizerPoint_unique_minimizer π hrho heq).1
  have hs : coordinateEnergy w xs + ∑ i, (xs i + w i)*(y i-xs i) +
      (1/2 : ℝ)*∑ i, (y i-xs i)^2 ≤ coordinateEnergy w y := by
    unfold coordinateEnergy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => nonnegative_energy_strong_subgradient
      (mul_nonneg hrho.1.le (sub_nonneg.mpr (hardWeight_le_top d (π i))))
      (hardWeight_nonneg d (π i)) (y i))
  have hn : ∑ i, (xs i+w i)*(y i-xs i) ≤ 0 := by
    rw [hb] at hs
    have hh : 0 ≤ ∑ i, (y i-xs i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  have hstationary : ∀ i, xs i - M = -optimizerMultiplier rho * (xs i+w i) := by
    intro i
    have h := optimizer_stationarity (wd := hardTopWeight d) (w := w i) (ne_of_lt hrho.2)
    change xs i-M+optimizerMultiplier rho*(xs i+w i)=0 at h
    linarith
  have hcross : (∑ i, (xs i-M)*(y i-xs i)) =
      -optimizerMultiplier rho * ∑ i, (xs i+w i)*(y i-xs i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hstationary]
    ring
  have hg : hardFamilyLoss d rho π y =
      (1/2 : ℝ)*∑ i, (y i-xs i)^2 + ∑ i, (xs i-M)*(y i-xs i) := by
    unfold hardFamilyLoss coordinateObjective
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (1/2 : ℝ)*(y i-M)^2-(1/2 : ℝ)*(xs i-M)^2 = _
    ring
  have hl : 0 ≤ optimizerMultiplier rho := by
    unfold optimizerMultiplier
    exact div_nonneg hrho.1.le (sub_pos.mpr hrho.2).le
  have hc := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hl) hn
  rw [hg, hcross]
  linarith

lemma hardFamilyLoss_invariant (d : ℕ) (rho : ℝ) (π σ : Equiv.Perm (Fin d)) (y : Fin d → ℝ) :
    hardFamilyLoss d rho π y = hardFamilyLoss d rho σ y := by
  unfold hardFamilyLoss
  rw [concrete_optimal_value_permutation_invariant, concrete_optimal_value_permutation_invariant]

namespace RankConstraint

variable {d : ℕ} (S : RankConstraint d) (hS : Nonempty S.Realizations)

lemma reduced_optimizerCoordinate (rho : ℝ) (σ : FerrersPerm (S.reducedData hS))
    (i : Fin S.remaining) :
    optimizerPoint rho (hardTopWeight d) (permutedHardWeight d ((S.ferrersEquiv hS).symm σ).val)
        (S.rowEnum i) =
      rho * hardC d * Real.sqrt 2 *
        (Real.sqrt (d : ℝ) - Real.sqrt (S.rank hS (σ.val i) : ℝ)) := by
  unfold optimizerPoint optimizerCoordinate permutedHardWeight
  rw [S.ferrersEquiv_symm_rank]
  simp only [hardTopWeight, hardWeight, rank]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  ring

/-- The actual posterior terminal estimate, including singleton/empty-row models.
Feasibility is required for EVERY compatible full instance, not just one of them. -/
theorem feasible_common_output_loss {rho : ℝ} (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (heq : rhoLHS (hardWeight d) (hardTopWeight d) rho = hardC d^2)
    (hd : 0 < d) (y : Fin d → ℝ)
    (hy : ∀ π : S.Realizations, coordinateEnergy (permutedHardWeight d π.val) y ≤ hardC d^2)
    (π : S.Realizations) :
    rho^2*hardC d^2*(S.deficit hS)^2/(48*(d : ℝ)^2) ≤ hardFamilyLoss d rho π.val y := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hm : 0 < S.remaining
  · let D := S.reducedData hS
    let X : FerrersPerm D → ℝ := fun σ => hardFamilyLoss d rho ((S.ferrersEquiv hS).symm σ).val y
    have hpoint : ∀ σ : FerrersPerm D,
        (1/2 : ℝ)*∑ i, (y (S.rowEnum i)-rho*hardC d*Real.sqrt 2*
          (Real.sqrt (d : ℝ)-Real.sqrt (S.rank hS (σ.val i) : ℝ)))^2 ≤ X σ := by
      intro σ
      simp_rw [← S.reduced_optimizerCoordinate hS rho σ]
      have hs : (∑ i, (y (S.rowEnum i) -
          optimizerPoint rho (hardTopWeight d) (permutedHardWeight d ((S.ferrersEquiv hS).symm σ).val)
            (S.rowEnum i))^2) ≤ ∑ i, (y i-
          optimizerPoint rho (hardTopWeight d) (permutedHardWeight d ((S.ferrersEquiv hS).symm σ).val) i)^2 := by
        rw [S.sum_free (fun i => (y i - optimizerPoint rho (hardTopWeight d)
          (permutedHardWeight d ((S.ferrersEquiv hS).symm σ).val) i)^2)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      exact (mul_le_mul_of_nonneg_left hs (by norm_num)).trans
        (concrete_quadratic_growth _ hrho heq y (hy _))
    have hv := ferrers_conditional_error D hm (fun a => (S.rank hS a : ℝ)) hdR
      (fun a => by positivity)
      (fun a => by exact_mod_cast S.rank_le hS a) (S.rank_gap hS)
      (fun i => y (S.rowEnum i)) X hpoint
    rw [← S.deficit_eq_sum hS] at hv
    have hav : uniformAverage X = hardFamilyLoss d rho π.val y := by
      have hx : X = fun _ => hardFamilyLoss d rho π.val y := by
        funext σ
        exact hardFamilyLoss_invariant _ _ _ _ _
      rw [hx, uniformAverage, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      exact mul_div_cancel_left₀ _ (card_cast_pos (Ω := FerrersPerm D)).ne'
    rw [hav] at hv
    have hmR : (0 : ℝ) < S.remaining := by exact_mod_cast hm
    have hmd : (S.remaining : ℝ) ≤ d := by exact_mod_cast S.remaining_le
    have hden : 48*(S.remaining : ℝ)*d ≤ 48*(d : ℝ)^2 := by nlinarith
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans hv
  · have hm0 : S.remaining = 0 := by omega
    rw [S.deficit_zero_of_remaining_zero hS hm0]
    simp only [sq, mul_zero, zero_div]
    have hg := concrete_quadratic_growth π.val hrho heq y (hy π)
    have hh : 0 ≤ (1/2 : ℝ)*∑ i, (y i-
      optimizerPoint rho (hardTopWeight d) (permutedHardWeight d π.val) i)^2 := by positivity
    linarith

end RankConstraint

noncomputable def numericalDeficit {d : ℕ} {Output : Type}
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (π : Equiv.Perm (Fin d)) : ℝ :=
  (numericalTranscriptConstraint strategy (strategy.transcript (concreteOracle d rho) π T)).deficit
    (numericalPosterior_nonempty strategy rho T (reachableHistoryOf strategy (concreteOracle d rho) T π))

lemma numericalDeficit_initial {d : ℕ} {Output : Type}
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (π : Equiv.Perm (Fin d)) : numericalDeficit strategy rho 0 π = initialDeficit d :=
  RankConstraint.empty_deficit _

lemma numericalDeficit_cap {d : ℕ} {Output : Type}
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (π : Equiv.Perm (Fin d)) : numericalDeficit strategy rho T π ≤ initialDeficit d :=
  RankConstraint.deficit_le_initial _ _

/-- Terminal variance/loss for the ACTUAL run, not a supplied `hloss` input. -/
theorem numerical_terminal_loss {d : ℕ}
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) (Fin d → ℝ))
    {rho : ℝ} (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (heq : rhoLHS (hardWeight d) (hardTopWeight d) rho = hardC d^2)
    (hd : 0 < d) (T : ℕ)
    (hFeas : ∀ π, coordinateEnergy (permutedHardWeight d π)
      (strategy.run (concreteOracle d rho) π T) ≤ hardC d^2)
    (π : Equiv.Perm (Fin d)) :
    rho^2*hardC d^2*(numericalDeficit strategy rho T π)^2/(48*(d : ℝ)^2) ≤
      hardFamilyLoss d rho π (strategy.run (concreteOracle d rho) π T) := by
  let h := reachableHistoryOf strategy (concreteOracle d rho) T π
  let S := numericalTranscriptConstraint strategy h.val
  have hS := numericalPosterior_nonempty strategy rho T h
  have hc : S.Compatible π := (reachable_numerical_constraint_iff strategy rho T h π).mpr rfl
  apply S.feasible_common_output_loss hS hrho heq hd _ ?_ ⟨π, hc⟩
  intro σ
  have hh := (numericalTranscriptConstraint_compatible_iff strategy rho π σ.val T).mp σ.property
  have ho : strategy.run (concreteOracle d rho) σ.val T = strategy.run (concreteOracle d rho) π T :=
    congrArg strategy.output hh
  rw [← ho]
  exact hFeas σ.val

end Lemmata.DistributionalLowerBounds.Core.Distributional
