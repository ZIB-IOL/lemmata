module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.ProbabilityLowerBound

@[expose] public section

/-!
# Deficit caps and the conditional-to-pointwise loss step

The common optimal value is proved for the actual permuted optimizer formula.
Positive-mass conditional lower bounds then become pointwise lower bounds when
loss depends only on the transcript. The numerical posterior construction and
the conditional variance bound for its concrete fibers remain explicit inputs;
this file does not silently manufacture those certificates.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

lemma DownEdge.natDeficit_le_initial {m : ℕ} (D : FerrersData m) :
    (DownEdge.natDeficit D : ℝ) ≤ initialDeficit m := by
  rw [DownEdge.natDeficit_eq, Nat.cast_sum]
  calc
    (∑ i : Fin m, ((i.val - D.lower i : ℕ) : ℝ)) ≤ ∑ i : Fin m, (i.val : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast Nat.sub_le i.val (D.lower i)
    _ = _ := sum_fin_val m

lemma initialDeficit_mono {m d : ℕ} (hmd : m ≤ d) :
    initialDeficit m ≤ initialDeficit d := by
  by_cases hd : d = 0
  · have hm : m = 0 := by omega
    simp [hm, hd]
  · have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hmR : (0 : ℝ) ≤ m := by positivity
    have hmdR : (m : ℝ) ≤ d := by exact_mod_cast hmd
    have hprod := mul_nonneg (sub_nonneg.mpr hmdR)
      (show 0 ≤ (d : ℝ)+m-1 by linarith)
    dsimp [initialDeficit]
    nlinarith

/-- Deficit read from a supplied posterior node, including the resolved case. -/
noncomputable def HistoryNode.deficit {d : ℕ} : HistoryNode d → ℝ
  | .resolved => 0
  | .active _ D _ _ _ => DownEdge.natDeficit D

lemma HistoryNode.deficit_le_initial {d : ℕ} (node : HistoryNode d) :
    node.deficit ≤ initialDeficit d := by
  cases node with
  | resolved => simpa [HistoryNode.deficit, initialDeficit] using
      (initialDeficit_mono (Nat.zero_le d))
  | active m D hm hmle query =>
      exact (DownEdge.natDeficit_le_initial D).trans (initialDeficit_mono hmle)

/-- Reindexing the optimizer's objective proves the common optimal value.
Together with `concrete_optimizerPoint_unique_minimizer`, this is the actual
hard-family optimum, not an assumption about a generic loss function. -/
theorem concrete_optimal_value_permutation_invariant
    (d : ℕ) (rho M : ℝ) (π : Equiv.Perm (Fin d)) :
    coordinateObjective M (optimizerPoint rho (hardTopWeight d) (permutedHardWeight d π)) =
      coordinateObjective M (optimizerPoint rho (hardTopWeight d) (hardWeight d)) := by
  unfold coordinateObjective optimizerPoint permutedHardWeight
  exact Equiv.sum_comp π (fun i =>
    (1/2 : ℝ)*(optimizerCoordinate rho (hardTopWeight d) (hardWeight d i)-M)^2)

namespace FinitePMF

variable {Ω H : Type*} [Fintype Ω] [Fintype H]

lemma fiberContribution_of_history_loss (P : FinitePMF Ω) (history : Ω → H)
    (L : H → ℝ) (h : H) :
    P.fiberContribution history (fun ω => L (history ω)) h =
      (P.map history).weight h * L h := by
  classical
  unfold fiberContribution map
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : history ω = h <;> simp [he]

lemma history_mass_pos (P : FinitePMF Ω) (history : Ω → H)
    (ω : Ω) (hω : 0 < P.weight ω) : 0 < (P.map history).weight (history ω) := by
  classical
  have hle : P.weight ω ≤ (P.map history).weight (history ω) := by
    change P.weight ω ≤ ∑ a, if history a = history ω then P.weight a else 0
    calc
      P.weight ω = (if history ω = history ω then P.weight ω else 0) := by simp
      _ ≤ _ := Finset.single_le_sum
        (f := fun a : Ω => if history a = history ω then P.weight a else 0)
        (fun a _ => by split_ifs; exact P.nonneg a; exact le_rfl) (Finset.mem_univ ω)
  exact hω.trans_le hle

/-- This is the missing algebraic transport, not a replacement for the
conditional variance calculation. Full support is appropriate for the uniform
permutation prior; a zero-mass fiber cannot be divided out. -/
theorem pointwise_of_conditional_history_loss
    (P : FinitePMF Ω) (history : Ω → H) (L bound : H → ℝ)
    (hpositive : ∀ ω, 0 < P.weight ω)
    (hconditional : ∀ h, (P.map history).weight h * bound h ≤
      P.fiberContribution history (fun ω => L (history ω)) h) :
    ∀ ω, bound (history ω) ≤ L (history ω) := by
  intro ω
  have h := hconditional (history ω)
  rw [P.fiberContribution_of_history_loss] at h
  exact le_of_mul_le_mul_left h (P.history_mass_pos history ω (hpositive ω))

end FinitePMF

/-- Specialize the transport to a genuine strategy output and a common
objective minus a common optimum. There is no instance-dependent output
inside a fixed transcript fiber. -/
theorem strategy_pointwise_of_conditional_loss
    {Ω Query Answer Output : Type} [Fintype Ω]
    (P : FinitePMF Ω) (strategy : DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Ω → Query → Answer) (f : Output → ℝ) (opt : ℝ) (T : ℕ)
    (bound : ReachableHistory strategy oracle T → ℝ)
    (hpositive : ∀ ω, 0 < P.weight ω)
    (hconditional : ∀ h,
      (reachableHistoryLaw strategy oracle P T).weight h * bound h ≤
        P.fiberContribution (reachableHistoryOf strategy oracle T)
          (fun ω => f (strategy.run oracle ω T) - opt) h) :
    ∀ ω, bound (reachableHistoryOf strategy oracle T ω) ≤ f (strategy.run oracle ω T) - opt := by
  exact P.pointwise_of_conditional_history_loss (reachableHistoryOf strategy oracle T)
    (fun h => f (strategy.output h.val) - opt) bound hpositive hconditional

end Lemmata.DistributionalLowerBounds.Core.Distributional
