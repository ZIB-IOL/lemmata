module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.NumericalDisclosure
public import Lemmata.DistributionalLowerBounds.Core.Distributional.ConcreteController

@[expose] public section

/-!
# Exact rank-constraint posteriors for actual adaptive transcripts

Replay uses only the controller and observed answer list. Its constraint set
is proved equivalent to the actual transcript fiber, for every candidate
permutation. Thus the uniform law on compatible FULL permutations is derived.

This is not yet the reduced Ferrers equivalence, a `WaterQuery` construction,
a deficit-drop identity, or a terminal variance/loss estimate. Posterior state
remains separate from `HistoryNode` next-query progress data. In particular a
zero query does not force the posterior to be resolved.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

variable {d : ℕ} {Output : Type}

lemma concreteOracle_eq_iff (rho : ℝ) (π σ : Equiv.Perm (Fin d)) (q : PairedQuery d) :
    concreteOracle d rho π q = concreteOracle d rho σ q ↔
      concreteLMO d π q.2 = concreteLMO d σ q.2 := by
  simp [concreteOracle]

@[simp] lemma concreteOracle_lmo (rho : ℝ) (π : Equiv.Perm (Fin d)) (q : PairedQuery d) :
    (concreteOracle d rho π q).2.2 = concreteLMO d π q.2 := rfl

noncomputable def numericalReplayStep
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (state : List (PairedAnswer d) × RankConstraint d) (answer : PairedAnswer d) :
    List (PairedAnswer d) × RankConstraint d :=
  (state.1 ++ [answer],
    (numericalDisclosure d (strategy.nextQuery state.1.length state.1).2 answer.2.2).refine state.2)

lemma numericalReplay_prefix
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (answers : List (PairedAnswer d)) (state : List (PairedAnswer d) × RankConstraint d) :
    (answers.foldl (numericalReplayStep strategy) state).1 = state.1 ++ answers := by
  induction answers generalizing state with
  | nil => simp
  | cons a tail ih =>
    simp only [List.foldl_cons, ih, numericalReplayStep, List.append_assoc, List.singleton_append]

noncomputable def numericalTranscriptConstraint
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (answers : List (PairedAnswer d)) : RankConstraint d :=
  (answers.foldl (numericalReplayStep strategy) ([], RankConstraint.empty d)).2

@[simp] lemma numericalTranscriptConstraint_nil
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output) :
    numericalTranscriptConstraint strategy [] = RankConstraint.empty d := rfl

lemma numericalTranscriptConstraint_snoc
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (answers : List (PairedAnswer d)) (a : PairedAnswer d) :
    numericalTranscriptConstraint strategy (answers ++ [a]) =
      (numericalDisclosure d (strategy.nextQuery answers.length answers).2 a.2.2).refine
        (numericalTranscriptConstraint strategy answers) := by
  unfold numericalTranscriptConstraint
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, numericalReplayStep, numericalReplay_prefix,
    List.nil_append]

/-- Exact closure for ACTUAL adaptive numerical transcripts. Query equality is
proved from prefix equality, not assumed independently for counterfactual instances. -/
theorem numericalTranscriptConstraint_compatible_iff
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (π₀ π : Equiv.Perm (Fin d)) (T : ℕ) :
    (numericalTranscriptConstraint strategy
      (strategy.transcript (concreteOracle d rho) π₀ T)).Compatible π ↔
      strategy.transcript (concreteOracle d rho) π T =
        strategy.transcript (concreteOracle d rho) π₀ T := by
  induction T with
  | zero => simp
  | succ t ih =>
    simp only [DeterministicAdaptiveStrategy.transcript_succ]
    rw [numericalTranscriptConstraint_snoc, DeterministicAdaptiveStrategy.transcript_length]
    rw [concreteOracle_lmo, numerical_refine_compatible_iff, ih]
    constructor
    · rintro ⟨hprefix, hanswer⟩
      rw [hprefix]
      congr 1
      exact congrArg (fun a => [a]) ((concreteOracle_eq_iff rho π π₀ _).mpr hanswer)
    · intro he
      have parts := List.append_inj' he (by simp)
      refine ⟨parts.1, ?_⟩
      have ha : concreteOracle d rho π
          (strategy.nextQuery t (strategy.transcript (concreteOracle d rho) π t)) =
          concreteOracle d rho π₀
          (strategy.nextQuery t (strategy.transcript (concreteOracle d rho) π₀ t)) := by
        simpa only [List.singleton_inj] using parts.2
      rw [parts.1] at ha
      exact (concreteOracle_eq_iff rho π π₀ _).mp ha

namespace RankConstraint

/-- Full compatible permutations, deliberately distinct from reduced Ferrers
permutations and from a next-query certificate. Inconsistent constraints may
have an empty realization type. -/
abbrev Realizations (S : RankConstraint d) := {π : Equiv.Perm (Fin d) // S.Compatible π}

noncomputable instance realizationsFintype (S : RankConstraint d) : Fintype S.Realizations :=
  Fintype.ofFinite _

end RankConstraint

lemma reachable_numerical_constraint_iff
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T)
    (π : Equiv.Perm (Fin d)) :
    (numericalTranscriptConstraint strategy h.val).Compatible π ↔
      reachableHistoryOf strategy (concreteOracle d rho) T π = h := by
  obtain ⟨π₀, hπ₀⟩ := h.property
  rw [Subtype.ext_iff]
  change _ ↔ strategy.transcript (concreteOracle d rho) π T = h.val
  rw [← hπ₀]
  exact numericalTranscriptConstraint_compatible_iff strategy rho π₀ π T

/-- An actual equivalence, with no separately supplied probability or decoder-
correctness premise. Its underlying map preserves the original permutation. -/
noncomputable def numericalPosteriorEquiv
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T) :
    {π // reachableHistoryOf strategy (concreteOracle d rho) T π = h} ≃
      (numericalTranscriptConstraint strategy h.val).Realizations :=
  Equiv.subtypeEquivRight (fun π => (reachable_numerical_constraint_iff strategy rho T h π).symm)

lemma numericalPosterior_nonempty
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T) :
    Nonempty (numericalTranscriptConstraint strategy h.val).Realizations := by
  obtain ⟨π₀, hπ₀⟩ := h.property
  refine ⟨⟨π₀, (reachable_numerical_constraint_iff strategy rho T h π₀).mpr ?_⟩⟩
  exact Subtype.ext hπ₀

/-- Uniform conditioning on actual transcripts equals averaging over the
compatible FULL permutations. Reduced Ferrers enumeration remains separate. -/
theorem numerical_uniform_posterior
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T)
    (X : Equiv.Perm (Fin d) → ℝ) :
    (FinitePMF.uniform (Equiv.Perm (Fin d))).fiberContribution
      (reachableHistoryOf strategy (concreteOracle d rho) T) X h =
      (reachableHistoryLaw strategy (concreteOracle d rho)
        (FinitePMF.uniform (Equiv.Perm (Fin d))) T).weight h *
          uniformAverage (fun π : (numericalTranscriptConstraint strategy h.val).Realizations => X π.val) := by
  classical
  exact reachable_uniform_fiberContribution_equiv strategy (concreteOracle d rho) T h X _
    (numericalPosteriorEquiv strategy rho T h) (fun _ => rfl)

lemma numerical_posterior_mass_pos
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T) :
    0 < (reachableHistoryLaw strategy (concreteOracle d rho)
      (FinitePMF.uniform (Equiv.Perm (Fin d))) T).weight h := by
  obtain ⟨π₀, hπ₀⟩ := h.property
  have hh : reachableHistoryOf strategy (concreteOracle d rho) T π₀ = h := Subtype.ext hπ₀
  rw [← hh]
  apply FinitePMF.history_mass_pos
  change 0 < (1 : ℝ)/(Fintype.card (Equiv.Perm (Fin d)) : ℝ)
  exact div_pos (by norm_num) card_cast_pos

theorem numerical_uniform_conditional_average
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T)
    (X : Equiv.Perm (Fin d) → ℝ) :
    (FinitePMF.uniform (Equiv.Perm (Fin d))).fiberContribution
      (reachableHistoryOf strategy (concreteOracle d rho) T) X h /
      (reachableHistoryLaw strategy (concreteOracle d rho)
        (FinitePMF.uniform (Equiv.Perm (Fin d))) T).weight h =
          uniformAverage (fun π : (numericalTranscriptConstraint strategy h.val).Realizations => X π.val) := by
  rw [numerical_uniform_posterior]
  exact mul_div_cancel_left₀ _ (numerical_posterior_mass_pos strategy rho T h).ne'

end Lemmata.DistributionalLowerBounds.Core.Distributional
