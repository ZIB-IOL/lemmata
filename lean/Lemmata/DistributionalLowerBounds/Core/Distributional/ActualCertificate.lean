module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.PosteriorEdges

@[expose] public section

/-! Constructing the adaptive certificate from actual numerical histories. -/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
namespace RankConstraint
variable {d : ℕ} (S : RankConstraint d)

lemma remaining_refine_le (A : RankDisclosure d) : (A.refine S).remaining ≤ S.remaining := by
  apply Finset.card_le_card
  intro i hi
  rw [mem_freeRows] at hi ⊢
  by_cases ha : i ∈ A.active
  · simp [RankDisclosure.refine, ha] at hi
  · simpa [RankDisclosure.refine, ha] using hi

lemma deficit_congr {R : RankConstraint d} (hS : Nonempty S.Realizations)
    (hR : Nonempty R.Realizations) (he : S=R) : S.deficit hS = R.deficit hR := by
  subst R
  rfl

noncomputable def after (p : Fin d → ℝ) (π : S.Realizations) : RankConstraint d :=
  (numericalDisclosure d p (concreteLMO d π.val p)).refine S

lemma after_nonempty (p : Fin d → ℝ) (π : S.Realizations) : Nonempty (S.after p π).Realizations :=
  ⟨⟨π.val,(numerical_refine_compatible_iff S π.val π.val p).mpr ⟨π.property,rfl⟩⟩⟩

noncomputable def afterDeficit (p : Fin d → ℝ) (π : S.Realizations) : ℝ :=
  (S.after p π).deficit (S.after_nonempty p π)

noncomputable def progressNode (hS : Nonempty S.Realizations) (p : Fin d → ℝ) : HistoryNode d :=
  if hm : 0 < S.remaining then
    if hp : ∃ i, p i ≠ 0 then
      .active S.remaining (S.reducedData hS) hm S.remaining_le (S.waterQuery hS p hp)
    else .resolved
  else .resolved

/-- Zero local progress does NOT redefine the posterior deficit as zero. -/
lemma progressNode_drop (hS : Nonempty S.Realizations) (p : Fin d → ℝ) :
    (S.progressNode hS p).localDrop =
      uniformAverage (fun σ : FerrersPerm (S.reducedData hS) =>
        S.deficit hS - S.afterDeficit p ((S.ferrersEquiv hS).symm σ)) := by
  classical
  by_cases hm : 0 < S.remaining
  · by_cases hp : ∃ i, p i ≠ 0
    · simp only [progressNode, dif_pos hm, dif_pos hp, HistoryNode.localDrop]
      congr 1
      funext σ
      have he := S.internalOutdegree_eq_refined_deficit hS p hp ((S.ferrersEquiv hS).symm σ)
      rw [Equiv.apply_symm_apply] at he
      rw [he]
      rfl
    · have hp0 : p=0 := by push Not at hp; funext i; exact hp i
      subst p
      have ha : ∀ π : S.Realizations, S.after 0 π = S := by
        intro π
        simp only [after, concreteLMO_zero, numericalDisclosure_zero_refine]
      have hd : ∀ π : S.Realizations, S.afterDeficit 0 π = S.deficit hS := by
        intro π
        exact (S.after 0 π).deficit_congr _ _ (ha π)
      simp only [progressNode, dif_pos hm, dif_neg hp, HistoryNode.localDrop, hd, sub_self,
        uniformAverage, Finset.sum_const_zero, zero_div]
  · have hm0 : S.remaining=0 := by omega
    have ha : ∀ π : S.Realizations, S.afterDeficit p π = 0 := by
      intro π
      apply RankConstraint.deficit_zero_of_remaining_zero
      have hh := S.remaining_refine_le (numericalDisclosure d p (concreteLMO d π.val p))
      change (S.after p π).remaining ≤ S.remaining at hh
      omega
    simp only [progressNode, dif_neg hm, HistoryNode.localDrop, S.deficit_zero_of_remaining_zero hS hm0,
      ha, sub_self, uniformAverage, Finset.sum_const_zero, zero_div]

end RankConstraint

variable {d : ℕ} {Output : Type}
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (t : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) t)

lemma numericalDeficit_at_history
    (π : (numericalTranscriptConstraint strategy h.val).Realizations) :
    numericalDeficit strategy rho t π.val =
      (numericalTranscriptConstraint strategy h.val).deficit (numericalPosterior_nonempty strategy rho t h) := by
  apply RankConstraint.deficit_congr
  have he := (reachable_numerical_constraint_iff strategy rho t h π.val).mp π.property
  exact congrArg (numericalTranscriptConstraint strategy) (congrArg Subtype.val he)

lemma numericalDeficit_next_history
    (π : (numericalTranscriptConstraint strategy h.val).Realizations) :
    numericalDeficit strategy rho (t+1) π.val =
      (numericalTranscriptConstraint strategy h.val).afterDeficit
        (strategy.nextQuery t h.val).2 π := by
  apply RankConstraint.deficit_congr
  have he := (reachable_numerical_constraint_iff strategy rho t h π.val).mp π.property
  have ht := congrArg Subtype.val he
  change strategy.transcript (concreteOracle d rho) π.val t = h.val at ht
  have hlen : h.val.length=t := by
    rw [← ht]
    exact strategy.transcript_length _ _ _
  change numericalTranscriptConstraint strategy (strategy.transcript _ π.val (t+1)) = _
  rw [DeterministicAdaptiveStrategy.transcript_succ, ht, numericalTranscriptConstraint_snoc, hlen]
  rfl

/-- No certificate, posterior law, drop identity, or deficit is supplied by the
caller. The old `CertifiedStrategy` interface is instantiated rather than changed. -/
noncomputable def actualCertifiedStrategy (T : ℕ) :
    CertifiedStrategy d T (FinitePMF.uniform (Equiv.Perm (Fin d))) strategy
      (concreteOracle d rho) (numericalDeficit strategy rho) where
  node t h := (numericalTranscriptConstraint strategy h.val).progressNode
    (numericalPosterior_nonempty strategy rho t.val h) (strategy.nextQuery t.val h.val).2
  drop_identity t h := by
    rw [numerical_uniform_reduced_posterior]
    rw [RankConstraint.progressNode_drop]
    congr 1
    congr 1
    funext σ
    rw [numericalDeficit_at_history strategy rho t.val h,
      numericalDeficit_next_history strategy rho t.val h]

end Lemmata.DistributionalLowerBounds.Core.Distributional
