module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.PosteriorLoss

@[expose] public section

/-! Actual nonzero queries on a constructed reduced posterior. Known-coordinate
contributions are retained; neither the query profile nor its root is assumed. -/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
namespace RankConstraint

variable {d : ℕ} (S : RankConstraint d) (hS : Nonempty S.Realizations)

noncomputable def knownProfile (p : Fin d → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i ∉ S.freeRows),
    max 0 (t*p i^2-permutedRank hS.some.val i)

lemma knownProfile_nonneg (p : Fin d → ℝ) (t : ℝ) : 0 ≤ S.knownProfile hS p t :=
  Finset.sum_nonneg (fun _ _ => le_max_left _ _)

lemma knownProfile_mono (p : Fin d → ℝ) : Monotone (S.knownProfile hS p) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro i _
  apply max_le_max_left
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right hab (sq_nonneg _)) _

lemma profile_split (p : Fin d → ℝ) (π : S.Realizations) (t : ℝ) :
    waterProfile p (permutedRank π.val) t = S.knownProfile hS p t +
      ∑ i, max 0 (t*(p (S.rowEnum i))^2-(S.rank hS (S.restrict hS π i) : ℝ)) := by
  simp_rw [show ∀ i, (S.rank hS (S.restrict hS π i) : ℝ) =
    permutedRank π.val (S.rowEnum i) by intro i; simp [rank, permutedRank]]
  rw [S.sum_free (fun i => max 0 (t*p i^2-permutedRank π.val i))]
  have hf : (∑ i ∈ Finset.univ.filter (fun i => i ∉ S.freeRows),
      max 0 (t*p i^2-permutedRank π.val i)) = S.knownProfile hS p t := by
    apply Finset.sum_congr rfl
    intro i hi
    have hfix := S.fixed_agree π hS.some (Finset.mem_filter.mp hi).2
    simp only [permutedRank, hfix]
  have he := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => i ∈ S.freeRows) (fun i => max 0 (t*p i^2-permutedRank π.val i))
  have hs : Finset.univ.filter (fun i => i ∈ S.freeRows) = S.freeRows := by ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hs, hf] at he
  exact he.symm.trans (add_comm _ _)

noncomputable def queryTau (p : Fin d → ℝ) (σ : FerrersPerm (S.reducedData hS)) : ℝ :=
  (waterInverse (permutedRank ((S.ferrersEquiv hS).symm σ).val) p)⁻¹

lemma queryTau_spec (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0)
    (σ : FerrersPerm (S.reducedData hS)) :
    0 < S.queryTau hS p σ ∧
      S.knownProfile hS p (S.queryTau hS p σ) +
        ∑ i, max 0 (S.queryTau hS p σ*(p (S.rowEnum i))^2-(S.rank hS (σ.val i) : ℝ)) = 1 := by
  have h := waterInverse_inv_spec p (permutedRank ((S.ferrersEquiv hS).symm σ).val)
    (fun i => by dsimp [permutedRank]; positivity) hp
  refine ⟨h.1, ?_⟩
  rw [S.profile_split hS] at h
  have hr : S.restrict hS ((S.ferrersEquiv hS).symm σ) = σ.val :=
    congrArg Subtype.val ((S.ferrersEquiv hS).apply_symm_apply σ)
  simpa [queryTau, hr] using h.2

lemma reduced_profile (p : Fin d → ℝ) (σ : FerrersPerm (S.reducedData hS)) (t : ℝ) :
    S.knownProfile hS p t + ∑ i, max 0 (t*(p (S.rowEnum i))^2-(S.rank hS (σ.val i) : ℝ)) =
      waterProfile p (permutedRank ((S.ferrersEquiv hS).symm σ).val) t := by
  rw [S.profile_split hS]
  have hr : S.restrict hS ((S.ferrersEquiv hS).symm σ) = σ.val :=
    congrArg Subtype.val ((S.ferrersEquiv hS).apply_symm_apply σ)
  rw [hr]

/-- No query-certificate fields are supplied by the caller. A nonzero direction
may be supported entirely on already known coordinates. -/
noncomputable def waterQuery (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0) :
    QueryRanks.WaterQuery (S.reducedData hS) :=
  QueryRanks.WaterQuery.ofWater (S.rank hS) (S.rank_pos hS) (S.rank_strict hS)
    (fun i => (p (S.rowEnum i))^2) (fun _ => sq_nonneg _)
    (S.knownProfile hS p) (S.knownProfile_mono hS p) (S.knownProfile_nonneg hS p)
    (S.queryTau hS p) (fun σ => (S.queryTau_spec hS p hp σ).2)
    (by
      intro σ t ht
      rw [S.reduced_profile hS]
      have hr := waterInverse_inv_spec p (permutedRank ((S.ferrersEquiv hS).symm σ).val)
        (fun i => by dsimp [permutedRank]; positivity) hp
      by_contra hn
      have hpos : 0 < waterProfile p (permutedRank ((S.ferrersEquiv hS).symm σ).val) t := by linarith
      have hs := waterProfile_strict_of_pos p _ (fun i => by dsimp [permutedRank]; positivity) ht hpos
      dsimp only [queryTau] at hs
      linarith [hr.2])
    (by
      intro σ t ht
      rw [S.reduced_profile hS] at ht
      have hr := waterInverse_inv_spec p (permutedRank ((S.ferrersEquiv hS).symm σ).val)
        (fun i => by dsimp [permutedRank]; positivity) hp
      by_contra hn
      have hlt : S.queryTau hS p σ < t := lt_of_not_ge hn
      have hs := waterProfile_strict_of_pos p (permutedRank ((S.ferrersEquiv hS).symm σ).val)
        (fun i => by dsimp [permutedRank]; positivity)
        hlt (by dsimp only [queryTau]; rw [hr.2]; norm_num)
      dsimp only [queryTau] at hs
      linarith [hr.2])

lemma query_decodedMultiplier (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0)
    (σ : FerrersPerm (S.reducedData hS)) :
    decodedMultiplier (hardC d) p (concreteLMO d ((S.ferrersEquiv hS).symm σ).val p) =
      multiplierOfTau (hardC d) (S.queryTau hS p σ) := by
  apply decodedMultiplier_soft p _ (hardC_pos d)
    (multiplierOfTau_pos (hardC_pos d) (S.queryTau_spec hS p hp σ).1)
  exact (concreteLMO_decoded_spec ((S.ferrersEquiv hS).symm σ).val p hp).2.2

lemma query_decodedTau (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0)
    (σ : FerrersPerm (S.reducedData hS)) :
    waterTau (hardC d) (decodedMultiplier (hardC d) p
      (concreteLMO d ((S.ferrersEquiv hS).symm σ).val p)) = S.queryTau hS p σ := by
  rw [S.query_decodedMultiplier hS p hp]
  exact waterTau_multiplierOfTau (hardC_pos d) (S.queryTau_spec hS p hp σ).1

lemma query_zero_iff (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0)
    (σ : FerrersPerm (S.reducedData hS)) (i : Fin S.remaining) :
    concreteLMO d ((S.ferrersEquiv hS).symm σ).val p (S.rowEnum i) = 0 ↔
      S.queryTau hS p σ*(p (S.rowEnum i))^2 ≤ (S.rank hS (σ.val i) : ℝ) := by
  let π := ((S.ferrersEquiv hS).symm σ).val
  have hs := concreteLMO_decoded_spec π p hp
  have hr : permutedRank π (S.rowEnum i) = (S.rank hS (σ.val i) : ℝ) := by
    dsimp [π, permutedRank]
    rw [S.ferrersEquiv_symm_rank]
    rfl
  rw [hs.2.1 (S.rowEnum i), softCoordinate_zero_iff]
  constructor
  · intro hi
    have h := inactive_water_level_le_rank (hardC_pos d) hs.1
      (permutedHardWeight_sq_rank π _) hi (hardWeight_nonneg d (π (S.rowEnum i)))
    rw [S.query_decodedTau hS p hp, hr] at h
    exact h
  · intro hi
    apply inactive_of_waterTau_le (hardC_pos d) hs.1
      (hardWeight_nonneg d (π (S.rowEnum i))) (permutedHardWeight_sq_rank π _)
    rw [S.query_decodedTau hS p hp, hr]
    exact hi

lemma query_soft (p : Fin d → ℝ) (σ : FerrersPerm (S.reducedData hS)) (i : Fin d) :
    concreteLMO d ((S.ferrersEquiv hS).symm σ).val p i =
      softCoordinate (p i) (permutedHardWeight d ((S.ferrersEquiv hS).symm σ).val i)
        (multiplierOfTau (hardC d) (S.queryTau hS p σ)) := rfl

/-- The constructed water-answer partition is EXACTLY the numerical partition,
not merely a more informative disclosure. -/
theorem water_answer_iff (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0)
    (σ τ : FerrersPerm (S.reducedData hS)) :
    (S.waterQuery hS p hp).answer σ = (S.waterQuery hS p hp).answer τ ↔
      concreteLMO d ((S.ferrersEquiv hS).symm σ).val p =
        concreteLMO d ((S.ferrersEquiv hS).symm τ).val p := by
  constructor
  · intro he
    have ht := congrArg QueryRanks.WaterQuery.Answer.tau he
    change S.queryTau hS p σ = S.queryTau hS p τ at ht
    funext j
    by_cases hj : j ∈ S.freeRows
    · let i := S.rowEnum.symm ⟨j,hj⟩
      have hi : (S.rowEnum i).val = j := by simp [i]
      have ha := congrFun (congrArg QueryRanks.WaterQuery.Answer.activeRank he) i
      change (if (S.rank hS (σ.val i) : ℝ) < S.queryTau hS p σ*(p (S.rowEnum i))^2 then
        some (σ.val i) else none) =
        (if (S.rank hS (τ.val i) : ℝ) < S.queryTau hS p τ*(p (S.rowEnum i))^2 then
        some (τ.val i) else none) at ha
      by_cases hs : (S.rank hS (σ.val i) : ℝ) < S.queryTau hS p σ*(p (S.rowEnum i))^2
      · by_cases hτ : (S.rank hS (τ.val i) : ℝ) < S.queryTau hS p τ*(p (S.rowEnum i))^2
        · have hv : σ.val i = τ.val i := by simpa only [if_pos hs, if_pos hτ, Option.some.injEq] using ha
          rw [← hi, S.query_soft hS, S.query_soft hS, ht]
          congr 1
          simp only [permutedHardWeight, S.ferrersEquiv_symm_rank hS, hv]
        · simp [hs,hτ] at ha
      · have hτ : ¬ (S.rank hS (τ.val i) : ℝ) < S.queryTau hS p τ*(p (S.rowEnum i))^2 := by
          intro hτ
          simp [hs,hτ] at ha
        rw [← hi, (S.query_zero_iff hS p hp σ i).mpr (le_of_not_gt hs),
          (S.query_zero_iff hS p hp τ i).mpr (le_of_not_gt hτ)]
    · rw [S.query_soft hS, S.query_soft hS, ht]
      congr 1
      unfold permutedHardWeight
      rw [S.fixed_agree ((S.ferrersEquiv hS).symm σ) ((S.ferrersEquiv hS).symm τ) hj]
  · intro he
    have ht : S.queryTau hS p σ = S.queryTau hS p τ := by
      rw [← S.query_decodedTau hS p hp σ, ← S.query_decodedTau hS p hp τ, he]
    apply QueryRanks.WaterQuery.Answer.eq_of_fields ht
    · funext i
      change (if (S.rank hS (σ.val i) : ℝ) < S.queryTau hS p σ*(p (S.rowEnum i))^2 then
        some (σ.val i) else none) =
        (if (S.rank hS (τ.val i) : ℝ) < S.queryTau hS p τ*(p (S.rowEnum i))^2 then
        some (τ.val i) else none)
      have hz := congrFun he (S.rowEnum i)
      have hs0 := S.query_zero_iff hS p hp σ i
      have ht0 := S.query_zero_iff hS p hp τ i
      by_cases hs : (S.rank hS (σ.val i) : ℝ) < S.queryTau hS p σ*(p (S.rowEnum i))^2
      · have hnon : concreteLMO d ((S.ferrersEquiv hS).symm σ).val p (S.rowEnum i) ≠ 0 :=
          fun h => (not_le_of_gt hs) (hs0.mp h)
        have hτ : (S.rank hS (τ.val i) : ℝ) < S.queryTau hS p τ*(p (S.rowEnum i))^2 := by
          by_contra h
          exact hnon (hz.trans (ht0.mpr (le_of_not_gt h)))
        have hsr := decoded_activeRank_eq ((S.ferrersEquiv hS).symm σ).val p hp (S.rowEnum i) hnon
        have htr := decoded_activeRank_eq ((S.ferrersEquiv hS).symm τ).val p hp (S.rowEnum i)
          (fun h => hnon (hz.trans h))
        rw [he] at hsr
        have hv : σ.val i = τ.val i := by
          apply (S.rankOrder hS).injective
          apply Subtype.ext
          rw [← S.ferrersEquiv_symm_rank hS, ← S.ferrersEquiv_symm_rank hS]
          exact hsr.symm.trans htr
        rw [if_pos hs, if_pos hτ, hv]
      · have hτ : ¬ (S.rank hS (τ.val i) : ℝ) < S.queryTau hS p τ*(p (S.rowEnum i))^2 := by
          intro h
          exact (not_le_of_gt h) (ht0.mp (hz.symm.trans (hs0.mpr (le_of_not_gt hs))))
        simp only [if_neg hs, if_neg hτ]
    · change (fun i => Nat.ceil (S.queryTau hS p σ*(p (S.rowEnum i))^2)) =
        (fun i => Nat.ceil (S.queryTau hS p τ*(p (S.rowEnum i))^2))
      rw [ht]

end RankConstraint
end Lemmata.DistributionalLowerBounds.Core.Distributional
