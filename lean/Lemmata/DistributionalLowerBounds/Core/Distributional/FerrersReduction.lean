module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.NumericalTranscript
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Removing fixed ranks and constructing the reduced Ferrers posterior

Rows, remaining ranks, and their orderings are computed from the constraint
state, not from an undisclosed permutation. A compatible witness is used to
prove feasibility and to fill ALREADY FIXED coordinates. Restriction and
completion are inverse maps, including zero or one remaining coordinate.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
namespace RankConstraint

variable {d : ℕ} (S : RankConstraint d)

def freeRows : Finset (Fin d) := Finset.univ.filter (fun i => S.exactRanks i = ∅)
def freeRanks : Finset (Fin d) := Finset.univ.filter (fun r => ∀ i, r ∉ S.exactRanks i)
def remaining : ℕ := S.freeRows.card

@[simp] lemma mem_freeRows (i : Fin d) : i ∈ S.freeRows ↔ S.exactRanks i = ∅ := by
  simp [freeRows]
@[simp] lemma mem_freeRanks (r : Fin d) : r ∈ S.freeRanks ↔ ∀ i, r ∉ S.exactRanks i := by
  simp [freeRanks]

lemma fixed_agree (π σ : S.Realizations) {i : Fin d} (hi : i ∉ S.freeRows) :
    π.val i = σ.val i := by
  have hn : (S.exactRanks i).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hi)
  obtain ⟨r, hr⟩ := hn
  exact ((π.property i).1 r hr).trans ((σ.property i).1 r hr).symm

lemma free_iff (π : S.Realizations) (i : Fin d) :
    i ∈ S.freeRows ↔ π.val i ∈ S.freeRanks := by
  rw [mem_freeRows, mem_freeRanks]
  constructor
  · intro hi j hj
    have hji : j = i := π.val.injective ((π.property j).1 _ hj)
    subst j
    simp [hi] at hj
  · intro hi
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have he := (π.property i).1 r hr
    exact hi i (he.symm ▸ hr)

/-- Restrict a full compatible permutation to the unassigned rows and ranks. -/
noncomputable def freeEquiv (π : S.Realizations) : S.freeRows ≃ S.freeRanks :=
  π.val.subtypeEquiv (fun i => S.free_iff π i)

lemma freeRanks_card (hS : Nonempty S.Realizations) : S.freeRanks.card = S.remaining := by
  obtain ⟨π⟩ := hS
  simpa only [remaining, Fintype.card_coe] using (Fintype.card_congr (S.freeEquiv π)).symm

/-- Increasing original-coordinate enumeration, before stable sorting. -/
noncomputable def rowOrder : Fin S.remaining ≃o S.freeRows :=
  S.freeRows.orderIsoOfFin rfl

/-- Increasing enumeration of the ORIGINAL remaining ranks (gaps retained). -/
noncomputable def rankOrder (hS : Nonempty S.Realizations) : Fin S.remaining ≃o S.freeRanks :=
  S.freeRanks.orderIsoOfFin (S.freeRanks_card hS)

noncomputable def rawLower : Fin S.remaining → ℕ := fun i => S.lowerRank (S.rowOrder i)

/-- Compress raw bounds BEFORE sorting: deleted ranks must not influence ties. -/
noncomputable def baseLower (i : Fin S.remaining) : ℕ :=
  (S.freeRanks.filter (fun r => r.val+1 < S.rawLower i)).card

/-- Stable increasing compressed-bound sort, breaking ties by original coordinate. -/
noncomputable def rowEnum : Fin S.remaining ≃ S.freeRows :=
  (Tuple.sort S.baseLower).trans S.rowOrder.toEquiv

noncomputable def rank (hS : Nonempty S.Realizations) (a : Fin S.remaining) : ℕ :=
  (S.rankOrder hS a).val.val + 1

lemma rank_pos (hS : Nonempty S.Realizations) (a : Fin S.remaining) : 0 < S.rank hS a := by
  unfold rank
  omega

lemma rank_strict (hS : Nonempty S.Realizations) : StrictMono (S.rank hS) := by
  intro i j hij
  have h := (S.rankOrder hS).strictMono hij
  change (S.rankOrder hS i).val.val < (S.rankOrder hS j).val.val at h
  dsimp [rank]
  omega

lemma rank_le (hS : Nonempty S.Realizations) (a : Fin S.remaining) : S.rank hS a ≤ d := by
  have h := (S.rankOrder hS a).val.isLt
  dsimp [rank]
  omega

/-- Zero-based suffix threshold: count REMAINING ranks below the raw bound. -/
noncomputable def reducedLower (hS : Nonempty S.Realizations) (i : Fin S.remaining) : ℕ :=
  (Finset.univ.filter (fun a => S.rank hS a < S.lowerRank (S.rowEnum i))).card

lemma reducedLower_le_iff (hS : Nonempty S.Realizations) (i a : Fin S.remaining) :
    S.reducedLower hS i ≤ a.val ↔ S.lowerRank (S.rowEnum i) ≤ S.rank hS a := by
  have h := Tuple.lt_card_lt_iff_apply_lt_of_monotone
    (f := S.rank hS) (j := a) (a := S.lowerRank (S.rowEnum i)) (S.rank_strict hS).monotone
  change a.val < S.reducedLower hS i ↔ S.rank hS a < S.lowerRank (S.rowEnum i) at h
  omega

lemma reducedLower_eq_baseLower (hS : Nonempty S.Realizations) (i : Fin S.remaining) :
    S.reducedLower hS i = S.baseLower (Tuple.sort S.baseLower i) := by
  unfold reducedLower baseLower
  apply Finset.card_bij (fun a _ => (S.rankOrder hS a).val)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(S.rankOrder hS a).property, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ he
    exact (S.rankOrder hS).injective (Subtype.ext he)
  · intro r hr
    let a := (S.rankOrder hS).symm ⟨r,(Finset.mem_filter.mp hr).1⟩
    have he : (S.rankOrder hS a).val = r := by simp [a]
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    change (S.rankOrder hS a).val.val+1 < _
    rw [he]
    exact (Finset.mem_filter.mp hr).2

lemma reducedLower_monotone (hS : Nonempty S.Realizations) : Monotone (S.reducedLower hS) := by
  intro i j hij
  simp only [reducedLower_eq_baseLower]
  exact Tuple.monotone_sort S.baseLower hij

lemma rowEnum_tie (hS : Nonempty S.Realizations) (i j : Fin S.remaining) (hij : i < j)
    (he : S.reducedLower hS i = S.reducedLower hS j) :
    (S.rowEnum i).val < (S.rowEnum j).val := by
  simp only [reducedLower_eq_baseLower] at he
  have ht := (Tuple.eq_sort_iff.mp (rfl : Tuple.sort S.baseLower = Tuple.sort S.baseLower)).2 i j hij he
  exact S.rowOrder.strictMono ht

/-- Restriction with both the row sort and the gapped rank enumeration. -/
noncomputable def restrict (hS : Nonempty S.Realizations) (π : S.Realizations) :
    Equiv.Perm (Fin S.remaining) :=
  S.rowEnum.trans ((S.freeEquiv π).trans (S.rankOrder hS).toEquiv.symm)

@[simp] lemma restrict_rankOrder (hS : Nonempty S.Realizations) (π : S.Realizations)
    (i : Fin S.remaining) :
    (S.rankOrder hS (S.restrict hS π i)).val = π.val (S.rowEnum i) := by
  simp [restrict, freeEquiv]

lemma restrict_compatible (hS : Nonempty S.Realizations) (π : S.Realizations)
    (i : Fin S.remaining) : S.reducedLower hS i ≤ (S.restrict hS π i).val := by
  rw [S.reducedLower_le_iff]
  simpa [rank] using (π.property (S.rowEnum i)).2

/-- The board is constructed; its Hall feasibility follows from a compatible
witness. The witness does not determine either enumeration or lower bounds. -/
noncomputable def reducedData (hS : Nonempty S.Realizations) : FerrersData S.remaining :=
  FerrersData.ofCompatible (S.reducedLower hS) (S.reducedLower_monotone hS)
    (S.restrict hS hS.some) (S.restrict_compatible hS hS.some)

/-- Complete a reduced permutation. The witness supplies only already fixed
coordinates, on which ALL compatible permutations agree. -/
noncomputable def completePerm (hS : Nonempty S.Realizations)
    (σ : Equiv.Perm (Fin S.remaining)) : Equiv.Perm (Fin d) where
  toFun i := if hi : i ∈ S.freeRows then
      (S.rankOrder hS (σ (S.rowEnum.symm ⟨i, hi⟩))).val else hS.some.val i
  invFun r := if hr : r ∈ S.freeRanks then
      (S.rowEnum (σ.symm ((S.rankOrder hS).symm ⟨r, hr⟩))).val else hS.some.val.symm r
  left_inv i := by
    dsimp only
    by_cases hi : i ∈ S.freeRows
    · rw [dif_pos hi, dif_pos (S.rankOrder hS _).property]
      simp
    · have hr : hS.some.val i ∉ S.freeRanks := mt (S.free_iff hS.some i).mpr hi
      rw [dif_neg hi, dif_neg hr]
      simp
  right_inv r := by
    dsimp only
    by_cases hr : r ∈ S.freeRanks
    · rw [dif_pos hr, dif_pos (S.rowEnum _).property]
      simp
    · have hi : hS.some.val.symm r ∉ S.freeRows := by
        intro hi
        apply hr
        simpa only [Equiv.apply_symm_apply] using (S.free_iff hS.some _).mp hi
      rw [dif_neg hr, dif_neg hi]
      simp

@[simp] lemma completePerm_row (hS : Nonempty S.Realizations)
    (σ : Equiv.Perm (Fin S.remaining)) (i : Fin S.remaining) :
    S.completePerm hS σ (S.rowEnum i) = (S.rankOrder hS (σ i)).val := by
  simp only [completePerm, Equiv.coe_fn_mk, dif_pos (S.rowEnum i).property]
  simp

lemma completePerm_fixed (hS : Nonempty S.Realizations)
    (σ : Equiv.Perm (Fin S.remaining)) (i : Fin d) (hi : i ∉ S.freeRows) :
    S.completePerm hS σ i = hS.some.val i := by
  simp only [completePerm, Equiv.coe_fn_mk, dif_neg hi]

lemma complete_compatible (hS : Nonempty S.Realizations) (σ : FerrersPerm (S.reducedData hS)) :
    S.Compatible (S.completePerm hS σ.val) := by
  intro i
  by_cases hi : i ∈ S.freeRows
  · let j := S.rowEnum.symm ⟨i, hi⟩
    have hj : (S.rowEnum j).val = i := by simp [j]
    have hlo := (S.reducedLower_le_iff hS j (σ.val j)).mp (σ.property j)
    constructor
    · intro r hr
      have he := (S.mem_freeRows i).mp hi
      simp [he] at hr
    · rw [← hj, S.completePerm_row]
      simpa [rank] using hlo
  · rw [S.completePerm_fixed hS σ.val i hi]
    exact hS.some.property i

/-- The concrete full-to-reduced bijection, not an assumed cardinal identity. -/
noncomputable def ferrersEquiv (hS : Nonempty S.Realizations) :
    S.Realizations ≃ FerrersPerm (S.reducedData hS) where
  toFun π := ⟨S.restrict hS π, S.restrict_compatible hS π⟩
  invFun σ := ⟨S.completePerm hS σ.val, S.complete_compatible hS σ⟩
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ S.freeRows
    · let j := S.rowEnum.symm ⟨i, hi⟩
      have hj : (S.rowEnum j).val = i := by simp [j]
      rw [← hj, S.completePerm_row, S.restrict_rankOrder]
    · rw [S.completePerm_fixed hS _ i hi]
      exact S.fixed_agree hS.some π hi
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply (S.rankOrder hS).injective
    apply Subtype.ext
    rw [S.restrict_rankOrder, S.completePerm_row]

/-- Assigned ORIGINAL ranks are preserved, not replaced by consecutive ranks. -/
lemma ferrersEquiv_rank (hS : Nonempty S.Realizations) (π : S.Realizations)
    (i : Fin S.remaining) :
    S.rank hS ((S.ferrersEquiv hS π).val i) = (π.val (S.rowEnum i)).val + 1 := by
  change S.rank hS (S.restrict hS π i) = _
  simp [rank]

lemma ferrersEquiv_symm_rank (hS : Nonempty S.Realizations)
    (σ : FerrersPerm (S.reducedData hS)) (i : Fin S.remaining) :
    ((S.ferrersEquiv hS).symm σ).val (S.rowEnum i) = (S.rankOrder hS (σ.val i)).val :=
  S.completePerm_row hS σ.val i

lemma remaining_le : S.remaining ≤ d := by
  exact (Finset.card_le_univ S.freeRows).trans_eq (Fintype.card_fin d)

lemma realizations_card (hS : Nonempty S.Realizations) :
    Fintype.card S.Realizations = ∏ i, (S.reducedData hS).choices i := by
  rw [Fintype.card_congr (S.ferrersEquiv hS), FerrersPerm.card_eq_prod_choices]

lemma uniformAverage_reduced (hS : Nonempty S.Realizations) (X : S.Realizations → ℝ) :
    uniformAverage X = uniformAverage (fun σ => X ((S.ferrersEquiv hS).symm σ)) := by
  symm
  exact uniformAverage_comp_equiv (S.ferrersEquiv hS).symm X

lemma sum_free {M : Type*} [AddCommMonoid M] (f : Fin d → M) :
    (∑ i : Fin S.remaining, f (S.rowEnum i)) = ∑ i ∈ S.freeRows, f i := by
  rw [Finset.sum_subtype S.freeRows (fun _ => Iff.rfl)]
  exact Equiv.sum_comp S.rowEnum (fun i => f i.val)

lemma rank_gap (hS : Nonempty S.Realizations) (i j : Fin S.remaining) :
    |(i.val : ℝ) - j.val| ≤ |(S.rank hS i : ℝ) - S.rank hS j| := by
  have hordered : ∀ a b : Fin S.remaining, a ≤ b →
      b.val + S.rank hS a ≤ S.rank hS b + a.val := by
    intro a b hab
    let f : Set.Ico a b → Set.Ico (S.rank hS a) (S.rank hS b) := fun k =>
      ⟨S.rank hS k.val, (S.rank_strict hS).monotone k.property.1,
        (S.rank_strict hS) k.property.2⟩
    have hinj : Function.Injective f := by
      intro x y he
      exact Subtype.ext ((S.rank_strict hS).injective (congrArg Subtype.val he))
    have hc := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_Ico, Fin.card_Ico, Nat.card_Ico] at hc
    have hm := (S.rank_strict hS).monotone hab
    change a.val ≤ b.val at hab
    omega
  rcases le_total i j with hij | hji
  · have h := hordered i j hij
    have hn : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
    have hr : (S.rank hS i : ℝ) ≤ S.rank hS j := by exact_mod_cast (S.rank_strict hS).monotone hij
    have h' : (j.val : ℝ) + S.rank hS i ≤ S.rank hS j + i.val := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr hn), abs_of_nonpos (sub_nonpos.mpr hr)]
    linarith
  · have h := hordered j i hji
    have hn : (j.val : ℝ) ≤ i.val := by exact_mod_cast hji
    have hr : (S.rank hS j : ℝ) ≤ S.rank hS i := by exact_mod_cast (S.rank_strict hS).monotone hji
    have h' : (i.val : ℝ) + S.rank hS j ≤ S.rank hS i + j.val := by exact_mod_cast h
    rw [abs_of_nonneg (sub_nonneg.mpr hn), abs_of_nonneg (sub_nonneg.mpr hr)]
    linarith

/-- A posterior statistic, not a next-query progress node. -/
noncomputable def deficit (hS : Nonempty S.Realizations) : ℝ :=
  DownEdge.natDeficit (S.reducedData hS)

lemma deficit_nonneg (hS : Nonempty S.Realizations) : 0 ≤ S.deficit hS := by
  unfold deficit
  positivity

lemma deficit_le_initial (hS : Nonempty S.Realizations) : S.deficit hS ≤ initialDeficit d :=
  (DownEdge.natDeficit_le_initial (S.reducedData hS)).trans (initialDeficit_mono S.remaining_le)

lemma deficit_eq_sum (hS : Nonempty S.Realizations) :
    S.deficit hS = ∑ i, (((S.reducedData hS).choices i : ℝ) - 1) := by
  rw [deficit, DownEdge.natDeficit, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub (Nat.succ_le_iff.mpr ((S.reducedData hS).choices_pos i)), Nat.cast_one]

lemma deficit_zero_of_remaining_zero (hS : Nonempty S.Realizations) (hm : S.remaining = 0) :
    S.deficit hS = 0 := by
  haveI : IsEmpty (Fin S.remaining) := ⟨fun i => by have := i.isLt; omega⟩
  simp [deficit, DownEdge.natDeficit]

@[simp] lemma empty_remaining : (empty d).remaining = d := by
  simp [remaining, freeRows, empty]

lemma empty_reducedLower (hS : Nonempty (empty d).Realizations)
    (i : Fin (empty d).remaining) : (empty d).reducedLower hS i = 0 := by
  change (Finset.univ.filter (fun a => (empty d).rank hS a < 1)).card = 0
  have he : Finset.univ.filter (fun a => (empty d).rank hS a < 1) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _
    have := (empty d).rank_pos hS a
    omega
  rw [he, Finset.card_empty]

lemma empty_deficit (hS : Nonempty (empty d).Realizations) :
    (empty d).deficit hS = initialDeficit d := by
  rw [deficit, DownEdge.natDeficit_eq, Nat.cast_sum]
  have hz : ∀ i, ((empty d).reducedData hS).lower i = 0 := empty_reducedLower hS
  simp_rw [hz, Nat.sub_zero]
  simpa only [empty_remaining, initialDeficit] using sum_fin_val (empty d).remaining

end RankConstraint

/-- Actual reachable numerical histories now determine the reduced Ferrers
posterior, without a separately supplied bijection or posterior identity. -/
noncomputable def numericalFerrersEquiv {d : ℕ} {Output : Type}
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T) :
    {π // reachableHistoryOf strategy (concreteOracle d rho) T π = h} ≃
      FerrersPerm ((numericalTranscriptConstraint strategy h.val).reducedData
        (numericalPosterior_nonempty strategy rho T h)) :=
  (numericalPosteriorEquiv strategy rho T h).trans
    ((numericalTranscriptConstraint strategy h.val).ferrersEquiv
      (numericalPosterior_nonempty strategy rho T h))

/-- Mass-weighted actual numerical conditioning in the reduced model. -/
theorem numerical_uniform_reduced_posterior {d : ℕ} {Output : Type}
    (strategy : DeterministicAdaptiveStrategy (PairedQuery d) (PairedAnswer d) Output)
    (rho : ℝ) (T : ℕ) (h : ReachableHistory strategy (concreteOracle d rho) T)
    (X : Equiv.Perm (Fin d) → ℝ) :
    let S := numericalTranscriptConstraint strategy h.val
    let hS := numericalPosterior_nonempty strategy rho T h
    (FinitePMF.uniform (Equiv.Perm (Fin d))).fiberContribution
      (reachableHistoryOf strategy (concreteOracle d rho) T) X h =
      (reachableHistoryLaw strategy (concreteOracle d rho)
        (FinitePMF.uniform (Equiv.Perm (Fin d))) T).weight h *
      uniformAverage (fun σ : FerrersPerm (S.reducedData hS) => X ((S.ferrersEquiv hS).symm σ).val) := by
  rw [numerical_uniform_posterior]
  rw [RankConstraint.uniformAverage_reduced]

end Lemmata.DistributionalLowerBounds.Core.Distributional
