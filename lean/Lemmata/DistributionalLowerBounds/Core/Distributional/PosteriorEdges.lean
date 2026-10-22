module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.PosteriorQuery

@[expose] public section

/-! Physical-rank downward swaps: the same graph before and after reducing a
posterior. Defining edges by compatibility makes refinement a literal induced
subgraph, independently of changing row/rank enumerations. -/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
namespace RankConstraint
variable {d : ℕ} (S : RankConstraint d)

lemma swap_compatible (π : S.Realizations) (row a : Fin d)
    (hr : row ∈ S.freeRows) (ha : a ∈ S.freeRanks)
    (hlo : S.lowerRank row ≤ a.val+1) (hlt : a < π.val row) :
    S.Compatible (swapValues π.val a (π.val row)) := by
  intro i
  by_cases hia : π.val i = a
  · have hfree : i ∈ S.freeRows := (S.free_iff π i).mpr (hia.symm ▸ ha)
    have he := (S.mem_freeRows i).mp hfree
    constructor
    · intro r hh
      simp [he] at hh
    · have hb := (π.property i).2
      simp only [swapValues_apply, hia, Equiv.swap_apply_left]
      rw [hia] at hb
      have ht : a.val < (π.val row).val := hlt
      omega
  · by_cases hir : π.val i = π.val row
    · have hi := π.val.injective hir
      subst i
      have he := (S.mem_freeRows row).mp hr
      constructor
      · intro r hh
        simp [he] at hh
      · simpa only [swapValues_apply, Equiv.swap_apply_right] using hlo
    · simpa only [swapValues_apply, Equiv.swap_apply_of_ne_of_ne hia hir] using π.property i

/-- Edges are defined using ORIGINAL coordinate/rank labels, without a query.
The source is compatible by type; the target must be compatible too. -/
structure PhysicalOutgoing (π : S.Realizations) where
  row : Fin d
  lower : Fin d
  lower_lt : lower < π.val row
  compatible : S.Compatible (swapValues π.val lower (π.val row))

namespace PhysicalOutgoing
variable {S} {π : S.Realizations}

noncomputable instance : Fintype (S.PhysicalOutgoing π) :=
  Fintype.ofInjective (fun e => (e.row,e.lower)) (by
    intro e f h
    cases e; cases f; simp_all)

lemma ext (e f : S.PhysicalOutgoing π) (hr : e.row=f.row) (ha : e.lower=f.lower) : e=f := by
  cases e; cases f; simp_all

def target (e : S.PhysicalOutgoing π) : S.Realizations :=
  ⟨swapValues π.val e.lower (π.val e.row), e.compatible⟩

lemma row_free (e : S.PhysicalOutgoing π) : e.row ∈ S.freeRows := by
  by_contra hn
  have he := S.fixed_agree π e.target hn
  have hv : π.val e.row = e.lower := by simpa [target, swapValues] using he
  exact e.lower_lt.ne hv.symm

lemma lower_free (e : S.PhysicalOutgoing π) : e.lower ∈ S.freeRanks := by
  let j := π.val.symm e.lower
  have hj : π.val j = e.lower := π.val.apply_symm_apply _
  have hf : j ∈ S.freeRows := by
    by_contra hn
    have he := S.fixed_agree π e.target hn
    have hv : e.lower = π.val e.row := by simpa [target, swapValues, hj] using he
    exact e.lower_lt.ne hv
  exact hj ▸ (S.free_iff π j).mp hf

lemma lower_allowed (e : S.PhysicalOutgoing π) : S.lowerRank e.row ≤ e.lower.val+1 := by
  simpa [swapValues] using (e.compatible e.row).2

end PhysicalOutgoing

variable (hS : Nonempty S.Realizations)

noncomputable def physicalToReduced (π : S.Realizations) (e : S.PhysicalOutgoing π) :
    DownEdge.Outgoing (S.reducedData hS) (S.ferrersEquiv hS π) := by
  let i := S.rowEnum.symm ⟨e.row,e.row_free⟩
  let a := (S.rankOrder hS).symm ⟨e.lower,e.lower_free⟩
  have hi : (S.rowEnum i).val = e.row := by simp [i]
  have ha : (S.rankOrder hS a).val = e.lower := by simp [a]
  refine ⟨⟨S.ferrersEquiv hS π, i, a, ?_, ?_⟩, rfl⟩
  · apply (S.reducedLower_le_iff hS i a).mpr
    simpa only [rank, ha, hi] using e.lower_allowed
  · apply (S.rankOrder hS).lt_iff_lt.mp
    change (S.rankOrder hS a).val < (S.rankOrder hS (S.restrict hS π i)).val
    rw [ha, S.restrict_rankOrder, hi]
    exact e.lower_lt

noncomputable def reducedToPhysical (π : S.Realizations)
    (e : DownEdge.Outgoing (S.reducedData hS) (S.ferrersEquiv hS π)) : S.PhysicalOutgoing π := by
  let row := (S.rowEnum e.val.row).val
  let a := (S.rankOrder hS e.val.lowerValue).val
  have he : e.val.source.val = S.restrict hS π := congrArg Subtype.val e.property
  have ht : a < π.val row := by
    have h := (S.rankOrder hS).strictMono e.val.lower_lt
    change a < (S.rankOrder hS (e.val.source.val e.val.row)).val at h
    rw [he, S.restrict_rankOrder] at h
    exact h
  have hlo : S.lowerRank row ≤ a.val+1 :=
    (S.reducedLower_le_iff hS e.val.row e.val.lowerValue).mp e.val.lower_allowed
  exact ⟨row, a, ht, S.swap_compatible π row a (S.rowEnum _).property
    (S.rankOrder hS _).property hlo ht⟩

noncomputable def outgoingEquiv (π : S.Realizations) :
    S.PhysicalOutgoing π ≃ DownEdge.Outgoing (S.reducedData hS) (S.ferrersEquiv hS π) where
  toFun := S.physicalToReduced hS π
  invFun := S.reducedToPhysical hS π
  left_inv e := by
    apply PhysicalOutgoing.ext <;> simp [physicalToReduced, reducedToPhysical]
  right_inv e := by
    rcases e with ⟨⟨source,row,a,hlo,hlt⟩,he⟩
    dsimp only at he
    subst source
    apply Subtype.ext
    simp [physicalToReduced, reducedToPhysical]

lemma card_physicalOutgoing (π : S.Realizations) :
    (Fintype.card (S.PhysicalOutgoing π) : ℝ) = S.deficit hS := by
  rw [Fintype.card_congr (S.outgoingEquiv hS π), DownEdge.card_outgoing]
  rfl

/-- Refinement is an induced subgraph in physical rank labels. This is the
combinatorial identity needed before relating numerical cuts to water answers. -/
noncomputable def refinedOutgoingEquiv (p : Fin d → ℝ) (π : S.Realizations) :
    let A := numericalDisclosure d p (concreteLMO d π.val p)
    let π' : (A.refine S).Realizations := ⟨π.val,
      (numerical_refine_compatible_iff S π.val π.val p).mpr ⟨π.property,rfl⟩⟩
    {e : S.PhysicalOutgoing π // concreteLMO d e.target.val p = concreteLMO d π.val p} ≃
      (A.refine S).PhysicalOutgoing π' where
  toFun e := ⟨e.val.row,e.val.lower,e.val.lower_lt,
    (numerical_refine_compatible_iff S π.val _ p).mpr ⟨e.val.compatible,e.property⟩⟩
  invFun e := ⟨⟨e.row,e.lower,e.lower_lt,
    ((numerical_refine_compatible_iff S π.val _ p).mp e.compatible).1⟩,
    ((numerical_refine_compatible_iff S π.val _ p).mp e.compatible).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma rankOrder_swap (a b c : Fin S.remaining) :
    (S.rankOrder hS (Equiv.swap a b c)).val =
      Equiv.swap (S.rankOrder hS a).val (S.rankOrder hS b).val (S.rankOrder hS c).val := by
  by_cases hca : c=a
  · subst c; simp
  by_cases hcb : c=b
  · subst c; simp
  have ha : (S.rankOrder hS c).val ≠ (S.rankOrder hS a).val :=
    fun h => hca ((S.rankOrder hS).injective (Subtype.ext h))
  have hb : (S.rankOrder hS c).val ≠ (S.rankOrder hS b).val :=
    fun h => hcb ((S.rankOrder hS).injective (Subtype.ext h))
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_of_ne_of_ne ha hb]

lemma physicalToReduced_target (π : S.Realizations) (e : S.PhysicalOutgoing π) :
    S.ferrersEquiv hS e.target = (S.physicalToReduced hS π e).val.target := by
  apply Subtype.ext
  let i := S.rowEnum.symm ⟨e.row,e.row_free⟩
  let a := (S.rankOrder hS).symm ⟨e.lower,e.lower_free⟩
  change S.restrict hS e.target = swapValues (S.restrict hS π) a (S.restrict hS π i)
  apply Equiv.ext
  intro k
  apply (S.rankOrder hS).injective
  apply Subtype.ext
  rw [S.restrict_rankOrder, swapValues_apply, S.rankOrder_swap,
    S.restrict_rankOrder, S.restrict_rankOrder]
  simp only [a, i, OrderIso.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

noncomputable def internalOutgoingEquiv (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0)
    (π : S.Realizations) :
    {e : S.PhysicalOutgoing π // concreteLMO d e.target.val p = concreteLMO d π.val p} ≃
      {e : DownEdge.Outgoing (S.reducedData hS) (S.ferrersEquiv hS π) //
        ¬ DownEdge.IsCut (S.waterQuery hS p hp).answer e.val} := by
  classical
  apply (S.outgoingEquiv hS π).subtypeEquiv
  intro e
  have ht : (S.outgoingEquiv hS π e).val.target = S.ferrersEquiv hS e.target :=
    (S.physicalToReduced_target hS π e).symm
  simp only [DownEdge.IsCut, (S.outgoingEquiv hS π e).property, ht, not_ne_iff,
    S.water_answer_iff hS p hp, Equiv.symm_apply_apply]
  exact eq_comm

/-- Exact identification of the next posterior deficit with internal outdegree.
This includes the changing fixed rows, gapped ranks, and row re-sorting. -/
theorem internalOutdegree_eq_refined_deficit (p : Fin d → ℝ) (hp : ∃ i, p i ≠ 0)
    (π : S.Realizations) :
    let A := numericalDisclosure d p (concreteLMO d π.val p)
    let hA : Nonempty (A.refine S).Realizations := ⟨⟨π.val,
      (numerical_refine_compatible_iff S π.val π.val p).mpr ⟨π.property,rfl⟩⟩⟩
    (DownEdge.internalOutdegree (S.waterQuery hS p hp).answer (S.ferrersEquiv hS π) : ℝ) =
      (A.refine S).deficit hA := by
  classical
  dsimp only
  let A := numericalDisclosure d p (concreteLMO d π.val p)
  let π' : (A.refine S).Realizations := ⟨π.val,
    (numerical_refine_compatible_iff S π.val π.val p).mpr ⟨π.property,rfl⟩⟩
  have hi := Fintype.card_congr (S.internalOutgoingEquiv hS p hp π)
  have hr := Fintype.card_congr (S.refinedOutgoingEquiv p π)
  rw [← (A.refine S).card_physicalOutgoing ⟨π'⟩ π']
  exact_mod_cast hi.symm.trans hr

end RankConstraint
end Lemmata.DistributionalLowerBounds.Core.Distributional
