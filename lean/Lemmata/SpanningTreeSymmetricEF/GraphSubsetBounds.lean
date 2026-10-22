module

public import Lemmata.SpanningTreeSymmetricEF.ApproximationUpper

@[expose] public section


/-! Actual forest subset inequalities, without a polytope-membership assumption. -/
namespace Lemmata.SpanningTreeSymmetricEF.GraphSubsetBounds
open scoped BigOperators
open SimpleGraph ApproximationUpper Approximation
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem acyclic_card_le [Nonempty V] {G : SimpleGraph V} (hG : G.IsAcyclic) :
    letI := Classical.decRel G.Adj
    G.edgeFinset.card + 1 ≤ Fintype.card V := by
  classical
  obtain ⟨T, hGT, _, hT⟩ :=
    (connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic le_top hG
  have hh := Finset.card_le_card (edgeFinset_mono hGT)
  have ht := hT.card_edgeFinset
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Every nonempty induced forest has at most |U|-1 edges, even when disconnected. -/
theorem acyclic_subset_card {G : SimpleGraph V} (hG : G.IsAcyclic)
    (U : Finset V) (hU : U.Nonempty) :
    letI := Classical.decRel G.Adj
    (G.edgeFinset ∩ U.sym2).card + 1 ≤ U.card := by
  classical
  let : Nonempty (U : Set V) := by
    obtain ⟨v, hv⟩ := hU
    exact ⟨⟨v, hv⟩⟩
  have hh := acyclic_card_le (hG.induce (U : Set V))
  have he := congrArg Finset.card (G.map_edgeFinset_induce (s := (U : Set V)))
  simp only [Finset.card_map] at he
  have hc : (G.edgeFinset ∩ U.sym2).card = (G.induce (U : Set V)).edgeFinset.card := by
    convert he.symm using 1 <;> congr 1 <;> ext e <;> simp
  rw [hc]
  simpa using hh

/-- The unit objective on all internal unordered pairs of U (diagonal harmless). -/
def subsetCost (U : Finset V) (e : Sym2 V) : ℝ := if e ∈ U.sym2 then 1 else 0

omit [Fintype V] in
theorem subsetCost_nonneg (U : Finset V) (e : Sym2 V) : 0 ≤ subsetCost U e := by
  unfold subsetCost
  split_ifs <;> norm_num

theorem objective_subsetCost (U : Finset V) (x : Sym2 V → ℝ) :
    objective (subsetCost U) x = ∑ e ∈ U.sym2, x e := by
  classical
  unfold objective subsetCost
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro e _; rfl

/-- In particular this gives the triangle objective bound for every actual tree. -/
theorem tree_subset_objective {G : SimpleGraph V} (hG : G.IsTree)
    (U : Finset V) (hU : U.Nonempty) :
    objective (subsetCost U) (graphIncidence G) ≤ (U.card : ℝ) - 1 := by
  classical
  rw [objective_subsetCost]
  have he : (∑ e ∈ U.sym2, graphIncidence G e) =
      ((G.edgeFinset ∩ U.sym2).card : ℝ) := by
    simp only [graphIncidence]
    rw [← Finset.sum_filter]
    have hf : U.sym2.filter (fun e => e ∈ G.edgeSet) = G.edgeFinset ∩ U.sym2 := by
      ext e; simp [and_comm]
    rw [hf]
    simp
  rw [he]
  have hh : ((G.edgeFinset ∩ U.sym2).card : ℝ) + 1 ≤ U.card := by
    exact_mod_cast acyclic_subset_card hG.isAcyclic U hU
  linarith
end
end Lemmata.SpanningTreeSymmetricEF.GraphSubsetBounds
