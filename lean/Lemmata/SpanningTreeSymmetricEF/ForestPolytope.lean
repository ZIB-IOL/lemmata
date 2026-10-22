module

public import Lemmata.SpanningTreeSymmetricEF.ForestGreedy
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section


/-!
Weighted forest dominance from the forest subset inequalities. Edges are `Sym2 V`;
diagonal entries are zero, so a subset's internal mass is the sum on `U.sym2`.
-/
namespace Lemmata.SpanningTreeSymmetricEF.ForestPolytope

open scoped BigOperators
open SimpleGraph

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Decompose an edge sum over the components of a graph in which its endpoints
are reachable. -/
theorem sum_over_components (F G : SimpleGraph V) (w : Sym2 V → ℝ)
    (h : ∀ u v, G.Adj u v → F.Reachable u v) :
    letI := Classical.decRel F.Adj
    letI := Classical.decRel G.Adj
    letI := Fintype.ofFinite F.ConnectedComponent
    (∑ C : F.ConnectedComponent, ∑ e ∈ G.edgeFinset ∩ C.supp.toFinset.sym2, w e) =
      ∑ e ∈ G.edgeFinset, w e := by
  classical
  have hinter (C : F.ConnectedComponent) :
      G.edgeFinset ∩ C.supp.toFinset.sym2 =
        G.edgeFinset.filter (· ∈ C.supp.toFinset.sym2) := by ext; simp
  simp_rw [hinter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hadj : G.Adj u v := by simpa using he
    have huv : F.connectedComponentMk u = F.connectedComponentMk v :=
      ConnectedComponent.sound (h u v hadj)
    simp only [Finset.mk_mem_sym2_iff, Set.mem_toFinset, ConnectedComponent.mem_supp_iff]
    simp [← huv]

/-- On each forest component, the number of edges is the number of vertices
minus one. The component partition then turns subset bounds into a rank bound. -/
theorem sum_le_card_spanning_forest (x : Sym2 V → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hsub : ∀ U : Finset V, U.Nonempty → (∑ e ∈ U.sym2, x e) ≤ (U.card : ℝ) - 1)
    (F G : SimpleGraph V) (hF : F.IsAcyclic) (hreach : G.Reachable = F.Reachable) :
    letI := Classical.decRel F.Adj
    letI := Classical.decRel G.Adj
    (∑ e ∈ G.edgeFinset, x e) ≤ (F.edgeFinset.card : ℝ) := by
  classical
  let := Fintype.ofFinite F.ConnectedComponent
  have hcount (C : F.ConnectedComponent) :
      ((F.edgeFinset ∩ C.supp.toFinset.sym2).card : ℝ) =
        (C.supp.toFinset.card : ℝ) - 1 := by
    have htree : (F.induce C.supp).IsTree :=
      ⟨C.connected_toSimpleGraph, hF.induce C.supp⟩
    have hh := htree.card_edgeFinset
    rw [← F.map_edgeFinset_induce (s := C.supp), Finset.card_map]
    have hc : Fintype.card C.supp = C.supp.toFinset.card := by simp
    rw [hc] at hh
    have hh' : ((F.induce C.supp).edgeFinset.card : ℝ) + 1 =
        (C.supp.toFinset.card : ℝ) := by exact_mod_cast hh
    linarith
  calc
    _ = ∑ C : F.ConnectedComponent, ∑ e ∈ G.edgeFinset ∩ C.supp.toFinset.sym2, x e :=
      (sum_over_components F G x (fun u v huv => hreach ▸ huv.reachable)).symm
    _ ≤ ∑ C : F.ConnectedComponent, ((F.edgeFinset ∩ C.supp.toFinset.sym2).card : ℝ) := by
      apply Finset.sum_le_sum
      intro C _
      rw [hcount]
      calc
        _ ≤ ∑ e ∈ C.supp.toFinset.sym2, x e :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun e _ _ => hx e)
        _ ≤ _ := hsub _ (by simpa using C.nonempty_supp)
    _ = _ := by
      simpa using sum_over_components F F (fun _ => (1 : ℝ)) (fun _ _ h => h.reachable)

omit [Fintype V] in
/-- A finite edge set decodes to a simple graph by dropping its diagonal. -/
theorem edgeFinset_from_finset (s : Finset (Sym2 V))
    [Fintype (fromEdgeSet (s : Set (Sym2 V))).edgeSet] :
    (fromEdgeSet (s : Set (Sym2 V))).edgeFinset = s.filter (fun e => ¬e.IsDiag) := by
  classical
  ext e
  simp [mem_edgeFinset, edgeSet_fromEdgeSet, Sym2.mem_diagSet]

/-- The subset inequalities imply the unweighted extension bound required by
weight induction. Loops are only a convenient part of the ambient `Sym2` type;
the selected edge sets have none. -/
theorem forest_extension_card_bound (x : Sym2 V → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hdiag : ∀ e, e.IsDiag → x e = 0)
    (hsub : ∀ U : Finset V, U.Nonempty → (∑ e ∈ U.sym2, x e) ≤ (U.card : ℝ) - 1)
    (s t : Finset (Sym2 V))
    (htdiag : ∀ e ∈ t, ¬e.IsDiag) (ht : (fromEdgeSet (t : Set (Sym2 V))).IsAcyclic)
    (hts : t ⊆ s) :
    ∃ u : Finset (Sym2 V),
      (∀ e ∈ u, ¬e.IsDiag) ∧ (fromEdgeSet (u : Set (Sym2 V))).IsAcyclic ∧
      t ⊆ u ∧ u ⊆ s ∧ (∑ e ∈ s, x e) ≤ (u.card : ℝ) := by
  classical
  let G := fromEdgeSet (s : Set (Sym2 V))
  let H := fromEdgeSet (t : Set (Sym2 V))
  have hHG : H ≤ G := fromEdgeSet_mono (by exact hts)
  obtain ⟨F, hHF, hFG, hF, hreach⟩ :=
    G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hHG ht
  have hFs : F.edgeFinset ⊆ s := by
    intro e he
    have hg := edgeFinset_mono hFG he
    rw [show G.edgeFinset = s.filter (fun e => ¬e.IsDiag) from edgeFinset_from_finset s] at hg
    exact (Finset.mem_filter.mp hg).1
  refine ⟨F.edgeFinset, (fun e he => F.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp he)),
    ?_, ?_, hFs, ?_⟩
  · simpa using hF
  · intro e he
    apply edgeFinset_mono hHF
    rw [show H.edgeFinset = t.filter (fun e => ¬e.IsDiag) from edgeFinset_from_finset t]
    exact Finset.mem_filter.mpr ⟨he, htdiag e he⟩
  · have heq : (∑ e ∈ G.edgeFinset, x e) = ∑ e ∈ s, x e := by
      rw [show G.edgeFinset = s.filter (fun e => ¬e.IsDiag) from edgeFinset_from_finset s]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro e he hnot
      exact hdiag e (by simpa [he] using hnot)
    rw [← heq]
    convert sum_le_card_spanning_forest x hx hsub F G hF hreach.symm using 1
    apply Finset.sum_congr
    · ext e; simp
    · intro e _; rfl

/-- Every nonnegative objective at a point satisfying the forest inequalities
is dominated by the incidence vector of an actual acyclic subgraph. This is a
weighted conclusion, proved without assuming a convex-hull theorem. -/
theorem weighted_forest_dominance (x : Sym2 V → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hdiag : ∀ e, e.IsDiag → x e = 0)
    (hsub : ∀ U : Finset V, U.Nonempty → (∑ e ∈ U.sym2, x e) ≤ (U.card : ℝ) - 1)
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (hc : ∀ e, 0 ≤ c e) :
    letI := Classical.decRel G.Adj
    ∃ F : SimpleGraph V, F.IsAcyclic ∧ F ≤ G ∧
      letI := Classical.decRel F.Adj
      (∑ e ∈ G.edgeFinset, c e * x e) ≤ ∑ e ∈ F.edgeFinset, c e := by
  classical
  let I : Finset (Sym2 V) → Prop := fun t =>
    (∀ e ∈ t, ¬e.IsDiag) ∧ (fromEdgeSet (t : Set (Sym2 V))).IsAcyclic
  have hi : I ∅ := by simp [I, isAcyclic_bot]
  have hext : ∀ s t, I t → t ⊆ s →
      ∃ u, I u ∧ t ⊆ u ∧ u ⊆ s ∧ (∑ e ∈ s, x e) ≤ (u.card : ℝ) := by
    intro s t ht hts
    obtain ⟨u, hud, hua, htu, hus, hcard⟩ :=
      forest_extension_card_bound x hx hdiag hsub s t ht.1 ht.2 hts
    exact ⟨u, ⟨hud, hua⟩, htu, hus, hcard⟩
  obtain ⟨t, ht, hts, hw⟩ :=
    weighted_dominance_of_extension I x hi hext G.edgeFinset c (fun e _ => hc e)
  refine ⟨fromEdgeSet (t : Set (Sym2 V)), ht.2, ?_, ?_⟩
  · apply G.fromEdgeSet_le.mpr
    intro e he
    exact mem_edgeFinset.mp (hts he.1)
  · simpa only [edgeFinset_from_finset, Finset.filter_eq_self.mpr ht.1] using hw

/-- Extend the dominating forest inside the connected ambient graph. With
nonnegative costs this proves domination by an actual spanning tree. -/
theorem weighted_spanning_tree_dominance (x : Sym2 V → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hdiag : ∀ e, e.IsDiag → x e = 0)
    (hsub : ∀ U : Finset V, U.Nonempty → (∑ e ∈ U.sym2, x e) ≤ (U.card : ℝ) - 1)
    (G : SimpleGraph V) (hG : G.Connected)
    (c : Sym2 V → ℝ) (hc : ∀ e, 0 ≤ c e) :
    letI := Classical.decRel G.Adj
    ∃ T : SimpleGraph V, T.IsTree ∧ T ≤ G ∧
      letI := Classical.decRel T.Adj
      (∑ e ∈ G.edgeFinset, c e * x e) ≤ ∑ e ∈ T.edgeFinset, c e := by
  classical
  obtain ⟨F, hF, hFG, hw⟩ := weighted_forest_dominance x hx hdiag hsub G c hc
  obtain ⟨T, hFT, hTG, hT⟩ := hG.exists_isTree_le_of_le_of_isAcyclic hFG hF
  refine ⟨T, hT, hTG, hw.trans ?_⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (edgeFinset_mono hFT) (fun e _ _ => hc e)

end
end Lemmata.SpanningTreeSymmetricEF.ForestPolytope
