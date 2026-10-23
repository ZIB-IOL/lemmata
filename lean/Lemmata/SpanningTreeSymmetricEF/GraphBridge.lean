module

public import Lemmata.SpanningTreeMinSplit.Main
-- The published API hides noncomputable definition bodies. This supplemental
-- import permits kernel-checked unfolding of its parent-edge projection;
-- the public dependency remains the published Main module.
import all Lemmata.SpanningTreeMinSplit.Trees
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Lemmata.SpanningTreeSymmetricEF.GraphBridge

open SimpleGraph
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V]

/-- Expose the published scalar incidence convention without defining a second one. -/
theorem published_edgeValue_eq {n : ℕ} (T : Lemmata.SpanningTreeMinSplit.Tree n)
    (e : Sym2 (Fin n)) :
    Lemmata.SpanningTreeMinSplit.edgeValue T e = if e ∈ T.val.edgeSet then 1 else 0 := by
  classical
  rfl

/-- Relabel a finite graph using `Fintype.equivFin`; no ordering is assumed on `V`. -/
def finIso (G : SimpleGraph V) : G ≃g G.map (Fintype.equivFin V) :=
  SimpleGraph.Iso.map (Fintype.equivFin V) G

/-- The same tree, as an input to the published tree infrastructure. -/
abbrev finTree {G : SimpleGraph V} (hG : G.IsTree) :
    Lemmata.SpanningTreeMinSplit.Tree (Fintype.card V) :=
  ⟨G.map (Fintype.equivFin V), (finIso G).isTree_iff.mp hG⟩

/-- Transport the published root path back to the original finite vertex type. -/
def rootWalk {G : SimpleGraph V} (hG : G.IsTree) (r v : V) : G.Walk r v :=
  ((Lemmata.SpanningTreeMinSplit.rootWalk (finTree hG)
    (Fintype.equivFin V r) (Fintype.equivFin V v)).map (finIso G).symm.toHom).copy
    (by simp [finIso]) (by simp [finIso])

theorem rootWalk_isPath {G : SimpleGraph V} (hG : G.IsTree) (r v : V) :
    (rootWalk hG r v).IsPath := by
  unfold rootWalk
  rw [Walk.isPath_copy]
  exact (Lemmata.SpanningTreeMinSplit.rootWalk_isPath _ _ _).map
    (finIso G).symm.injective

/-- The transported path is exactly the source's unique-path choice. -/
theorem rootWalk_eq_sourceChoice {G : SimpleGraph V} (hG : G.IsTree) (r v : V) :
    rootWalk hG r v = Classical.choose (hG.existsUnique_path r v) :=
  (Classical.choose_spec (hG.existsUnique_path r v)).2 _ (rootWalk_isPath hG r v)

/-- Transport the published parent, including its convention at the root. -/
def parent {G : SimpleGraph V} (hG : G.IsTree) (r v : V) : V :=
  (Fintype.equivFin V).symm (Lemmata.SpanningTreeMinSplit.parent (finTree hG)
    (Fintype.equivFin V r) (Fintype.equivFin V v))

@[simp] theorem parent_root {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    parent hG r r = r := by simp [parent]

theorem parent_adj {G : SimpleGraph V} (hG : G.IsTree) (r v : V) (hv : v ≠ r) :
    G.Adj v (parent hG r v) := by
  have h := (finIso G).symm.toHom.map_adj
    (Lemmata.SpanningTreeMinSplit.parent_adj (finTree hG) _ _
      (fun he => hv ((Fintype.equivFin V).injective he)))
  simpa [finIso, parent] using h

theorem parent_support {G : SimpleGraph V} (hG : G.IsTree) (r v : V) (hv : v ≠ r) :
    parent hG r v ∈ (rootWalk hG r v).support := by
  have h := Lemmata.SpanningTreeMinSplit.parent_support (finTree hG)
    (Fintype.equivFin V r) (Fintype.equivFin V v)
    (fun he => hv ((Fintype.equivFin V).injective he))
  unfold rootWalk
  rw [Walk.support_copy, Walk.support_map]
  exact List.mem_map.mpr ⟨_, h, rfl⟩

/-- Compatibility with the source's penultimate-vertex definition. -/
theorem parent_eq_penultimate {G : SimpleGraph V} (hG : G.IsTree) (r v : V)
    (hv : v ≠ r) : parent hG r v = (rootWalk hG r v).penultimate :=
  hG.isAcyclic.eq_penultimate_of_adj_end (rootWalk_isPath hG r v)
    (parent_adj hG r v hv) (parent_support hG r v hv)

/-- Relabel nonroot vertices without choosing any extra graph data. -/
def childEquiv (r : V) : {v : V // v ≠ r} ≃
    Lemmata.SpanningTreeMinSplit.Child (Fintype.equivFin V r) where
  toFun v := ⟨Fintype.equivFin V v.val,
    fun h => v.property ((Fintype.equivFin V).injective h)⟩
  invFun v := ⟨(Fintype.equivFin V).symm v.val, by
    intro h
    apply v.property
    simpa using congrArg (Fintype.equivFin V) h⟩
  left_inv v := by simp
  right_inv v := by simp

/-- Transport the published parent-edge map, rather than reproving its bijection. -/
def parentTreeEdge {G : SimpleGraph V} (hG : G.IsTree) (r : V)
    (v : {v : V // v ≠ r}) : G.edgeSet :=
  (finIso G).mapEdgeSet.symm (Lemmata.SpanningTreeMinSplit.parentTreeEdge
    (finTree hG) (Fintype.equivFin V r) (childEquiv r v))

theorem parentTreeEdge_val {G : SimpleGraph V} (hG : G.IsTree) (r : V)
    (v : {v : V // v ≠ r}) :
    (parentTreeEdge hG r v).val = s(v.val, parent hG r v.val) := by
  simp [parentTreeEdge, SimpleGraph.Iso.mapEdgeSet, finIso,
    SimpleGraph.Hom.mapEdgeSet,
    Lemmata.SpanningTreeMinSplit.parentTreeEdge, childEquiv, parent]

theorem parentTreeEdge_bijective {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    Function.Bijective (parentTreeEdge hG r) :=
  (finIso G).mapEdgeSet.symm.bijective.comp
    ((Lemmata.SpanningTreeMinSplit.parentTreeEdge_bijective (finTree hG)
      (Fintype.equivFin V r)).comp (childEquiv r).bijective)

end
end Lemmata.SpanningTreeSymmetricEF.GraphBridge
