module

/-
  Actual spanning trees belong to the orientation LP and cut-matrix SDP.

  The witnesses are constructed from unique tree paths and a genuine proper
  two-coloring. No orientation-existence or SDP-containment hypothesis is used.
  The LP subset bound is also proved directly, independently of matching
  integrality. Conversion of subset bounds into objective bounds is separate.
-/
public import Lemmata.SpanningTreeSymmetricEF.GraphBridge
public import Lemmata.SpanningTreeSymmetricEF.SDPBounds

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.TreeModels

open scoped BigOperators
open SimpleGraph SDPBounds

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The symmetric zero-diagonal incidence matrix of a simple graph. -/
def incidence (G : SimpleGraph V) : Matrix V V ℝ := by
  classical
  exact fun i j => if G.Adj i j then 1 else 0

/-- On labelled vertices this is precisely the already-published scalar incidence. -/
theorem incidence_fin_eq_edgeValue {n : ℕ} (T : Lemmata.SpanningTreeMinSplit.Tree n)
    (i j : Fin n) : incidence T.val i j =
      Lemmata.SpanningTreeMinSplit.edgeValue T s(i,j) := by
  classical
  rw [GraphBridge.published_edgeValue_eq]
  rfl

/-- The unique path is transported from the published tree infrastructure. -/
abbrev rootWalk {G : SimpleGraph V} (hG : G.IsTree) (r v : V) : G.Walk r v :=
  GraphBridge.rootWalk hG r v

omit [DecidableEq V] in
theorem rootWalk_isPath {G : SimpleGraph V} (hG : G.IsTree) (r v : V) :
    (rootWalk hG r v).IsPath :=
  GraphBridge.rootWalk_isPath hG r v

/-- Orient an edge toward the root: the head lies on the root-to-tail path. -/
def treeOrientation {G : SimpleGraph V} (hG : G.IsTree) (r : V) : Matrix V V ℝ := by
  classical
  exact fun i j => if G.Adj i j ∧ j ∈ (rootWalk hG r i).support then 1 else 0

theorem treeOrientation_nonneg {G : SimpleGraph V} (hG : G.IsTree) (r i j : V) :
    0 ≤ treeOrientation hG r i j := by
  classical
  unfold treeOrientation
  split_ifs <;> norm_num

theorem treeOrientation_diagonal {G : SimpleGraph V} (hG : G.IsTree) (r i : V) :
    treeOrientation hG r i i = 0 := by
  classical
  simp [treeOrientation]

theorem treeOrientation_outdegree {G : SimpleGraph V} (hG : G.IsTree) (r i : V) :
    ∑ j, treeOrientation hG r i j ≤ 1 := by
  classical
  have heq : (∑ j, treeOrientation hG r i j) =
      treeOrientation hG r i (rootWalk hG r i).penultimate := by
    apply Finset.sum_eq_single
    · intro j _ hj
      unfold treeOrientation
      split_ifs with h
      · exact (hj (hG.isAcyclic.eq_penultimate_of_adj_end
          (rootWalk_isPath hG r i) h.1 h.2)).elim
      · rfl
    · simp
  rw [heq]
  unfold treeOrientation
  split_ifs <;> norm_num

theorem treeOrientation_projects {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    edgeWeights (treeOrientation hG r) = incidence G := by
  classical
  ext i j
  by_cases hij : G.Adj i j
  · by_cases hj : j ∈ (rootWalk hG r i).support
    · have hi := hG.isAcyclic.ne_mem_support_of_support_of_adj_of_isPath
        (rootWalk_isPath hG r i) (rootWalk_isPath hG r j) hij hj
      simp [edgeWeights, treeOrientation, incidence, hij, hij.symm, hj, hi]
    · have hi := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (rootWalk_isPath hG r j) (rootWalk_isPath hG r i) hij.symm hj
      simp [edgeWeights, treeOrientation, incidence, hij, hij.symm, hj, hi]
  · have hji : ¬ G.Adj j i := fun h => hij h.symm
    simp [edgeWeights, treeOrientation, incidence, hij, hji]

/-- Signs of a proper two-coloring; changing all signs does not change its Gram matrix. -/
def colorSign {G : SimpleGraph V} (C : G.Coloring (Fin 2)) (i : V) : ℝ :=
  if C i = 0 then 1 else -1

omit [Fintype V] [DecidableEq V] in
theorem colorSign_sq {G : SimpleGraph V} (C : G.Coloring (Fin 2)) (i : V) :
    colorSign C i * colorSign C i = 1 := by
  unfold colorSign
  split_ifs <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem colorSign_adj {G : SimpleGraph V} (C : G.Coloring (Fin 2))
    {i j : V} (hij : G.Adj i j) : colorSign C i * colorSign C j = -1 := by
  have hne := C.valid hij
  have hi := (C i).isLt
  have hj := (C j).isLt
  have cases : (C i = 0 ∧ C j = 1) ∨ (C i = 1 ∧ C j = 0) := by omega
  rcases cases with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> simp [colorSign, hi, hj]

/-- A concrete feasible lift for every spanning tree, with its actual incidence projection. -/
theorem tree_sdp_containment {G : SimpleGraph V} (hG : G.IsTree) :
    ∃ y X : Matrix V V ℝ, Feasible y X ∧ edgeWeights y = incidence G := by
  classical
  let r := hG.connected.nonempty.some
  let C := hG.coloringTwo
  let z := colorSign C
  let X := Matrix.vecMulVec z z
  refine ⟨treeOrientation hG r, X, ?_, treeOrientation_projects hG r⟩
  constructor
  · exact treeOrientation_nonneg hG r
  · exact treeOrientation_diagonal hG r
  · exact treeOrientation_outdegree hG r
  · simpa [X] using Matrix.posSemidef_vecMulVec_self_star z
  · intro i
    exact colorSign_sq C i
  · intro i j _
    rw [treeOrientation_projects]
    change incidence G i j ≤ (1 - z i * z j) / 2
    by_cases hij : G.Adj i j
    · have hh := colorSign_adj C hij
      change colorSign C i * colorSign C j = -1 at hh
      simp [incidence, hij, z, hh]
    · simp only [incidence, hij, ↓reduceIte]
      dsimp [z, colorSign]
      split_ifs <;> norm_num

/-- The paper's orientation LP: nonnegative arcs, outdegree at most one,
zero diagonal and undirected edge capacity one. -/
structure LPFeasible (y : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ y i j
  diagonal : ∀ i, y i i = 0
  outdegree : ∀ i, ∑ j, y i j ≤ 1
  capacity : ∀ i j, edgeWeights y i j ≤ 1

theorem tree_lp_containment {G : SimpleGraph V} (hG : G.IsTree) :
    ∃ y : Matrix V V ℝ, LPFeasible y ∧ edgeWeights y = incidence G := by
  classical
  let r := hG.connected.nonempty.some
  refine ⟨treeOrientation hG r, ?_, treeOrientation_projects hG r⟩
  refine ⟨treeOrientation_nonneg hG r, treeOrientation_diagonal hG r,
    treeOrientation_outdegree hG r, ?_⟩
  intro i j
  rw [treeOrientation_projects]
  unfold incidence
  split_ifs <;> norm_num

omit [DecidableEq V] in
theorem LPFeasible.internalWeight_le_card {y : Matrix V V ℝ}
    (h : LPFeasible y) (U : Finset V) :
    internalWeight (edgeWeights y) U ≤ (U.card : ℝ) := by
  rw [internalWeight_edgeWeights]
  calc
    _ ≤ ∑ i ∈ U, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.sum_le_univ_sum_of_nonneg (s := U) (h.nonneg i)).trans (h.outdegree i)
    _ = _ := by simp

/-- The same forest-inequality route works for the LP, with scale 2/3.
It avoids importing bipartite matching integrality as an unproved interface. -/
theorem LPFeasible.scaled_forest_inequality {y : Matrix V V ℝ}
    (h : LPFeasible y) (U : Finset V) (hU : U.Nonempty) :
    (2 / 3 : ℝ) * internalWeight (edgeWeights y) U ≤ (U.card : ℝ) - 1 := by
  have hcard : 1 ≤ U.card := hU.card_pos
  by_cases h1 : U.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
    simp [internalWeight, edgeWeights, h.diagonal]
  by_cases h2 : U.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    have hcap := h.capacity a b
    simp [internalWeight, edgeWeights, h.diagonal, hab] at *
    linarith
  have h3 : (3 : ℝ) ≤ U.card := by exact_mod_cast (by omega : 3 ≤ U.card)
  have hh := h.internalWeight_le_card U
  linarith

end
end Lemmata.SpanningTreeSymmetricEF.TreeModels
