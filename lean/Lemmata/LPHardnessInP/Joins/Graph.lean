module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.LPHardnessInP.Graph

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of edges of a simple graph. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- Degree of a vertex, independent of an explicitly supplied decision procedure. -/
noncomputable def degree (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact G.degree v

/-- An unordered edge crosses a cut when exactly one endpoint lies in it. -/
def crosses (U : Finset V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun u v => (u ∈ U ∧ v ∉ U) ∨ (v ∈ U ∧ u ∉ U),
    fun _ _ => propext or_comm⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem crosses_mk (U : Finset V) (u v : V) :
    crosses U s(u, v) ↔ (u ∈ U ∧ v ∉ U) ∨ (v ∈ U ∧ u ∉ U) := Iff.rfl

/-- Number of edges crossing a cut. -/
noncomputable def cutCount (G : SimpleGraph V) (U : Finset V) : ℕ := by
  classical
  exact (G.edgeFinset.filter (crosses U)).card

/-- Positive edge costs, with an additional penalty for crossing the cut. -/
noncomputable def edgeCost (U : Finset V) (gamma : ℝ) (e : Sym2 V) : ℝ := by
  classical
  exact 1 + if crosses U e then gamma else 0

/-- The cost of the actual edge set of a graph. -/
noncomputable def cost (G : SimpleGraph V) (U : Finset V) (gamma : ℝ) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset, edgeCost U gamma e

omit [DecidableEq V] in
/-- The cut cost separates into the number of edges and the number of
crossing edges. -/
theorem cost_eq (G : SimpleGraph V) (U : Finset V) (gamma : ℝ) :
    cost G U gamma = (edgeCount G : ℝ) + gamma * (cutCount G U : ℝ) := by
  classical
  simp only [cost, edgeCost, Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_filter]
  simp [edgeCount, cutCount, mul_comm]

omit [DecidableEq V] in
/-- The degree-sum identity in the common graph representation. -/
theorem sum_degree (G : SimpleGraph V) :
    ∑ v, degree G v = 2 * edgeCount G := by
  classical
  exact G.sum_degrees_eq_twice_card_edges

omit [DecidableEq V] in
/-- Every vertex degree is bounded by the total number of edges. -/
theorem degree_le_edgeCount (G : SimpleGraph V) (v : V) :
    degree G v ≤ edgeCount G := by
  classical
  exact G.degree_le_card_edgeFinset v

omit [Fintype V] [DecidableEq V] in
/-- A non-loop edge crosses a singleton exactly when it contains that vertex. -/
theorem crosses_singleton {e : Sym2 V} (v : V) (he : ¬e.IsDiag) :
    crosses {v} e ↔ v ∈ e := by
  obtain ⟨a, b⟩ := e
  have hab : a ≠ b := by simpa using he
  simp only [crosses_mk, Finset.mem_singleton, Sym2.mem_iff]
  aesop

/-- A singleton cut contains precisely the incident edges. -/
theorem cutCount_singleton (G : SimpleGraph V) (v : V) :
    cutCount G {v} = degree G v := by
  classical
  unfold cutCount degree
  rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]
  congr 1
  apply Finset.filter_congr
  intro e he
  exact crosses_singleton v (G.not_isDiag_of_mem_edgeFinset he)

omit [DecidableEq V] in
/-- A crossing adjacency gives a positive cut cardinality. -/
theorem cutCount_pos_of_adj (G : SimpleGraph V) (U : Finset V)
    {u v : V} (hu : u ∈ U) (hv : v ∉ U) (huv : G.Adj u v) :
    0 < cutCount G U := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨s(u, v), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · simpa using huv
  · exact Or.inl ⟨hu, hv⟩

/-- If no edge crosses a cut, every neighbor of a vertex of the cut remains
inside the cut. -/
theorem neighbor_subset_of_cutCount_zero (G : SimpleGraph V) (U : Finset V)
    (hz : cutCount G U = 0) (u : (U : Set V)) :
    G.neighborSet u ⊆ (U : Set V) := by
  intro v huv
  by_contra hv
  have hp := cutCount_pos_of_adj G U u.property hv huv
  omega

/-- An odd-cardinality set cannot be a union of components of a graph in
which every vertex has odd degree. This is the cut property needed for
minimum-cost V-joins. -/
theorem cutCount_pos_of_odd_degrees (G : SimpleGraph V)
    (hdegree : ∀ v, Odd (degree G v)) (U : Finset V) (hU : Odd U.card) :
    0 < cutCount G U := by
  classical
  by_contra hn
  have hz : cutCount G U = 0 := by omega
  let : Fintype (U : Set V) := Subtype.fintype (Membership.mem (U : Set V))
  have hind : ∀ v : (U : Set V), Odd ((G.induce (U : Set V)).degree v) := by
    intro v
    have hd : (G.induce (U : Set V)).degree v = G.degree v :=
      G.degree_induce_of_neighborSet_subset (neighbor_subset_of_cutCount_zero G U hz v)
    rw [hd]
    exact hdegree v
  have heven := (G.induce (U : Set V)).even_card_odd_degree_vertices
  have heven' : Even U.card := by
    simpa [hind] using heven
  exact (Nat.not_even_iff_odd.mpr hU) heven'

end Lemmata.LPHardnessInP.Graph
