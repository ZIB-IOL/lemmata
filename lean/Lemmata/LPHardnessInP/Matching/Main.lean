module

public import Lemmata.LPHardnessInP.Matching.Statement
public import Lemmata.LPHardnessInP.Matching.Attainment
public import Lemmata.LPHardnessInP.Formulation.Main

@[expose] public section

namespace Lemmata.LPHardnessInP.Matching

open Lemmata.SpanningTreeMinSplit
open Lemmata.LPHardnessInP.RankReduction
open Lemmata.LPHardnessInP.CostTransfer
open Lemmata.LPHardnessInP.Formulation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Perfect matchings have exactly half as many edges as vertices. -/
theorem edgeCount_matching (M : PerfectMatching V) :
    (Graph.edgeCount M.val : ℝ) = halfOrder V := by
  have h : Fintype.card V = 2 * Graph.edgeCount M.val := by
    simpa only [M.property, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
      Graph.sum_degree M.val
  have h' : (Fintype.card V : ℝ) = 2 * (Graph.edgeCount M.val : ℝ) := by exact_mod_cast h
  unfold halfOrder
  linarith

/-- Every perfect matching crosses every odd cut. -/
theorem crossing_ge_one (U : OddCut V) (M : PerfectMatching V) :
    1 ≤ crossing U M := by
  have h := Graph.cutCount_pos_of_odd_degrees M.val
    (fun v => by rw [M.property v]; decide) U.val U.property
  change (1 : ℝ) ≤ (Graph.cutCount M.val U.val : ℝ)
  exact_mod_cast (show 1 ≤ Graph.cutCount M.val U.val by omega)

omit [DecidableEq V] in
/-- A unique crossing adjacency means exactly one crossing unordered edge. -/
theorem cutCount_eq_one_of_unique_crossing (G : SimpleGraph V) (U : Finset V)
    (u v : V) (hu : u ∈ U) (hv : v ∉ U)
    (hcross : ∀ x y, x ∈ U → y ∉ U → (G.Adj x y ↔ x = u ∧ y = v)) :
    Graph.cutCount G U = 1 := by
  classical
  have hset : G.edgeFinset.filter (Graph.crosses U) = {s(u, v)} := by
    ext e
    constructor
    · intro he
      obtain ⟨x, y⟩ := e
      obtain ⟨hxy, hc⟩ := Finset.mem_filter.mp he
      have hadj : G.Adj x y := by simpa using hxy
      rcases hc with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · obtain ⟨rfl, rfl⟩ := (hcross x y hx hy).mp hadj
        simp
      · obtain ⟨rfl, rfl⟩ := (hcross y x hy hx).mp hadj.symm
        simp [Sym2.eq_swap]
    · intro he
      have he' : e = s(u, v) := Finset.mem_singleton.mp he
      subst e
      apply Finset.mem_filter.mpr
      refine ⟨?_, Or.inl ⟨hu, hv⟩⟩
      simpa using (hcross u v hu hv).mpr ⟨rfl, rfl⟩
  unfold Graph.cutCount
  rw [hset, Finset.card_singleton]

/-- The lower bound of one crossing is attained for every odd cut. -/
theorem exists_one_crossing (hV : Even (Fintype.card V)) (U : OddCut V) :
    ∃ M : PerfectMatching V, Graph.cutCount M.val U.val = 1 := by
  classical
  obtain ⟨G, hG, u, hu, v, hv, hc⟩ :=
    exists_unique_crossing_graph hV U.val U.property
  have hdeg : ∀ x, Graph.degree G x = 1 := by
    intro x
    exact G.degree_eq_one_iff_existsUnique_adj.mpr (hG x)
  exact ⟨⟨G, hdeg⟩, cutCount_eq_one_of_unique_crossing G U.val u v hu hv hc⟩

/-- The edge-sum objective equals its baseline plus its crossing penalty. -/
theorem matchingValue_eq (α : ℝ) (U : OddCut V) (M : PerfectMatching V) :
    matchingValue α U M = halfOrder V + penalty V α * crossing U M := by
  rw [matchingValue, Graph.cost_eq, edgeCount_matching]
  rfl

omit [DecidableEq V] in
theorem penalty_eq (α : ℝ) :
    penalty V α = 2 * (α - 1) * halfOrder V := by
  unfold penalty halfOrder
  ring

omit [DecidableEq V] in
theorem halfOrder_pos [Nonempty V] : 0 < halfOrder V := by
  unfold halfOrder
  positivity

/-- Exact optimum of the concrete matching cost family. -/
theorem matching_minimum (hV : Even (Fintype.card V)) (α : ℝ) (hα : 1 < α)
    (U : OddCut V) :
    (∀ M : PerfectMatching V, halfOrder V + penalty V α ≤ matchingValue α U M) ∧
      ∃ M : PerfectMatching V, matchingValue α U M = halfOrder V + penalty V α := by
  have hp : 0 ≤ penalty V α := by unfold penalty; positivity
  constructor
  · intro M
    rw [matchingValue_eq]
    have h := mul_le_mul_of_nonneg_left (crossing_ge_one U M) hp
    linarith
  · obtain ⟨M, hM⟩ := exists_one_crossing hV U
    refine ⟨M, ?_⟩
    rw [matchingValue_eq]
    simp only [crossing, hM, Nat.cast_one, mul_one]

omit [Fintype V] in
/-- The edge costs in the concrete construction are the off-diagonal
distances of the two-cluster metric. -/
theorem edgeCost_eq_cutMetric (U : OddCut V) (γ : ℝ) (u v : V) (huv : u ≠ v) :
    Graph.edgeCost U.val γ s(u, v) =
      cutMetric (fun x => decide (x ∈ U.val)) γ u v := by
  unfold Graph.edgeCost cutMetric
  simp only [Graph.crosses_mk, huv, ↓reduceIte]
  by_cases hu : u ∈ U.val <;> by_cases hv : v ∈ U.val <;> simp [hu, hv]

/-- Rank identity for the approximation slack of actual minimum-cost
perfect matchings on the fixed complete host. -/
theorem matching_slack_rank [Nonempty V] (α : ℝ) (hα : 1 < α) :
    nonnegativeRank (matchingSlack (V := V) α) =
      nonnegativeRank (fun U M => crossing (V := V) U M - 1 / (2 * α)) := by
  have hmatrix : matchingSlack (V := V) α =
      costSlack crossing (fun _ => 2 * (α - 1) * halfOrder V) (fun _ => halfOrder V) α := by
    funext U M
    rw [matchingSlack, matchingValue_eq, penalty_eq]
    unfold costSlack
    ring
  rw [hmatrix]
  exact positive_cost_rank_identity crossing α (halfOrder V) hα halfOrder_pos

/-- A source shifted-matching bound gives a lower bound for any certified
approximate matching LP. Source rank is the only matrix-hardness hypothesis. -/
theorem matching_lp_lower_bound [Nonempty V]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (α : ℝ) (hα : 1 < α) {m L : ℕ}
    (C : CertifiedLP (V := E) (matchingValue (V := V) α)
      (fun _ => (halfOrder V + penalty V α) / α) m)
    (source_lower_bound : (L : ℕ∞) ≤
      nonnegativeRank (fun U M => crossing (V := V) U M - 1 / (2 * α))) :
    L ≤ m + 1 := by
  rw [← matching_slack_rank α hα] at source_lower_bound
  exact_mod_cast source_lower_bound.trans (certified_slack_rank_bound C)

/-- For matching-indicator weights, the minimum odd cut has value one. -/
theorem oddCut_minimum [Nonempty V] (M : PerfectMatching V) :
    (∀ U : OddCut V, 1 ≤ oddCutValue M U) ∧
      ∃ U : OddCut V, oddCutValue M U = 1 := by
  constructor
  · exact fun U => crossing_ge_one U M
  · let v : V := Classical.choice inferInstance
    let U : OddCut V := ⟨{v}, by simp⟩
    refine ⟨U, ?_⟩
    change (Graph.cutCount M.val {v} : ℝ) = 1
    rw [Graph.cutCount_singleton, M.property, Nat.cast_one]

omit [DecidableEq V] in
/-- Odd-cut approximation slacks are the transpose of the shifted matching
matrix; the edge weights are the zero-one incidence vector of `M`. -/
theorem oddCut_slack_rank (α : ℝ) :
    nonnegativeRank (fun M U => oddCutValue (V := V) M U - 1 / α) =
      nonnegativeRank (fun U M => crossing (V := V) U M - 1 / α) :=
  rank_transpose _

omit [DecidableEq V] in
/-- The concrete odd-cut LP lower bound, with the shifted source rank theorem
as an explicit hypothesis. -/
theorem oddCut_lp_lower_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (α : ℝ) {m L : ℕ}
    (C : CertifiedLP (V := E) (oddCutValue (V := V)) (fun _ => 1 / α) m)
    (source_lower_bound : (L : ℕ∞) ≤
      nonnegativeRank (fun U M => crossing (V := V) U M - 1 / α)) :
    L ≤ m + 1 := by
  rw [← oddCut_slack_rank α] at source_lower_bound
  exact_mod_cast source_lower_bound.trans (certified_slack_rank_bound C)

end Lemmata.LPHardnessInP.Matching
