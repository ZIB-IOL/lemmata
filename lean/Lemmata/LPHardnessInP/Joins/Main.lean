module

public import Lemmata.LPHardnessInP.Joins.Statement
public import Lemmata.LPHardnessInP.Matching.Main
public import Lemmata.LPHardnessInP.Formulation.Main

@[expose] public section

namespace Lemmata.LPHardnessInP.Joins

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit
open Lemmata.LPHardnessInP.Matching
open Lemmata.LPHardnessInP.Formulation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every perfect matching is a V-join, independently of the cost instance. -/
def ofMatching (M : PerfectMatching V) : VJoin V :=
  ⟨M.val, fun v => by rw [M.property v]; exact odd_one⟩

omit [DecidableEq V] in
/-- A V-join has at least half as many edges as there are vertices. -/
theorem order_le_twice_edges (J : VJoin V) :
    Fintype.card V ≤ 2 * Graph.edgeCount J.val := by
  have hdeg : ∀ v, 1 ≤ Graph.degree J.val v := by
    intro v
    obtain ⟨k, hk⟩ := J.property v
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Graph.sum_degree] using hsum

/-- Every odd cut is crossed by a V-join. -/
theorem cutCount_ge_one (J : VJoin V) (U : OddCut V) :
    1 ≤ Graph.cutCount J.val U.val :=
  Graph.cutCount_pos_of_odd_degrees J.val J.property U.val U.property

/-- The same cut-metric objective is evaluated on all V-joins. -/
noncomputable def joinValue (α : ℝ) (U : OddCut V) (J : VJoin V) : ℝ :=
  Graph.cost J.val U.val (penalty V α)

omit [DecidableEq V] in
/-- The objective-independent inclusion of matchings preserves each cost. -/
theorem ofMatching_cost (α : ℝ) (U : OddCut V) (M : PerfectMatching V) :
    joinValue α U (ofMatching M) = matchingValue α U M := rfl

/-- The full V-join objective has the same optimum as the matching objective,
including an attaining feasible solution. -/
theorem vjoin_minimum (hV : Even (Fintype.card V)) (α : ℝ) (hα : 1 < α)
    (U : OddCut V) :
    (∀ J : VJoin V, halfOrder V + penalty V α ≤ joinValue α U J) ∧
      ∃ J : VJoin V, joinValue α U J = halfOrder V + penalty V α := by
  constructor
  · intro J
    have hsize : halfOrder V ≤ (Graph.edgeCount J.val : ℝ) := by
      have h := order_le_twice_edges J
      have h' : (Fintype.card V : ℝ) ≤ 2 * (Graph.edgeCount J.val : ℝ) := by
        exact_mod_cast h
      unfold halfOrder
      linarith
    have hcut : (1 : ℝ) ≤ (Graph.cutCount J.val U.val : ℝ) := by
      exact_mod_cast cutCount_ge_one J U
    have hp : 0 ≤ penalty V α := by unfold penalty; positivity
    have hmul := mul_le_mul_of_nonneg_left hcut hp
    rw [joinValue, Graph.cost_eq]
    linarith
  · obtain ⟨M, hM⟩ := (matching_minimum hV α hα U).2
    exact ⟨ofMatching M, hM⟩

/-- The rank lower bound for the shifted perfect-matching matrix transfers
to an approximate LP for the actual V-join solution set. The solution
inclusion is independent of the odd cut indexing the cost instance. -/
theorem vjoin_lp_lower_bound [Nonempty V]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (α : ℝ) (hα : 1 < α) {m L : ℕ}
    (C : CertifiedLP (V := E) (joinValue (V := V) α)
      (fun _ => (halfOrder V + penalty V α) / α) m)
    (source_lower_bound : (L : ℕ∞) ≤
      nonnegativeRank (fun U M => crossing (V := V) U M - 1 / (2 * α))) :
    L ≤ m + 1 := by
  let C' : CertifiedLP (V := E) (matchingValue (V := V) α)
      (fun _ => (halfOrder V + penalty V α) / α) m :=
    C.pullback id ofMatching
  exact matching_lp_lower_bound α hα C' source_lower_bound

end Lemmata.LPHardnessInP.Joins
