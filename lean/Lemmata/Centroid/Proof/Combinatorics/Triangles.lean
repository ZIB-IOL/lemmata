module

public import Lemmata.Centroid.Def.Bounds
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

namespace Lemmata.Centroid

open Finset
open scoped BigOperators

namespace Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_positive_degree_lt {a : ℕ} (hG : G ≠ ⊥)
    (hE : G.edgeFinset.card < (a + 1).choose 2) :
    ∃ v, 0 < G.degree v ∧ G.degree v < a := by
  classical
  by_contra h
  have hall : ∀ v ∈ G.support, a ≤ G.degree v := by
    intro v hv
    have hp := (G.degree_pos_iff_mem_support v).2 hv
    exact Nat.le_of_not_gt fun hn => h ⟨v, hp, hn⟩
  obtain ⟨v, w, hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.1 hG
  have hv : v ∈ G.support := (G.degree_pos_iff_mem_support v).1 hvw.degree_pos_left
  have hsubset : G.neighborFinset v ⊆ G.support.toFinset.erase v := by
    intro w hw
    have ha := (G.mem_neighborFinset v w).1 hw
    exact Finset.mem_erase.2 ⟨ha.ne.symm, Set.mem_toFinset.2
      ((G.degree_pos_iff_mem_support w).1 ha.degree_pos_right)⟩
  have hdegree := Finset.card_le_card hsubset
  rw [G.card_neighborFinset_eq_degree,
    Finset.card_erase_of_mem (Set.mem_toFinset.2 hv)] at hdegree
  have hcard : a < G.support.toFinset.card := by
    have := hall v hv
    have := Finset.card_pos.2 ⟨v, Set.mem_toFinset.2 hv⟩
    omega
  have hsum : a * G.support.toFinset.card ≤ 2 * G.edgeFinset.card := by
    calc
      a * G.support.toFinset.card = ∑ _ ∈ G.support.toFinset, a := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ G.support.toFinset, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hall v (Set.mem_toFinset.1 hv)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_support_eq_twice_card_edges
  have hchoose := two_mul_choose_two_succ a
  have hprod := Nat.mul_le_mul_left a (Nat.succ_le_of_lt hcard)
  nlinarith

theorem triangles_delete (v : V) :
    (G.deleteIncidenceSet v).cliqueFinset 3 = (G.cliqueFinset 3).filter (v ∉ ·) := by
  classical
  ext s
  simp only [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_filter]
  constructor
  · intro hs
    refine ⟨hs.mono (G.deleteIncidenceSet_le v), ?_⟩
    intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne (by rw [hs.card_eq]; omega : 1 < s.card) v
    have hadj := hs.isClique hw hv hwv
    exact (SimpleGraph.deleteIncidenceSet_adj.1 hadj).2.2 rfl
  · rintro ⟨hs, hv⟩
    refine ⟨?_, hs.card_eq⟩
    intro x hx y hy hxy
    exact SimpleGraph.deleteIncidenceSet_adj.2
      ⟨hs.isClique hx hy hxy, fun h => hv (h ▸ hx), fun h => hv (h ▸ hy)⟩

theorem triangles_through_vertex_le (v : V) :
    ((G.cliqueFinset 3).filter (v ∈ ·)).card ≤ (G.degree v).choose 2 := by
  classical
  rw [← G.card_neighborFinset_eq_degree, ← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn (fun s => s.erase v)
  · intro s hs
    obtain ⟨hs, hv⟩ := Finset.mem_filter.1 hs
    have hc := SimpleGraph.mem_cliqueFinset_iff.1 hs
    apply Finset.mem_powersetCard.2
    constructor
    · intro w hw
      obtain ⟨hwv, hw⟩ := Finset.mem_erase.1 hw
      exact (G.mem_neighborFinset v w).2 (hc.isClique hv hw hwv.symm)
    · rw [Finset.card_erase_of_mem hv, hc.card_eq]
  · intro s hs t ht hst
    have hv₁ := (Finset.mem_filter.1 hs).2
    have hv₂ := (Finset.mem_filter.1 ht).2
    calc
      s = insert v (s.erase v) := (Finset.insert_erase hv₁).symm
      _ = insert v (t.erase v) := congrArg (insert v) hst
      _ = t := Finset.insert_erase hv₂

theorem triangles_le_delete_add (v : V) :
    (G.cliqueFinset 3).card ≤ ((G.deleteIncidenceSet v).cliqueFinset 3).card +
      (G.degree v).choose 2 := by
  classical
  rw [triangles_delete]
  have hsplit := Finset.card_filter_add_card_filter_not (s := G.cliqueFinset 3) (v ∈ ·)
  have hbound := triangles_through_vertex_le G v
  omega

theorem triangle_bound (a b : ℕ) (hb : b < a)
    (hE : G.edgeFinset.card = a.choose 2 + b) :
    (G.cliqueFinset 3).card ≤ triangleBoundAt a b := by
  classical
  have aux : ∀ E : ℕ, ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (a b : ℕ),
      b < a → H.edgeFinset.card = E → E = a.choose 2 + b →
      (H.cliqueFinset 3).card ≤ triangleBoundAt a b := by
    intro E
    induction E using Nat.strong_induction_on with
    | h E ih =>
      intro H _ a b hb hcount hrepr
      by_cases hH : H = ⊥
      · subst H
        simp [SimpleGraph.cliqueFinset, SimpleGraph.isNClique_bot_iff]
      have hupper : H.edgeFinset.card < (a + 1).choose 2 := by
        have hnext : (a + 1).choose 2 = a + a.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' a 1
        rw [hcount, hrepr, hnext]
        omega
      obtain ⟨v, hv, hva⟩ := exists_positive_degree_lt H hH hupper
      have hdE : H.degree v ≤ E := hcount ▸ H.degree_le_card_edgeFinset v
      have hlt : (H.deleteIncidenceSet v).edgeFinset.card < E := by
        rw [H.card_edgeFinset_deleteIncidenceSet, hcount]
        omega
      have hsplit := triangles_le_delete_add H v
      by_cases hdb : H.degree v ≤ b
      · have hrepr' : (H.deleteIncidenceSet v).edgeFinset.card =
            a.choose 2 + (b - H.degree v) := by
          rw [H.card_edgeFinset_deleteIncidenceSet, hcount, hrepr]
          omega
        have hrec := ih _ hlt (H.deleteIncidenceSet v) a (b - H.degree v)
          (by omega) rfl hrepr'
        exact hsplit.trans ((Nat.add_le_add_right hrec _).trans
          (triangleBoundAt_delete_small a b (H.degree v) hdb))
      · have hba : b < H.degree v := by omega
        have ha : 0 < a := by omega
        have hbin : a.choose 2 = (a - 1).choose 2 + (a - 1) := by
          conv_lhs => rw [show a = (a - 1) + 1 by omega]
          rw [Nat.choose_succ_succ' _ 1, Nat.choose_one_right]
          exact Nat.add_comm _ _
        have hrepr' : (H.deleteIncidenceSet v).edgeFinset.card =
            (a - 1).choose 2 + (a - 1 + b - H.degree v) := by
          rw [H.card_edgeFinset_deleteIncidenceSet, hcount, hrepr, hbin]
          omega
        have hrec := ih _ hlt (H.deleteIncidenceSet v) (a - 1)
          (a - 1 + b - H.degree v) (by omega) rfl hrepr'
        exact hsplit.trans ((Nat.add_le_add_right hrec _).trans
          (triangleBoundAt_delete_large a b (H.degree v) hba hva))
  exact aux _ G a b hb rfl hE

theorem triangle_bound_edges : (G.cliqueFinset 3).card ≤ triangleBound G.edgeFinset.card := by
  rw [triangleBound]
  exact triangle_bound G _ _ (edge_remainder_lt _) (edge_decomposition _)

end Graph

end Lemmata.Centroid
