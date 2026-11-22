module

public import Lemmata.PlanarSteinerXC.Duality
public import Lemmata.PlanarSteinerXC.TwoTerminal
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Spanning cycles in the flag graph

Edge sets of the flag graph are represented by spanning subgraphs `D ≤ Γ` and by their
indicator vectors over `ZMod 2`. A connected `2`-regular spanning subgraph is a Hamiltonian cycle;
it has no nonempty proper even edge set, and conversely a `2`-regular spanning subgraph without
such edge sets is connected. Removing an edge `st` of a Hamiltonian cycle gives a Hamiltonian
`s`-`t` path of `Γ - st`, and every Hamiltonian `s`-`t` path of `Γ - st` arises in this way.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

/-- A nonempty acyclic graph has a vertex of odd degree (a leaf). -/
theorem IsAcyclic.exists_odd_degree {W : Type*} [Fintype W] {Z : SimpleGraph W} [DecidableRel Z.Adj]
    (hZ : Z.IsAcyclic) {a b : W} (hab : Z.Adj a b) : ∃ x, Z.degree x = 1 := by
  classical
  let c := Z.connectedComponentMk a
  have htree := hZ.isTree_connectedComponent c
  have ha : a ∈ c.supp := rfl
  have hb : b ∈ c.supp := by
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact hab.reachable.symm
  have hnt : Nontrivial c.supp := ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab.ne (congrArg Subtype.val h)⟩⟩
  obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
  refine ⟨x, ?_⟩
  have hsub : Z.neighborSet x ⊆ c.supp := by
    intro y hy
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    have hxc : (x : W) ∈ c.supp := x.2
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hxc
    exact (Adj.reachable hy).symm.trans hxc
  have := degree_induce_of_neighborSet_subset (G := Z) (s := c.supp) (v := x) hsub
  rw [← this]
  convert hx using 2
  · rfl

namespace FlagSystem

variable {Φ Q0 Q1 Q2 : Type*} (F : FlagSystem Φ Q0 Q1 Q2)
variable [DecidableEq Q0] [DecidableEq Q1] [DecidableEq Q2] [Fintype Φ] [DecidableEq Φ]

/-- The indicator vector over `ZMod 2` of a spanning subgraph, on the edges of `Γ`. -/
noncomputable def zvec (D : SimpleGraph Φ) : F.graph.edgeSet → ZMod 2 :=
  fun ε => by classical exact if (ε : Sym2 Φ) ∈ D.edgeSet then 1 else 0

theorem zvec_eq_one_iff (D : SimpleGraph Φ) (ε : F.graph.edgeSet) :
    F.zvec D ε = 1 ↔ (ε : Sym2 Φ) ∈ D.edgeSet := by
  classical
  unfold zvec; split_ifs with h <;> simp [h]

theorem zvec_eq_zero_iff (D : SimpleGraph Φ) (ε : F.graph.edgeSet) :
    F.zvec D ε = 0 ↔ (ε : Sym2 Φ) ∉ D.edgeSet := by
  classical
  unfold zvec; split_ifs with h <;> simp [h]

/-- `D` uses exactly two of the three edges at every flag. -/
def TwoRegular (D : SimpleGraph Φ) : Prop :=
  D ≤ F.graph ∧ ∀ φ, {i : Fin 3 | D.Adj φ (F.tau i φ)}.ncard = 2

theorem adj_iff_tau {D : SimpleGraph Φ} (hD : D ≤ F.graph) {φ ψ : Φ} :
    D.Adj φ ψ ↔ ∃ i, ψ = F.tau i φ ∧ D.Adj φ (F.tau i φ) := by
  constructor
  · intro h
    rcases F.edge_cases (hD h) with rfl | rfl | rfl
    · exact ⟨0, rfl, h⟩
    · exact ⟨1, rfl, h⟩
    · exact ⟨2, rfl, h⟩
  · rintro ⟨i, rfl, h⟩; exact h

theorem sum_inc_zvec (D : SimpleGraph Φ) (φ : Φ) :
    ∑ ε ∈ F.inc φ, F.zvec D ε = ({i : Fin 3 | D.Adj φ (F.tau i φ)}.ncard : ZMod 2) := by
  classical
  rw [F.inc_eq, Finset.sum_image (fun i _ j _ h => F.edgeAt_injective φ h),
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [zvec, edgeAt, mem_edgeSet]

theorem zvec_isEven {D : SimpleGraph Φ} (hD : F.TwoRegular D) : F.IsEven (F.zvec D) := by
  intro φ
  rw [F.sum_inc_zvec, hD.2 φ]
  rfl

/-- Every edge of `Γ` is an edge at one of its endpoints. -/
theorem exists_edgeAt (ε : F.graph.edgeSet) : ∃ φ i, ε = F.edgeAt φ i := by
  obtain ⟨ε, hε⟩ := ε
  induction ε using Sym2.ind with
  | h a b =>
    have hadj : F.graph.Adj a b := F.graph.mem_edgeSet.mp hε
    rcases F.edge_cases hadj with rfl | rfl | rfl
    · exact ⟨a, 0, rfl⟩
    · exact ⟨a, 1, rfl⟩
    · exact ⟨a, 2, rfl⟩

/-- **A connected `2`-regular spanning subgraph has no nonempty proper even edge set.** -/
theorem even_sub_of_connected {D : SimpleGraph Φ} (hD : F.TwoRegular D) (hconn : D.Connected)
    (z : F.graph.edgeSet → ZMod 2) (hz : F.IsEven z)
    (hsub : ∀ ε, z ε ≠ 0 → (ε : Sym2 Φ) ∈ D.edgeSet) : z = 0 ∨ z = F.zvec D := by
  classical
  -- `U`: flags at which `z` does not vanish
  let U : Set Φ := {φ | ∃ i, z (F.edgeAt φ i) ≠ 0}
  have hval : ∀ φ i, z (F.edgeAt φ i) = 0 ∨ z (F.edgeAt φ i) = 1 := fun φ i => zmod2_cases _
  -- at a flag in `U`, all `D`-edges carry `1`
  have hfull : ∀ φ ∈ U, ∀ i, D.Adj φ (F.tau i φ) → z (F.edgeAt φ i) = 1 := by
    intro φ hφ i hi
    obtain ⟨j, hj⟩ := hφ
    have hjD : D.Adj φ (F.tau j φ) := hsub _ hj
    have hsum := hz φ
    rw [F.sum_inc] at hsum
    have h2 := hD.2 φ
    -- the third edge is not in `D`
    by_contra hne
    have hzi : z (F.edgeAt φ i) = 0 := (hval φ i).resolve_right hne
    have hij : i ≠ j := fun h => by rw [h] at hzi; exact hj hzi
    have hzj : z (F.edgeAt φ j) = 1 := (hval φ j).resolve_left hj
    obtain ⟨k, hk⟩ : ∃ k, k ≠ i ∧ k ≠ j ∧ ∀ l, l = i ∨ l = j ∨ l = k := by
      fin_cases i <;> fin_cases j <;> simp_all <;> first
        | exact ⟨2, by decide, by decide, by decide⟩
        | exact ⟨1, by decide, by decide, by decide⟩
        | exact ⟨0, by decide, by decide, by decide⟩
    have hkD : ¬ D.Adj φ (F.tau k φ) := by
      intro hkD
      have : {l : Fin 3 | D.Adj φ (F.tau l φ)} = Set.univ := by
        ext l; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rcases hk.2.2 l with rfl | rfl | rfl <;> assumption
      rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
      norm_num at h2
    have hzk : z (F.edgeAt φ k) = 0 := by
      by_contra h; exact hkD (hsub _ h)
    have : z (F.edgeAt φ 0) + z (F.edgeAt φ 1) + z (F.edgeAt φ 2) = 1 := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> decide
    rw [this] at hsum
    exact one_ne_zero hsum
  -- `U` is closed under `D`-adjacency
  have hclosed : ∀ φ ψ, D.Adj φ ψ → φ ∈ U → ψ ∈ U := by
    intro φ ψ hadj hφ
    obtain ⟨i, rfl, hi⟩ := (F.adj_iff_tau hD.1).mp hadj
    have h1 := hfull φ hφ i hi
    -- the same edge seen from `ψ`
    obtain ⟨j, hj⟩ : ∃ j, F.edgeAt (F.tau i φ) j = F.edgeAt φ i := by
      fin_cases i
      · exact ⟨0, Subtype.ext (by simp [edgeAt, tau, F.τ0_inv, Sym2.eq_swap])⟩
      · exact ⟨1, Subtype.ext (by simp [edgeAt, tau, F.τ1_inv, Sym2.eq_swap])⟩
      · exact ⟨2, Subtype.ext (by simp [edgeAt, tau, F.τ2_inv, Sym2.eq_swap])⟩
    exact ⟨j, by rw [hj, h1]; exact one_ne_zero⟩
  have hconst : ∀ φ ψ, φ ∈ U → ψ ∈ U := by
    intro φ ψ hφ
    obtain ⟨p⟩ := hconn.preconnected φ ψ
    induction p with
    | nil => exact hφ
    | cons h _ ih => exact ih (hclosed _ _ h hφ)
  by_cases hU : ∃ φ, φ ∈ U
  · right
    obtain ⟨φ₀, hφ₀⟩ := hU
    funext ε
    obtain ⟨φ, i, rfl⟩ := F.exists_edgeAt ε
    by_cases hi : D.Adj φ (F.tau i φ)
    · rw [hfull φ (hconst φ₀ φ hφ₀) i hi, eq_comm, zvec_eq_one_iff]; exact hi
    · have : z (F.edgeAt φ i) = 0 := by
        by_contra h; exact hi (hsub _ h)
      rw [this, eq_comm, zvec_eq_zero_iff]; exact hi
  · left
    push Not at hU
    funext ε
    obtain ⟨φ, i, rfl⟩ := F.exists_edgeAt ε
    by_contra h
    exact hU φ ⟨i, h⟩

theorem neighborSet_eq_image {D : SimpleGraph Φ} (hD : D ≤ F.graph) (φ : Φ) :
    D.neighborSet φ = (fun i => F.tau i φ) '' {i : Fin 3 | D.Adj φ (F.tau i φ)} := by
  ext ψ
  simp only [mem_neighborSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨i, rfl, hi⟩ := (F.adj_iff_tau hD).mp h
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact hi

theorem ncard_neighborSet {D : SimpleGraph Φ} (hD : D ≤ F.graph) (φ : Φ) :
    (D.neighborSet φ).ncard = {i : Fin 3 | D.Adj φ (F.tau i φ)}.ncard := by
  rw [F.neighborSet_eq_image hD, Set.ncard_image_of_injective _ (F.tau_index_injective φ)]

theorem isCycles_of_twoRegular {D : SimpleGraph Φ} (hD : F.TwoRegular D) : D.IsCycles := by
  intro φ _
  rw [F.ncard_neighborSet hD.1, hD.2 φ]

theorem twoRegular_of_isCycles {D : SimpleGraph Φ} (hle : D ≤ F.graph) (hc : D.IsCycles)
    (hne : ∀ φ, (D.neighborSet φ).Nonempty) : F.TwoRegular D :=
  ⟨hle, fun φ => by rw [← F.ncard_neighborSet hle]; exact hc (hne φ)⟩

/-- **A `2`-regular spanning subgraph without nonempty proper even edge sets is connected.** -/
theorem connected_of_minimal [Nonempty Φ] {D : SimpleGraph Φ} (hD : F.TwoRegular D)
    (hmin : ∀ z, F.IsEven z → (∀ ε, z ε ≠ 0 → (ε : Sym2 Φ) ∈ D.edgeSet) →
      z = 0 ∨ z = F.zvec D) : D.Connected := by
  classical
  obtain ⟨φ₀⟩ := (inferInstance : Nonempty Φ)
  let D₁ : SimpleGraph Φ :=
    { Adj := fun a b => D.Adj a b ∧ D.Reachable φ₀ a
      symm := ⟨fun a b ⟨h, hr⟩ => ⟨h.symm, hr.trans h.reachable⟩⟩
      loopless := ⟨fun a ⟨h, _⟩ => h.ne rfl⟩ }
  have hD₁ : D₁ ≤ D := fun a b h => h.1
  have hreg : ∀ φ, D.Reachable φ₀ φ →
      {i : Fin 3 | D₁.Adj φ (F.tau i φ)} = {i : Fin 3 | D.Adj φ (F.tau i φ)} := by
    intro φ hφ; ext i; simp only [Set.mem_ofPred_eq]; exact ⟨fun h => h.1, fun h => ⟨h, hφ⟩⟩
  have hunreg : ∀ φ, ¬ D.Reachable φ₀ φ → {i : Fin 3 | D₁.Adj φ (F.tau i φ)} = ∅ := by
    intro φ hφ; ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hφ h.2
  have heven : F.IsEven (F.zvec D₁) := by
    intro φ
    rw [F.sum_inc_zvec]
    by_cases hφ : D.Reachable φ₀ φ
    · rw [hreg φ hφ, hD.2 φ]; rfl
    · rw [hunreg φ hφ, Set.ncard_empty]; rfl
  have hsub : ∀ ε, F.zvec D₁ ε ≠ 0 → (ε : Sym2 Φ) ∈ D.edgeSet := by
    intro ε h
    rw [ne_eq, zvec_eq_zero_iff, not_not] at h
    exact edgeSet_mono hD₁ h
  have hpos : ∃ i, D.Adj φ₀ (F.tau i φ₀) := by
    have h2 := hD.2 φ₀
    obtain ⟨i, hi⟩ : {i : Fin 3 | D.Adj φ₀ (F.tau i φ₀)}.Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero; rw [h2]; norm_num
    exact ⟨i, hi⟩
  rcases hmin _ heven hsub with h0 | h1
  · exfalso
    obtain ⟨i, hi⟩ := hpos
    have := congrFun h0 (F.edgeAt φ₀ i)
    rw [Pi.zero_apply, zvec_eq_zero_iff] at this
    exact this ⟨hi, Reachable.refl _⟩
  · refine (connected_iff_exists_forall_reachable _).mpr ⟨φ₀, fun ψ => ?_⟩
    have h2 := hD.2 ψ
    obtain ⟨j, hj⟩ : {i : Fin 3 | D.Adj ψ (F.tau i ψ)}.Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero; rw [h2]; norm_num
    have hz : F.zvec D (F.edgeAt ψ j) = 1 := (zvec_eq_one_iff _ _ _).mpr hj
    rw [← h1, zvec_eq_one_iff] at hz
    change D₁.Adj ψ (F.tau j ψ) at hz
    exact hz.2

/-- The graph `Γ - st`. -/
abbrev minus (s t : Φ) : SimpleGraph Φ := F.graph.deleteEdges {s(s, t)}

/-- **From a Hamiltonian cycle to a Hamiltonian path.** A connected `2`-regular spanning subgraph
through the edge `st` gives a Hamiltonian `s`-`t` path of `Γ - st` with the remaining edges. -/
theorem exists_hamiltonian_path {D : SimpleGraph Φ} (hD : F.TwoRegular D) (hconn : D.Connected)
    {s t : Φ} (hst : D.Adj s t) :
    ∃ p : (F.minus s t).Walk s t, p.IsHamiltonian ∧ walkGraph p = D.deleteEdges {s(s, t)} := by
  classical
  have hcyc := F.isCycles_of_twoRegular hD
  obtain ⟨c, hc, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := D.connectedComponentMk s) rfl ⟨t, hst⟩
  have hall : ∀ v, v ∈ c.toSubgraph.verts := by
    intro v; rw [hverts, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact hconn.preconnected v s
  have hsuppall : ∀ v, v ∈ c.support := fun v => c.mem_verts_toSubgraph.mp (hall v)
  have hadjiff : ∀ v w, c.toSubgraph.Adj v w ↔ D.Adj v w :=
    fun v w => hc.adj_toSubgraph_iff_of_isCycles hcyc (hall v) w
  -- choose the orientation in which `t` follows `s`
  obtain ⟨c', hc', hsupp', hadj', hsnd⟩ : ∃ c' : D.Walk s s, c'.IsCycle ∧
      (∀ v, v ∈ c'.support) ∧ (∀ v w, c'.toSubgraph.Adj v w ↔ D.Adj v w) ∧ c'.snd = t := by
    have ht : t ∈ c.toSubgraph.neighborSet s := (hadjiff s t).mpr hst
    rw [hc.neighborSet_toSubgraph_endpoint] at ht
    rcases ht with h | h
    · exact ⟨c, hc, hsuppall, hadjiff, h.symm⟩
    · refine ⟨c.reverse, hc.reverse, ?_, ?_, ?_⟩
      · intro v
        rw [Walk.support_reverse, List.mem_reverse]
        exact hsuppall v
      · intro v w
        rw [Walk.toSubgraph_reverse]
        exact hadjiff v w
      · rw [Walk.snd_reverse]
        exact (Set.mem_singleton_iff.mp h).symm
  have hnil : ¬ c'.Nil := hc'.not_nil
  have hcons := c'.cons_tail_eq hnil
  set q := c'.tail with hq
  have hcq : (Walk.cons (c'.adj_snd hnil) q).IsCycle := by rw [hcons]; exact hc'
  rw [Walk.cons_isCycle_iff] at hcq
  obtain ⟨hqpath, hqst⟩ := hcq
  -- `q` runs from `t` to `s`; reverse it and transfer it to `Γ - st`
  have hsndt := hsnd
  let q' : D.Walk c'.snd s := q
  have hedges : ∀ e ∈ q'.reverse.edges, e ∈ (F.minus s t).edgeSet := by
    intro e he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    rw [edgeSet_deleteEdges]
    refine ⟨edgeSet_mono hD.1 (q'.edges_subset_edgeSet he), ?_⟩
    rintro rfl
    have he' := he
    rw [← hsndt] at he'
    exact hqst he'
  let p₀ := q'.reverse.transfer (F.minus s t) hedges
  have hp₀path : p₀.IsPath := (Walk.isPath_transfer _).mpr hqpath.reverse
  have hsuppq : ∀ v, v ∈ q'.reverse.support := by
    intro v
    have hv := hsupp' v
    rw [← hcons, Walk.support_cons] at hv
    rw [Walk.support_reverse, List.mem_reverse]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact q'.end_mem_support
    · exact hv
  have hp₀ham : p₀.IsHamiltonian := by
    apply hp₀path.isHamiltonian_of_mem
    intro v
    rw [Walk.support_transfer]; exact hsuppq v
  -- the endpoint is `t`
  have key : ∀ (t' : Φ) (ht' : c'.snd = t'), ∃ p : (F.minus s t).Walk s t', p.IsHamiltonian ∧
      walkGraph p = D.deleteEdges {s(s, t)} := by
    rintro t' rfl
    refine ⟨p₀, hp₀ham, ?_⟩
    rw [← edgeSet_inj, walkGraph_edgeSet, edgeSet_deleteEdges]
    ext e
    simp only [Walk.edgeSet, Set.mem_ofPred_eq, Set.mem_diff, Set.mem_singleton_iff]
    rw [Walk.edges_transfer, Walk.edges_reverse, List.mem_reverse]
    constructor
    · intro he
      refine ⟨q'.edges_subset_edgeSet he, ?_⟩
      rintro rfl
      have he' := he
      rw [← hsndt] at he'
      exact hqst he'
    · rintro ⟨heD, hne⟩
      induction e using Sym2.ind with
      | h a b =>
        have hab : D.Adj a b := heD
        have hc'ab : c'.toSubgraph.Adj a b := (hadj' a b).mpr hab
        rw [Walk.adj_toSubgraph_iff_mem_edges, ← hcons, Walk.edges_cons] at hc'ab
        rcases List.mem_cons.mp hc'ab with h | h
        · exact absurd (h.trans (by rw [hsndt])) hne
        · exact h
  exact key t hsnd

/-- **From a Hamiltonian path to a Hamiltonian cycle.** -/
theorem twoRegular_of_hamiltonian_path {s t : Φ} (hst : F.graph.Adj s t)
    (p : (F.minus s t).Walk s t) (hp : p.IsHamiltonian) :
    F.TwoRegular (walkGraph p ⊔ edge s t) ∧ (walkGraph p ⊔ edge s t).Connected := by
  classical
  have hne : s ≠ t := hst.ne
  have hle : walkGraph p ⊔ edge s t ≤ F.graph := by
    refine sup_le ((walkGraph_le p).trans (deleteEdges_le _)) ?_
    intro a b h
    rw [edge_adj] at h
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hst
    · exact hst.symm
  have hnotin : s(t, s) ∉ p.edges := by
    intro h
    have := p.edges_subset_edgeSet h
    rw [edgeSet_deleteEdges] at this
    exact this.2 (by rw [Sym2.eq_swap]; rfl)
  have hcyc := hp.isPath.isCycles_spanningCoe_toSubgraph_sup_edge hne hnotin
  rw [edge_comm] at hcyc
  have hconn : (walkGraph p ⊔ edge s t).Connected :=
    (walkGraph_connected_of_isHamiltonian p hp).mono le_sup_left
  refine ⟨F.twoRegular_of_isCycles hle hcyc fun φ => ?_, hconn⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ ≠ φ := by
    by_cases h : s = φ
    · exact ⟨t, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨s, h⟩
  obtain ⟨w⟩ := hconn.preconnected φ ψ
  cases w with
  | nil => exact absurd rfl hψ
  | cons h _ => exact ⟨_, h⟩


end FlagSystem

end Lemmata.PlanarSteinerXC
