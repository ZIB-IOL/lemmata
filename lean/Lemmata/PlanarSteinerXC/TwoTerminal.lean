module

public import Lemmata.PlanarSteinerXC.Objects

/-!
# Two terminals: the Hamiltonian path face of `Pmin`

For two terminals, the inclusion-minimal connecting edge sets are exactly the edge sets of the
`s`-`t` paths; they have at most `n - 1` edges, with equality exactly for Hamiltonian paths.
Hence `HP G s t = Pmin G {s,t} ∩ {x : x(E) = n - 1}` (Feldmann and Rai, Lemma 9).
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

variable {V : Type*}

/-- The spanning subgraph formed by the edges of a walk. -/
abbrev walkGraph {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : SimpleGraph V :=
  p.toSubgraph.spanningCoe

theorem walkGraph_edgeSet {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    (walkGraph p).edgeSet = p.edgeSet := by
  rw [Subgraph.edgeSet_spanningCoe, Walk.edgeSet_toSubgraph]

theorem walkGraph_le {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : walkGraph p ≤ G :=
  p.toSubgraph.spanningCoe_le

theorem mem_walkGraph_edgeSet {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (e : Sym2 V) :
    e ∈ (walkGraph p).edgeSet ↔ e ∈ p.edges := by
  rw [walkGraph_edgeSet]; rfl

/-- A walk transferred into the graph of its own edges. -/
def Walk.inOwnGraph {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : (walkGraph p).Walk u v :=
  p.transfer (walkGraph p) (fun e he => (mem_walkGraph_edgeSet p e).mpr he)

theorem walkGraph_reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    (walkGraph p).Reachable u v :=
  ⟨Walk.inOwnGraph p⟩

theorem walkGraph_congr {G G' : SimpleGraph V} {u v u' v' : V} (p : G.Walk u v)
    (p' : G'.Walk u' v') (h : p.edges = p'.edges) : walkGraph p = walkGraph p' := by
  rw [← edgeSet_inj, walkGraph_edgeSet, walkGraph_edgeSet]
  ext e; simp [Walk.edgeSet, h]

theorem card_walkGraph_edgeSet {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    Nat.card (walkGraph p).edgeSet = p.length := by
  classical
  rw [walkGraph_edgeSet, Nat.card_coe_set_eq]
  have hset : p.edgeSet = ((p.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) := by
    ext e; simp [Walk.edgeSet]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
    Walk.length_edges]

theorem connects_pair_of_reachable {K : SimpleGraph V} {s t : V} (h : K.Reachable s t) :
    Connects K {s, t} := by
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Reachable.refl _
  · exact h
  · exact h.symm
  · exact Reachable.refl _

/-- A minimal `{s,t}`-connector is the edge set of an `s`-`t` path. -/
theorem IsMinConnector.exists_path {G K : SimpleGraph V} {s t : V}
    (h : IsMinConnector G {s, t} K) : ∃ q : K.Walk s t, q.IsPath ∧ K = walkGraph q := by
  classical
  obtain ⟨q⟩ := h.2.1 s (by simp) t (by simp)
  refine ⟨q.bypass, q.bypass_isPath, ?_⟩
  exact (h.2.2 _ (walkGraph_le _) (connects_pair_of_reachable (walkGraph_reachable _))).symm

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Minimal `{s,t}`-connectors have at most `n - 1` edges. -/
theorem IsMinConnector.card_le {G K : SimpleGraph V} {s t : V} (h : IsMinConnector G {s, t} K) :
    Nat.card K.edgeSet ≤ Fintype.card V - 1 := by
  obtain ⟨q, hq, hK⟩ := h.exists_path
  have hlt := hq.length_lt
  have : Nat.card K.edgeSet = q.length :=
    (congrArg (fun H : SimpleGraph V => Nat.card H.edgeSet) hK).trans
      (card_walkGraph_edgeSet q hq)
  lia

/-- A minimal `{s,t}`-connector with `n - 1` edges is a Hamiltonian path. -/
theorem IsMinConnector.exists_hamiltonian {G K : SimpleGraph V} {s t : V}
    (h : IsMinConnector G {s, t} K) (hc : Nat.card K.edgeSet = Fintype.card V - 1) :
    ∃ p : G.Walk s t, p.IsHamiltonian ∧ K = walkGraph p := by
  obtain ⟨q, hq, hK⟩ := h.exists_path
  have hlen : q.length = Fintype.card V - 1 := by
    have h1 : Nat.card K.edgeSet = q.length :=
      (congrArg (fun H : SimpleGraph V => Nat.card H.edgeSet) hK).trans
        (card_walkGraph_edgeSet q hq)
    lia
  have hqH : q.IsHamiltonian := Walk.isHamiltonian_iff_isPath_and_length_eq.mpr ⟨hq, hlen⟩
  refine ⟨q.mapLe h.1, (Walk.isHamiltonian_mapLe h.1).mpr hqH, ?_⟩
  exact hK.trans (walkGraph_congr _ _ (Walk.edges_mapLe_eq_edges _ _).symm)

omit [Fintype V] in
/-- The edge set of a Hamiltonian path is a connected spanning subgraph. -/
theorem walkGraph_connected_of_isHamiltonian {G : SimpleGraph V} {s t : V} (p : G.Walk s t)
    (hp : p.IsHamiltonian) : (walkGraph p).Connected := by
  have hs : ∀ v, (walkGraph p).Reachable s v := by
    intro v
    have hv := hp.mem_support v
    refine ⟨(p.takeUntil v hv).transfer (walkGraph p) ?_⟩
    intro e he
    exact (mem_walkGraph_edgeSet p e).mpr (p.edges_takeUntil_subset_edges hv he)
  exact (connected_iff_exists_forall_reachable _).mpr ⟨s, hs⟩

/-- The edge set of a Hamiltonian `s`-`t` path is a minimal `{s,t}`-connector with `n - 1`
edges. -/
theorem isMinConnector_of_isHamiltonian {G : SimpleGraph V} {s t : V} (p : G.Walk s t)
    (hp : p.IsHamiltonian) :
    IsMinConnector G {s, t} (walkGraph p) ∧
      Nat.card (walkGraph p).edgeSet = Fintype.card V - 1 := by
  have hpath := hp.isPath
  have hcard : Nat.card (walkGraph p).edgeSet = Fintype.card V - 1 := by
    rw [card_walkGraph_edgeSet p hpath, hp.length_eq]
  refine ⟨⟨walkGraph_le p, connects_pair_of_reachable (walkGraph_reachable p), ?_⟩, hcard⟩
  intro K' hK' hconn
  classical
  set K := walkGraph p with hKdef
  have htree : K.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨walkGraph_connected_of_isHamiltonian p hp, ?_⟩
    rw [hcard, Nat.card_eq_fintype_card]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    lia
  obtain ⟨q'⟩ := hconn s (by simp) t (by simp)
  set q'' : K.Walk s t := (q'.bypass).mapLe hK'
  have hq'' : q''.IsPath := (Walk.isPath_mapLe hK').mpr q'.bypass_isPath
  have hp' : (Walk.inOwnGraph p).IsPath := by
    unfold Walk.inOwnGraph
    exact (Walk.isPath_transfer _).mpr hpath
  have huniq : (⟨q'', hq''⟩ : K.Path s t) = ⟨Walk.inOwnGraph p, hp'⟩ :=
    (htree.isAcyclic.subsingleton_path s t).elim _ _
  have hedges : q'.bypass.edges = p.edges := by
    have := congrArg (fun r : K.Path s t => (r : K.Walk s t).edges) huniq
    simp only [q'', Walk.edges_mapLe_eq_edges] at this
    rw [this]
    unfold Walk.inOwnGraph
    rw [Walk.edges_transfer]
  apply le_antisymm hK'
  rw [← edgeSet_subset_edgeSet]
  intro e he
  rw [mem_walkGraph_edgeSet, ← hedges] at he
  exact (q'.bypass).edges_subset_edgeSet he

/-- **Feldmann–Rai, Lemma 9.** For two terminals, the Hamiltonian path polytope is the
face `x(E) = n - 1` of the minimal Steiner tree polytope. -/
theorem hp_eq_pmin_inter (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) :
    HP G s t = Pmin G {s, t} ∩ {x | sumOver Finset.univ x = (Fintype.card V : ℝ) - 1} := by
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Nat.cast_sub hpos, Nat.cast_one]
  unfold Pmin
  rw [convexHull_inter_hyperplane_of_le]
  · unfold HP
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, sumOver_apply]
    constructor
    · rintro ⟨K, ⟨p, hp, rfl⟩, rfl⟩
      obtain ⟨hmin, hcard⟩ := isMinConnector_of_isHamiltonian p hp
      refine ⟨⟨_, hmin, rfl⟩, ?_⟩
      rw [sum_edgeVec G _ hmin.1, hcard, hcast]
    · rintro ⟨⟨K, hK, rfl⟩, hsum⟩
      rw [sum_edgeVec G _ hK.1, ← hcast] at hsum
      have hc : Nat.card K.edgeSet = Fintype.card V - 1 := by exact_mod_cast hsum
      obtain ⟨p, hp, rfl⟩ := hK.exists_hamiltonian hc
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  · rintro x ⟨K, hK, rfl⟩
    rw [sumOver_apply, sum_edgeVec G _ hK.1, ← hcast]
    exact_mod_cast hK.card_le

/-- Consequently `xc (HP G s t) ≤ xc (Pmin G {s, t})`. -/
theorem xc_hp_le_pmin (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) :
    xc (HP G s t) ≤ xc (Pmin G {s, t}) := by
  rw [hp_eq_pmin_inter G s t]
  exact xc_inter_hyperplane_le _ _ _

end Lemmata.PlanarSteinerXC
