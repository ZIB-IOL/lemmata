module

public import Lemmata.PlanarSteinerXC.Objects

/-!
# Planar face systems

A *planar face system* on a finite graph `G` is a finite family of faces, each an edge set in
which every vertex has degree `0` or `2`, such that every edge lies on exactly two faces, the
faces are connected through shared edges, `G` is connected, and Euler's formula
`|V| - |E| + |F| = 2` holds.

The facial cycles of a 2-connected plane graph form such a system. Conversely, a graph with a
planar face system is planar, by MacLane's criterion (Diestel, *Graph Theory*, Theorem 4.5.1).
Every face lies in the cycle space over `ZMod 2`. Since every edge lies on exactly two faces and
the faces are connected through shared edges, the only nonempty set of faces with zero sum is the
set of all faces, so the faces span a space of dimension `|F| - 1 = |E| - |V| + 1` (Euler), the
whole cycle space of the connected graph `G`. Dropping one face therefore gives a basis of the
cycle space in which every edge lies on at most two members.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges of an edge set `F` at a vertex `v`. -/
def edgeDeg (F : Finset (Sym2 V)) (v : V) : ℕ := (F.filter (fun e => v ∈ e)).card

/-- A planar face system on `G`. -/
structure PlanarFaces.{u} {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W) :
    Type (u + 1) where
  /-- The faces. -/
  Face : Type u
  [instFintype : Fintype Face]
  [instDecEq : DecidableEq Face]
  /-- The boundary edges of each face. -/
  edges : Face → Finset (Sym2 W)
  edges_subset : ∀ f, ∀ e ∈ edges f, e ∈ G.edgeSet
  /-- Faces are nonempty. -/
  edges_nonempty : ∀ f, (edges f).Nonempty
  /-- Every face is an even subgraph in which every vertex has degree `0` or `2`. -/
  edgeDeg_eq : ∀ f v, edgeDeg (edges f) v = 0 ∨ edgeDeg (edges f) v = 2
  /-- Every edge lies on exactly two faces. -/
  two_faces : ∀ e ∈ G.edgeSet, (Finset.univ.filter (fun f => e ∈ edges f)).card = 2
  connected : G.Connected
  /-- The faces are connected through shared edges. -/
  dual_connected : (SimpleGraph.fromRel fun f g : Face => ∃ e, e ∈ edges f ∧ e ∈ edges g).Connected
  /-- Euler's formula `|V| - |E| + |F| = 2`. -/
  euler : Fintype.card W + Fintype.card Face = Nat.card G.edgeSet + 2

/-- `G` is planar: it has a planar face system. -/
def IsPlanar (G : SimpleGraph V) : Prop := Nonempty (PlanarFaces G)

namespace PlanarFaces

variable {G : SimpleGraph V} (S : PlanarFaces G)

attribute [instance] PlanarFaces.instFintype PlanarFaces.instDecEq

/-- The vertices on the boundary of a face. -/
def verts (f : S.Face) : Set V := {v | ∃ e ∈ S.edges f, v ∈ e}

/-- The dual graph: faces sharing an edge. -/
def dual : SimpleGraph S.Face :=
  SimpleGraph.fromRel fun f g : S.Face => ∃ e, e ∈ S.edges f ∧ e ∈ S.edges g

theorem dual_conn : S.dual.Connected := S.dual_connected

theorem exists_face_of_edge {e : Sym2 V} (he : e ∈ G.edgeSet) : ∃ f, e ∈ S.edges f := by
  have h := S.two_faces e he
  obtain ⟨f, hf⟩ : (Finset.univ.filter (fun f => e ∈ S.edges f)).Nonempty := by
    rw [← Finset.card_pos, h]; norm_num
  exact ⟨f, (Finset.mem_filter.mp hf).2⟩

/-- Every edge lies on two distinct faces. -/
theorem exists_two_faces {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ f g, f ≠ g ∧ e ∈ S.edges f ∧ e ∈ S.edges g := by
  have h := S.two_faces e he
  obtain ⟨f, g, hfg, hs⟩ := Finset.card_eq_two.mp h
  have hf : f ∈ Finset.univ.filter (fun f => e ∈ S.edges f) := by rw [hs]; simp
  have hg : g ∈ Finset.univ.filter (fun f => e ∈ S.edges f) := by rw [hs]; simp
  exact ⟨f, g, hfg, (Finset.mem_filter.mp hf).2, (Finset.mem_filter.mp hg).2⟩

/-- A vertex with an incident edge lies on some face. -/
theorem exists_face_of_adj {u v : V} (h : G.Adj u v) : ∃ f, u ∈ S.verts f := by
  obtain ⟨f, hf⟩ := S.exists_face_of_edge (G.mem_edgeSet.mpr h)
  exact ⟨f, s(u, v), hf, Sym2.mem_mk_left _ _⟩

theorem mem_edgeSet_of_mem {f : S.Face} {e : Sym2 V} (he : e ∈ S.edges f) : e ∈ G.edgeSet :=
  S.edges_subset f e he

/-- The faces around a vertex are connected through shared edges at that vertex. -/
def LinksConnected : Prop :=
  ∀ u f g, u ∈ S.verts f → u ∈ S.verts g →
    (SimpleGraph.fromRel fun a b : S.Face => ∃ e, e ∈ S.edges a ∧ e ∈ S.edges b ∧ u ∈ e).Reachable
      f g

theorem edgeDeg_pos_of_mem {f : S.Face} {u : V} (hu : u ∈ S.verts f) :
    0 < edgeDeg (S.edges f) u := by
  obtain ⟨e, he, hue⟩ := hu
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hue⟩⟩

theorem edgeDeg_eq_two_of_mem {f : S.Face} {u : V} (hu : u ∈ S.verts f) :
    edgeDeg (S.edges f) u = 2 := by
  rcases S.edgeDeg_eq f u with h | h
  · exact absurd h (Nat.pos_iff_ne_zero.mp (S.edgeDeg_pos_of_mem hu))
  · exact h

/-- At a vertex of degree at most three, any two faces through it share an edge at it. -/
theorem linksConnected_of_degree_le_three [DecidableRel G.Adj] (hdeg : ∀ u, G.degree u ≤ 3) :
    S.LinksConnected := by
  intro u f g hf hg
  by_cases hfg : f = g
  · rw [hfg]
  apply Adj.reachable
  rw [fromRel_adj]
  refine ⟨hfg, Or.inl ?_⟩
  -- the edges at `u` of `f` and of `g` are two-element subsets of the at most three edges at `u`
  let Af := (S.edges f).filter (fun e => u ∈ e)
  let Ag := (S.edges g).filter (fun e => u ∈ e)
  let Nu := G.incidenceFinset u
  have hAf : Af ⊆ Nu := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    exact mem_incidenceFinset.mpr ⟨S.edges_subset f e he1, he2⟩
  have hAg : Ag ⊆ Nu := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    exact mem_incidenceFinset.mpr ⟨S.edges_subset g e he1, he2⟩
  have hcf : Af.card = 2 := S.edgeDeg_eq_two_of_mem hf
  have hcg : Ag.card = 2 := S.edgeDeg_eq_two_of_mem hg
  have hcN : Nu.card ≤ 3 := by rw [card_incidenceFinset_eq_degree]; exact hdeg u
  have hunion : (Af ∪ Ag).card ≤ 3 := (Finset.card_le_card (Finset.union_subset hAf hAg)).trans hcN
  have hinter := Finset.card_union_add_card_inter Af Ag
  obtain ⟨e, he⟩ : (Af ∩ Ag).Nonempty := by
    rw [← Finset.card_pos]; lia
  obtain ⟨he1, he2⟩ := Finset.mem_inter.mp he
  exact ⟨e, (Finset.mem_filter.mp he1).1, (Finset.mem_filter.mp he2).1, (Finset.mem_filter.mp he1).2⟩

end PlanarFaces

end Lemmata.PlanarSteinerXC
