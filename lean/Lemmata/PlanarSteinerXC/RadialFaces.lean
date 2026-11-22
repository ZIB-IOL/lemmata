module

public import Lemmata.PlanarSteinerXC.FlagGraph
public import Lemmata.PlanarSteinerXC.ForestDual

/-!
# The face system of the radial graph

The faces of `H` are the sides `(φ, e)`, i.e. the quadrilaterals `u q_e w f_φ` for `e = uw`.
Every edge of `H` is a half-edge `u q_e` (a dart of `J`) or a spoke `u f_φ` (a corner of `J`).
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

namespace PlanarFaces

variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} (S : PlanarFaces J)

/-- The edge of `H` represented by a dart or a corner of `J`. -/
def hEdge : J.Dart ⊕ S.Corner → Sym2 S.RadV
  | .inl d => s(.inl d.fst, .inr (.inl ⟨d.edge, d.edge_mem⟩))
  | .inr c => s(.inl c.vert, .inr (.inr c.face))

theorem hEdge_mem (a : J.Dart ⊕ S.Corner) : S.hEdge a ∈ S.radial.edgeSet := by
  rcases a with d | c
  · rw [hEdge, mem_edgeSet]
    exact Sym2.mem_mk_left _ _
  · rw [hEdge, mem_edgeSet]
    exact c.vert_mem

theorem hEdge_injective : Function.Injective S.hEdge := by
  rintro (d | c) (d' | c') h <;> simp only [hEdge, Sym2.eq_iff] at h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · simp only [Sum.inl.injEq, Sum.inr.injEq, Subtype.mk.injEq] at h1 h2
      congr 1
      ext
      · exact h1
      · have h3 := h2
        rw [Dart.edge, Dart.edge] at h3
        rw [h1] at h3
        exact Sym2.congr_right.mp h3
    · exact absurd h1 (by simp)
  · rcases h with ⟨-, h2⟩ | ⟨h1, -⟩ <;> simp at *
  · rcases h with ⟨-, h2⟩ | ⟨h1, -⟩ <;> simp at *
  · rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2
      congr 1
      ext
      · exact h2
      · exact h1
    · exact absurd h1 (by simp)

theorem hEdge_surj {ε : Sym2 S.RadV} (hε : ε ∈ S.radial.edgeSet) : ∃ a, S.hEdge a = ε := by
  induction ε using Sym2.ind with
  | h x y =>
    have h := S.radial.mem_edgeSet.mp hε
    rcases S.radial_adj_cases h with ⟨v, t, rfl, rfl⟩ | ⟨v, t, rfl, rfl⟩
    · rcases t with ⟨e, he⟩ | f
      · have hv : v ∈ e := h
        refine ⟨.inl ⟨(v, otherEnd v e), adj_otherEnd hv he⟩, ?_⟩
        simp only [hEdge, Dart.edge]
        congr 3
        exact Subtype.ext (otherEnd_spec hv)
      · exact ⟨.inr ⟨f, v, h⟩, rfl⟩
    · rcases t with ⟨e, he⟩ | f
      · have hv : v ∈ e := h
        refine ⟨.inl ⟨(v, otherEnd v e), adj_otherEnd hv he⟩, ?_⟩
        simp only [hEdge, Dart.edge]
        rw [Sym2.eq_swap]
        congr 3
        exact Subtype.ext (otherEnd_spec hv)
      · exact ⟨.inr ⟨f, v, h⟩, Sym2.eq_swap⟩

/-- The four edges of a side. -/
noncomputable def sideEdges (σ : S.Side) : Finset (Sym2 S.RadV) := by
  classical
  exact Finset.univ.filter fun ε => ∃ x ∈ σ.edge,
    ε = s(.inl x, .inr (.inl ⟨σ.edge, S.mem_edgeSet_of_mem σ.edge_mem⟩)) ∨
    ε = s(.inl x, .inr (.inr σ.face))

theorem mem_sideEdges {σ : S.Side} {ε : Sym2 S.RadV} :
    ε ∈ S.sideEdges σ ↔ ∃ x ∈ σ.edge,
      ε = s(.inl x, .inr (.inl ⟨σ.edge, S.mem_edgeSet_of_mem σ.edge_mem⟩)) ∨
      ε = s(.inl x, .inr (.inr σ.face)) := by
  classical
  simp [sideEdges]

/-- A `4`-cycle has degree `2` at its vertices and `0` elsewhere. -/
theorem edgeDeg_square {W : Type*} [DecidableEq W] {a b c d : W} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (y : W) :
    edgeDeg ({s(a, b), s(c, b), s(a, d), s(c, d)} : Finset (Sym2 W)) y = 0 ∨
      edgeDeg ({s(a, b), s(c, b), s(a, d), s(c, d)} : Finset (Sym2 W)) y = 2 := by
  unfold edgeDeg
  by_cases ya : y = a
  · subst ya; right
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [Sym2.mem_iff, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had]
  by_cases yb : y = b
  · subst yb; right
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [Sym2.mem_iff, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hbc, Ne.symm hbd]
  by_cases yc : y = c
  · subst yc; right
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [Sym2.mem_iff, hab, hac, had, hbc, hbd, hcd, Ne.symm hac, Ne.symm hbc, Ne.symm hcd]
  by_cases yd : y = d
  · subst yd; right
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [Sym2.mem_iff, hab, hac, had, hbc, hbd, hcd, Ne.symm had, Ne.symm hbd, Ne.symm hcd]
  · left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hye
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [Sym2.mem_iff, ya, yb, yc, yd] at hye

theorem sideEdges_eq (σ : S.Side) {u w : V} (huw : σ.edge = s(u, w)) :
    S.sideEdges σ = {s(.inl u, .inr (.inl ⟨σ.edge, S.mem_edgeSet_of_mem σ.edge_mem⟩)),
      s(.inl w, .inr (.inl ⟨σ.edge, S.mem_edgeSet_of_mem σ.edge_mem⟩)),
      s(.inl u, .inr (.inr σ.face)), s(.inl w, .inr (.inr σ.face))} := by
  ext ε
  rw [mem_sideEdges]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, h | h⟩
    · rw [huw, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [huw, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · have hu : u ∈ σ.edge := by rw [huw]; exact Sym2.mem_mk_left _ _
    have hw : w ∈ σ.edge := by rw [huw]; exact Sym2.mem_mk_right _ _
    rintro (h | h | h | h)
    · exact ⟨u, hu, Or.inl h⟩
    · exact ⟨w, hw, Or.inl h⟩
    · exact ⟨u, hu, Or.inr h⟩
    · exact ⟨w, hw, Or.inr h⟩

theorem sideEdges_edgeDeg (σ : S.Side) (y : S.RadV) :
    edgeDeg (S.sideEdges σ) y = 0 ∨ edgeDeg (S.sideEdges σ) y = 2 := by
  obtain ⟨u, hu⟩ := exists_mem_sym2 σ.edge
  have huw := (otherEnd_spec hu).symm
  have hne : otherEnd u σ.edge ≠ u := otherEnd_ne hu (S.mem_edgeSet_of_mem σ.edge_mem)
  rw [S.sideEdges_eq σ huw]
  have := edgeDeg_square (a := (.inl u : S.RadV))
    (b := .inr (.inl ⟨σ.edge, S.mem_edgeSet_of_mem σ.edge_mem⟩))
    (c := .inl (otherEnd u σ.edge)) (d := .inr (.inr σ.face))
    (by simp) (by simpa using Ne.symm hne) (by simp) (by simp) (by simp) (by simp) y
  convert this using 3 <;> simp [Sym2.eq_swap]

theorem hEdge_edg_mem (φ : S.Flag) : S.hEdge (S.edg φ) ∈ S.sideEdges (S.fac φ) := by
  rw [mem_sideEdges]
  refine ⟨φ.vert, φ.vert_mem, ?_⟩
  unfold edg
  cases h : φ.spoke
  · left
    simp only [Bool.false_eq_true, ite_false, hEdge, fac, Dart.edge]
    congr 3
    exact Subtype.ext (otherEnd_spec φ.vert_mem)
  · right
    simp [hEdge, fac]

theorem dart_mem_sideEdges_iff (σ : S.Side) (d : J.Dart) :
    S.hEdge (.inl d) ∈ S.sideEdges σ ↔ σ.edge = d.edge := by
  rw [mem_sideEdges]
  constructor
  · rintro ⟨x, hx, h | h⟩
    · simp only [hEdge, Sym2.eq_iff] at h
      rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
      · simp only [Sum.inr.injEq, Sum.inl.injEq, Subtype.mk.injEq] at h2
        exact h2.symm
      · exact absurd h1 (by simp)
    · simp only [hEdge, Sym2.eq_iff] at h
      rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 (by simp)
      · exact absurd h1 (by simp)
  · intro h
    have hx : d.fst ∈ σ.edge := by rw [h]; exact Sym2.mem_mk_left _ _
    refine ⟨d.fst, hx, Or.inl ?_⟩
    simp only [hEdge]
    congr 3
    exact Subtype.ext h.symm

theorem corner_mem_sideEdges_iff (σ : S.Side) (c : S.Corner) :
    S.hEdge (.inr c) ∈ S.sideEdges σ ↔ σ.face = c.face ∧ c.vert ∈ σ.edge := by
  rw [mem_sideEdges]
  constructor
  · rintro ⟨x, hx, h | h⟩
    · simp only [hEdge, Sym2.eq_iff] at h
      rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 (by simp)
      · exact absurd h1 (by simp)
    · simp only [hEdge, Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
      · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2
        exact ⟨h2.symm, h1 ▸ hx⟩
      · exact absurd h1 (by simp)
  · rintro ⟨h1, h2⟩
    refine ⟨c.vert, h2, Or.inr ?_⟩
    simp only [hEdge, h1]

theorem sideEdges_subset (σ : S.Side) : ∀ ε ∈ S.sideEdges σ, ε ∈ S.radial.edgeSet := by
  intro ε hε
  obtain ⟨x, hx, rfl | rfl⟩ := (S.mem_sideEdges).mp hε
  · exact hx
  · exact ⟨σ.edge, σ.edge_mem, hx⟩

theorem sideEdges_nonempty (σ : S.Side) : (S.sideEdges σ).Nonempty := by
  obtain ⟨u, hu⟩ := exists_mem_sym2 σ.edge
  exact ⟨_, (S.mem_sideEdges).mpr ⟨u, hu, Or.inr rfl⟩⟩

theorem two_sides (ε : Sym2 S.RadV) (hε : ε ∈ S.radial.edgeSet) :
    (Finset.univ.filter (fun σ => ε ∈ S.sideEdges σ)).card = 2 := by
  classical
  obtain ⟨a, rfl⟩ := S.hEdge_surj hε
  rw [← Fintype.card_subtype]
  rcases a with d | c
  · let eqv : {σ : S.Side // S.hEdge (.inl d) ∈ S.sideEdges σ} ≃
        {f : S.Face // d.edge ∈ S.edges f} :=
      { toFun := fun σ => ⟨σ.1.face, by
          rw [← (S.dart_mem_sideEdges_iff σ.1 d).mp σ.2]; exact σ.1.edge_mem⟩
        invFun := fun f => ⟨⟨f.1, d.edge, f.2⟩, (S.dart_mem_sideEdges_iff _ d).mpr rfl⟩
        left_inv := fun σ => by
          have h := (S.dart_mem_sideEdges_iff σ.1 d).mp σ.2
          apply Subtype.ext
          ext <;> simp [h]
        right_inv := fun f => rfl }
    rw [Fintype.card_congr eqv, Fintype.card_subtype]
    exact S.two_faces d.edge (J.mem_edgeSet.mpr d.adj)
  · let eqv : {σ : S.Side // S.hEdge (.inr c) ∈ S.sideEdges σ} ≃
        {e : Sym2 V // e ∈ S.edges c.face ∧ c.vert ∈ e} :=
      { toFun := fun σ => ⟨σ.1.edge, by
          obtain ⟨h1, h2⟩ := (S.corner_mem_sideEdges_iff σ.1 c).mp σ.2
          exact ⟨h1 ▸ σ.1.edge_mem, h2⟩⟩
        invFun := fun e => ⟨⟨c.face, e.1, e.2.1⟩, (S.corner_mem_sideEdges_iff _ c).mpr ⟨rfl, e.2.2⟩⟩
        left_inv := fun σ => by
          obtain ⟨h1, -⟩ := (S.corner_mem_sideEdges_iff σ.1 c).mp σ.2
          apply Subtype.ext
          ext <;> simp [h1]
        right_inv := fun e => rfl }
    rw [Fintype.card_congr eqv, Fintype.card_subtype]
    have h2 : edgeDeg (S.edges c.face) c.vert = 2 := S.edgeDeg_eq_two_of_mem c.vert_mem
    rw [← h2, edgeDeg]
    congr 1
    ext e; simp

theorem radial_connected [Nonempty V] (hJ : ∀ v : V, ∃ w, J.Adj v w) : S.radial.Connected := by
  have h := S.induce_connected_of_cover hJ (T := Set.univ) isVertexCover_univ
  have hW : ∀ x, x ∈ S.withOpt Set.univ := by
    rintro (v | t)
    · exact S.inl_mem_withOpt.mpr trivial
    · exact S.inr_mem_withOpt _ t
  refine ⟨fun x y => ?_⟩
  have := h.preconnected ⟨x, hW x⟩ ⟨y, hW y⟩
  exact this.map (Embedding.induce _).toHom

theorem card_radial_edgeSet [DecidableRel J.Adj] :
    Nat.card S.radial.edgeSet = Fintype.card (J.Dart ⊕ S.Corner) := by
  classical
  rw [← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_eq_of_bijective (fun a => (⟨S.hEdge a, S.hEdge_mem a⟩ : S.radial.edgeSet))
  constructor
  · intro a b h
    exact S.hEdge_injective (congrArg Subtype.val h)
  · rintro ⟨ε, hε⟩
    obtain ⟨a, rfl⟩ := S.hEdge_surj hε
    exact ⟨a, rfl⟩

theorem radial_dual_connected [Nonempty V] (hJ : ∀ v : V, ∃ w, J.Adj v w)
    (hlink : S.LinksConnected) :
    (SimpleGraph.fromRel fun σ τ : S.Side => ∃ ε, ε ∈ S.sideEdges σ ∧ ε ∈ S.sideEdges τ).Connected := by
  classical
  have hfg := S.fg_connected hJ hlink
  obtain ⟨φ₀⟩ := hfg.nonempty
  refine (connected_iff_exists_forall_reachable _).mpr ⟨S.fac φ₀, fun σ => ?_⟩
  obtain ⟨φ, rfl⟩ := S.fac_surj σ
  obtain ⟨p⟩ := hfg.preconnected φ₀ φ
  clear hfg
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hab p ih =>
    refine Reachable.trans ?_ ih
    rcases (S.flagSystem hJ).edge_cases hab with rfl | rfl | rfl
    · change (fromRel _).Reachable (S.fac a) (S.fac (S.t0 a))
      rw [fac_t0]
    · change (fromRel _).Reachable (S.fac a) (S.fac (S.t1 a))
      rw [fac_t1]
    · change (fromRel _).Reachable (S.fac a) (S.fac (S.t2 a))
      apply Adj.reachable
      rw [fromRel_adj]
      refine ⟨(fac_t2 a).symm, Or.inl ⟨S.hEdge (S.edg a), S.hEdge_edg_mem a, ?_⟩⟩
      rw [← edg_t2]
      exact S.hEdge_edg_mem (S.t2 a)

/-- **The radial graph is planar**: its sides form a planar face system. -/
noncomputable def radialFaces [Nonempty V] [DecidableRel J.Adj] (hJ : ∀ v : V, ∃ w, J.Adj v w)
    (hlink : S.LinksConnected) : PlanarFaces S.radial where
  Face := S.Side
  edges := S.sideEdges
  edges_subset := S.sideEdges_subset
  edges_nonempty := S.sideEdges_nonempty
  edgeDeg_eq := S.sideEdges_edgeDeg
  two_faces := S.two_sides
  connected := S.radial_connected hJ
  dual_connected := S.radial_dual_connected hJ hlink
  euler := by
    classical
    have he := S.euler
    have hd : Fintype.card J.Dart = 2 * Nat.card J.edgeSet := by
      rw [dart_card_eq_twice_card_edges, edgeFinset_card, Nat.card_eq_fintype_card]
    have hR : Fintype.card S.RadV = Fintype.card V + Nat.card J.edgeSet + Fintype.card S.Face := by
      rw [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_sum,
        Nat.card_eq_fintype_card (α := V), Nat.card_eq_fintype_card (α := S.Face)]
      ring
    have hE := S.card_radial_edgeSet
    have hDC : Fintype.card (J.Dart ⊕ S.Corner) = Fintype.card J.Dart + Fintype.card S.Corner :=
      Fintype.card_sum
    have hC := S.card_corner
    have hS := S.card_side
    show Fintype.card S.RadV + Fintype.card S.Side = Nat.card S.radial.edgeSet + 2
    rw [hE, hR, hDC, hd, hC, hS]
    lia

end PlanarFaces

end Lemmata.PlanarSteinerXC
