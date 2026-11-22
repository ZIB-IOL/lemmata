module

public import Lemmata.PlanarSteinerXC.Statement
public import Lemmata.PlanarSteinerXC.GridPlanar
public import Lemmata.PlanarSteinerXC.RadialFaces
public import Lemmata.PlanarSteinerXC.HamiltonEncode
public import Lemmata.PlanarSteinerXC.FlagFaces

/-!
# Assembly at the grid

We instantiate the general results at the planar cover graph `Jg` of the grid formula: the cover
graph lemma for the grid, the face system and its link condition, and the vertex counts of the
radial graph `H` and of the flag graph.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

namespace Grid

open SimpleGraph

variable {h : ℕ} (hh : 2 ≤ h)

include hh in
theorem nonempty_JV : Nonempty (JV h) := ⟨(occP hh (p0 hh), 0)⟩

/-- The links of the face system of `Jg` are connected (maximum degree three). -/
theorem gridLinks : (gridFaces hh).LinksConnected :=
  (gridFaces hh).linksConnected_of_degree_le_three (degree_le_three hh)

/-- **The cover graph lemma for the grid.** The correlation polytope of the grid is a projection
of the minimum-cover face of the planar cover graph `Jg`. -/
theorem xc_COR_grid_le : xc (COR (grid h)) ≤ xc (minCoverFace (Jg hh)) :=
  xc_COR_le_minCoverFace (nextPerm hh) (var_nextPerm hh) (nextPerm_cyclic hh) (occP hh)
    (var_occP hh) (grid h) oeEquiv oeEquiv_apply

theorem gridFaces_face : (gridFaces hh).Face = Face h := rfl

/-- The flag graph of `Jg` has `16 |E(Jg)| = 832 h (h - 1)` vertices. -/
theorem card_flag_grid : Fintype.card (gridFaces hh).Flag = 832 * h * (h - 1) := by
  rw [PlanarFaces.card_flag, PlanarFaces.card_side, card_edges, card_oe]
  ring

/-- The radial graph of `Jg` has `|V| + |E| + |F| = 104 h (h - 1) + 2` vertices. -/
theorem card_radV_grid : Fintype.card (gridFaces hh).RadV = 104 * h * (h - 1) + 2 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_sum, gridFaces_face,
    Nat.card_eq_fintype_card (α := JV h), Nat.card_eq_fintype_card (α := Face h), card_JV,
    card_edges, card_face, card_oe]
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by lia⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- **The cover graph of the grid is planar.** It has a planar face system, is connected, has
maximum degree three and no isolated vertices, and has `42 h (h - 1)` vertices, `52 h (h - 1)`
edges and `h² + 8 h (h - 1) + (h - 1)² + 1` faces. -/
theorem grid_cover_planar :
    IsPlanar (Jg hh) ∧ (Jg hh).Connected ∧ (∀ w, (Jg hh).degree w ≤ 3) ∧
      (∀ w, ∃ w', (Jg hh).Adj w w') ∧ Fintype.card (JV h) = 42 * h * (h - 1) ∧
      Nat.card (Jg hh).edgeSet = 52 * h * (h - 1) ∧
      Nat.card (gridFaces hh).Face = h * h + 8 * h * (h - 1) + (h - 1) * (h - 1) + 1 := by
  refine ⟨⟨gridFaces hh⟩, Jg_connected hh, degree_le_three hh, no_isolated hh, ?_, ?_, ?_⟩
  · rw [card_JV, card_oe]; ring
  · rw [card_edges, card_oe]; ring
  · show Nat.card (Face h) = _
    rw [Nat.card_eq_fintype_card, card_face, card_oe]; ring

end Grid

namespace PlanarFaces

variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V}

/-- **The radial graph is planar.** If `J` has a planar face system with connected links and no
isolated vertices, then its radial graph `H` is planar (its faces are the quadrilaterals
`u q_e v f`, one for each side of an edge `e = uv` on a face `f`). -/
theorem radial_isPlanar (S : PlanarFaces J) [Nonempty V] [DecidableRel J.Adj]
    (hJ : ∀ v : V, ∃ w, J.Adj v w) (hlink : S.LinksConnected) : IsPlanar S.radial :=
  ⟨S.radialFaces hJ hlink⟩

end PlanarFaces

namespace FlagSystem

/-- **The flag graph is planar.** If the flag graph of a flag system is connected and Euler's
relation `2 (|Q₀| + |Q₁| + |Q₂|) = |Φ| + 4` holds, then it is planar, with the stars of the
elements of `Q₀ ⊕ Q₁ ⊕ Q₂` as faces. -/
theorem isPlanar.{u} {Φ Q0 Q1 Q2 : Type u} (F : FlagSystem Φ Q0 Q1 Q2) [DecidableEq Q0]
    [DecidableEq Q1] [DecidableEq Q2] [Fintype Φ] [DecidableEq Φ] [Fintype Q0] [Fintype Q1]
    [Fintype Q2] (hconn : F.graph.Connected)
    (heuler : 2 * (Fintype.card Q0 + Fintype.card Q1 + Fintype.card Q2) = Fintype.card Φ + 4) :
    IsPlanar F.graph :=
  ⟨F.planarFaces hconn heuler⟩

end FlagSystem

end Lemmata.PlanarSteinerXC
