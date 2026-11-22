module

public import Lemmata.PlanarSteinerXC.Assembly
public import Lemmata.PlanarSteinerXC.Pendant

/-!
# Exact LP extension complexity of planar Steiner tree polytopes: the lower bound

The statements are in `Statement.lean`. The reduction chain is

`COR(grid h)` → (Lemma 3) minimum vertex covers of the planar cover graph `J` → (Theorem 6)
Hamiltonian paths of the planar flag graph minus an edge `st` → (Feldmann–Rai, Lemma 9)
`P_min(Γ - st, {s, t})`,

and, for the four polyhedra with many terminals, (Proposition 5) the radial graph `H` of `J`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph Grid

theorem sqrt_le_mul {n a h : ℕ} (hn : n ≤ a * a * (h * h)) :
    Real.sqrt (n : ℝ) ≤ a * h := by
  rw [show ((a : ℝ) * h) = Real.sqrt (((a : ℝ) * h) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have : (n : ℝ) ≤ ((a * a * (h * h) : ℕ) : ℝ) := by exact_mod_cast hn
  exact this.trans (le_of_eq (by push_cast; ring))

theorem rpow_le_of_sqrt {c : ℝ} (hc : 0 < c) {n a h : ℕ} (ha : 0 < a)
    (hn : n ≤ a * a * (h * h)) :
    (2 : ℝ) ^ (c / a * Real.sqrt (n : ℝ)) ≤ 2 ^ (c * h) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h1 := sqrt_le_mul hn
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  calc c / a * Real.sqrt (n : ℝ) ≤ c / a * (a * h) := by gcongr
    _ = c * h := by field_simp

-- DOCS_BEGIN_MAIN
/-- **Two cofacial terminals.** The correlation polytope of the `h × h` grid is, up to faces and
projections, the Steiner tree polytope `P_min(Γ - st, {s, t})` of a planar graph `Γ` on
`832 h (h - 1)` vertices with an edge `st`. -/
theorem twoTerminalReduction : TwoTerminalReduction := by
  intro h hh
  have := nonempty_JV hh
  have hJ := no_isolated hh
  have : DecidableEq (gridFaces hh).RadV := Classical.decEq _
  refine ⟨(gridFaces hh).Flag, inferInstance, inferInstance, (gridFaces hh).fg hJ,
    (gridFaces hh).sF hJ, (gridFaces hh).tF hJ,
    ⟨((gridFaces hh).flagSystem hJ).planarFaces ((gridFaces hh).fg_connected hJ (gridLinks hh))
      (gridFaces hh).flag_euler⟩,
    (gridFaces hh).sF_tF_adj hJ, card_flag_grid hh, ?_⟩
  exact (xc_COR_grid_le hh).trans ((xc_minCoverFace_le_VC _).trans
    ((gridFaces hh).xc_VC_le_Pmin hJ (gridLinks hh)))

/-- **Four polyhedra.** The correlation polytope of the `h × h` grid is, up to faces and
projections, each of `P_min(H, R)`, `P_conn(H, R)`, `P_up(H, R)` and the dominant of a planar
graph `H` on `104 h (h - 1) + 2` vertices. -/
theorem steinerReduction : SteinerReduction := by
  intro h hh
  have := nonempty_JV hh
  have hJ := no_isolated hh
  obtain ⟨h1, h2, h3, h4⟩ := (gridFaces hh).xc_minCoverFace_le_steiner hJ
  have h0 := xc_COR_grid_le hh
  exact ⟨(gridFaces hh).RadV, _, _, (gridFaces hh).radial,
    (gridFaces hh).terms, ⟨(gridFaces hh).radialFaces hJ (gridLinks hh)⟩, card_radV_grid hh,
    h0.trans h1, h0.trans h2, h0.trans h3, h0.trans h4⟩

/-- **Lower bound, two cofacial terminals:** `xc(P_min(Γ - st, {s, t})) ≥ 2^{(c/29) √n}`,
given the bound `2^{c h}` for correlation polytopes of grids. -/
theorem twoTerminalLowerBound : TwoTerminalLowerBound := by
  intro c hc hbound h hh
  obtain ⟨Φ, i1, i2, Γ, s, t, hpl, hadj, hcard, hxc⟩ := twoTerminalReduction h hh
  refine ⟨Φ, i1, i2, Γ, s, t, hpl, hadj, hcard, fun k hk => ?_⟩
  refine lt_of_lt_of_le (hbound h hh k (lt_of_lt_of_le hk ?_)) hxc
  rw [hcard]
  exact_mod_cast rpow_le_of_sqrt hc (a := 29) (by norm_num)
    (by have : h - 1 ≤ h := Nat.sub_le h 1; nlinarith)

/-- **Lower bound, four polyhedra:** each has extension complexity at least `2^{(c/11) √n}`,
given the bound `2^{c h}` for correlation polytopes of grids. -/
theorem steinerLowerBound : SteinerLowerBound := by
  intro c hc hbound h hh
  obtain ⟨W, i1, i2, H, R, hpl, hcard, h1, h2, h3, h4⟩ := steinerReduction h hh
  refine ⟨W, i1, i2, H, R, hpl, hcard, fun k hk => ?_⟩
  have hk' : (k : ℕ∞) < xc (COR (grid h)) := by
    refine hbound h hh k (lt_of_lt_of_le hk ?_)
    rw [hcard]
    exact_mod_cast rpow_le_of_sqrt hc (a := 11) (by norm_num)
      (by have : h - 1 ≤ h := Nat.sub_le h 1; nlinarith)
  exact ⟨hk'.trans_le h1, hk'.trans_le h2, hk'.trans_le h3, hk'.trans_le h4⟩
-- DOCS_END_MAIN

end Lemmata.PlanarSteinerXC
