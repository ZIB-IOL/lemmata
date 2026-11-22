module

public import Lemmata.PlanarSteinerXC.Objects
public import Lemmata.PlanarSteinerXC.Polyhedral
public import Lemmata.PlanarSteinerXC.FaceSystem
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt

/-!
# Statements

The main claims of the entry, stated as propositions about the objects of `Objects.lean`
(`COR`, `grid`, `Pmin`, `Pconn`, `Pup`, `Dom`), linear extension complexity `xc`
(`Polyhedral.lean`) and planarity `IsPlanar` (`FaceSystem.lean`: a face system whose faces are
cycles, every edge on two faces, connected primal and dual, and Euler's formula). The proofs are
in `Main.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

open SimpleGraph

/-- **Two cofacial terminals.** For every `h ≥ 2` there are a planar graph `Γ` on
`832 h (h - 1)` vertices and an edge `st` of `Γ` such that the correlation polytope of the
`h × h` grid has extension complexity at most that of the Steiner tree polytope
`P_min(Γ - st, {s, t})`. The terminals `s, t` are cofacial in `Γ - st`. -/
def TwoTerminalReduction : Prop :=
  ∀ h : ℕ, 2 ≤ h →
    ∃ (Φ : Type) (_ : Fintype Φ) (_ : DecidableEq Φ) (Γ : SimpleGraph Φ) (s t : Φ),
      IsPlanar Γ ∧ Γ.Adj s t ∧ Fintype.card Φ = 832 * h * (h - 1) ∧
      xc (COR (grid h)) ≤ xc (Pmin (Γ.deleteEdges {s(s, t)}) {s, t})

/-- **Four terminal-connectivity polyhedra.** For every `h ≥ 2` there are a planar graph `H` on
`104 h (h - 1) + 2` vertices and a terminal set `R` such that the correlation polytope of the
`h × h` grid has extension complexity at most that of each of `P_min(H, R)`, `P_conn(H, R)`,
`P_up(H, R)` and the dominant `P_min(H, R) + ℝ^E_{≥0}`. -/
def SteinerReduction : Prop :=
  ∀ h : ℕ, 2 ≤ h →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W) (R : Set W),
      IsPlanar H ∧ Fintype.card W = 104 * h * (h - 1) + 2 ∧
      xc (COR (grid h)) ≤ xc (Pmin H R) ∧ xc (COR (grid h)) ≤ xc (Pconn H R) ∧
      xc (COR (grid h)) ≤ xc (Pup H R) ∧ xc (COR (grid h)) ≤ xc (Dom H R)

/-- The exponential lower bound for correlation polytopes of grids, with constant `c`: every
LP extension of `COR(grid h)` has at least `2^{c h}` inequalities. This is the external input
(Aboulker, Fiorini, Huynh, Macchia and Seif); it is a hypothesis of the lower bounds below. -/
def GridCorrelationBound (c : ℝ) : Prop :=
  ∀ h : ℕ, 2 ≤ h → ∀ k : ℕ, (k : ℝ) < 2 ^ (c * h) → (k : ℕ∞) < xc (COR (grid h))

/-- **The lower bound, two cofacial terminals.** If the correlation polytopes of grids satisfy
the bound with constant `c > 0`, then for every `h ≥ 2` there are a planar graph on
`n = 832 h (h - 1)` vertices and an edge `st` with
`xc(P_min(Γ - st, {s, t})) ≥ 2^{(c/29) √n}`. -/
def TwoTerminalLowerBound : Prop :=
  ∀ c : ℝ, 0 < c → GridCorrelationBound c → ∀ h : ℕ, 2 ≤ h →
    ∃ (Φ : Type) (_ : Fintype Φ) (_ : DecidableEq Φ) (Γ : SimpleGraph Φ) (s t : Φ),
      IsPlanar Γ ∧ Γ.Adj s t ∧ Fintype.card Φ = 832 * h * (h - 1) ∧
      ∀ k : ℕ, (k : ℝ) < 2 ^ (c / 29 * Real.sqrt (Fintype.card Φ)) →
        (k : ℕ∞) < xc (Pmin (Γ.deleteEdges {s(s, t)}) {s, t})

/-- **The lower bound, four polyhedra.** Under the same hypothesis, for every `h ≥ 2` there are
a planar graph on `n = 104 h (h - 1) + 2` vertices and a terminal set `R` such that each of
`P_min`, `P_conn`, `P_up` and the dominant has extension complexity at least `2^{(c/11) √n}`. -/
def SteinerLowerBound : Prop :=
  ∀ c : ℝ, 0 < c → GridCorrelationBound c → ∀ h : ℕ, 2 ≤ h →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W) (R : Set W),
      IsPlanar H ∧ Fintype.card W = 104 * h * (h - 1) + 2 ∧
      ∀ k : ℕ, (k : ℝ) < 2 ^ (c / 11 * Real.sqrt (Fintype.card W)) →
        (k : ℕ∞) < xc (Pmin H R) ∧ (k : ℕ∞) < xc (Pconn H R) ∧
        (k : ℕ∞) < xc (Pup H R) ∧ (k : ℕ∞) < xc (Dom H R)

end Lemmata.PlanarSteinerXC
