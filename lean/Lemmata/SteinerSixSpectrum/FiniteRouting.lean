module

public import Lemmata.SteinerSixSpectrum.Reduction
public meta import Lemmata.SteinerSixSpectrum.Reduction
import Mathlib.Tactic.Eval
import Lean.Elab.Deriving.ToExpr

public section

namespace Lemmata.SteinerSixSpectrum

namespace Routing

/-- A proposed induction step below the analytic cutoff. A terminal case
is handled by an explicit finite design. -/
inductive Hint where
  | terminal
  | weight (wide : Bool) (t r e : Nat)
  | product (d m e : Nat)
  deriving Lean.ToExpr

def orders : List Nat :=
  (List.range 582).flatMap fun q => [15*q+1, 15*q+6]

def propose (n : Nat) : Hint := Id.run do
  if !decide (constructible n) then return .terminal
  let w := findWeighting n
  if stepValid n w then return .weight w.wide w.t w.r w.e
  let p := findProduct n
  if productValid n p then return .product p.d p.m p.e
  return .terminal

private def routes : List (Nat × Hint) := eval% orders.map (fun n => (n, propose n))

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem enumerates : routes.map Prod.fst = orders := by decide +kernel

private def routeOK (seeds : List Nat) (n : Nat) : Hint → Bool
  | .terminal => !decide (constructible n) || seeds.contains n
  | .weight wide t r e => decide (stepValid n ⟨wide,t,r,e⟩)
  | .product d m e => decide (productValid n ⟨d,m,e⟩)

/-- The orders at which the induction calls for an explicit incidence matrix. -/
@[expose] def terminalOrders : List Nat := eval% orders.filter
  (fun n => decide (constructible n) && match propose n with | .terminal => true | _ => false)

private theorem routes_checked : routes.all (fun q => routeOK terminalOrders q.1 q.2) = true := by
  decide +kernel

theorem finiteRoute {n : Nat} (hn : n < 8726) (hc : constructible n) :
    (∃ p, stepValid n p) ∨ (∃ p, productValid n p) ∨ n ∈ terminalOrders := by
  have member : n ∈ orders := by
    apply List.mem_flatMap.mpr
    refine ⟨n/15, List.mem_range.mpr (by omega), ?_⟩
    have := hc.1
    unfold admissible at this
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rw [← enumerates] at member
  obtain ⟨⟨m,hint⟩, hm, rfl⟩ := List.mem_map.mp member
  have ok := List.all_eq_true.mp routes_checked _ hm
  cases hint with
  | terminal =>
    exact Or.inr (Or.inr (by simpa [routeOK, hc] using ok))
  | weight wide t r e => exact Or.inl ⟨_, of_decide_eq_true ok⟩
  | product d m e => exact Or.inr (Or.inl ⟨_, of_decide_eq_true ok⟩)

end Routing

end Lemmata.SteinerSixSpectrum
