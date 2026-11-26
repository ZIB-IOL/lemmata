module

public import Lemmata.FrankWolfeBSS.Proof

@[expose] public section

namespace Lemmata.FrankWolfeBSS

open Lemmata.FrankWolfe

-- DOCS_BEGIN_MAIN
/-- The primal-dual gap bounds the primal gap. -/
theorem gap_bounds_primal : GapBoundsPrimal := Proof.gap_bounds_primal

/-- Proposition 4.1: the primal-dual gap recursion. -/
theorem gap_recursion : GapRecursion := Proof.gap_recursion

/-- Proposition 4.1: the bound is convex in the step size. -/
theorem gap_bound_convex : GapBoundConvex := Proof.gap_bound_convex

/-- Proposition 4.1: the rate `2 L D²/(t + 2)` for open-loop steps, primal-dual short steps and line
search on the primal-dual gap, mixed freely. -/
theorem primal_dual_rate : PrimalDualRate := Proof.primal_dual_rate

/-- Proposition 4.1: the rate for the explicit primal-dual short step. -/
theorem primal_dual_short_step_rate : PrimalDualShortStepRate := Proof.primal_dual_short_step_rate
/-- Heavy-ball Frank–Wolfe: the primal-dual gap bounds the primal gap. -/
theorem heavy_ball_gap_bounds_primal : HeavyBallGapBoundsPrimal := Proof.hb_gap_bounds_primal

/-- Proposition 4.1 for heavy-ball Frank–Wolfe: the gap recursion. -/
theorem heavy_ball_gap_recursion : HeavyBallGapRecursion := Proof.hb_gap_recursion

/-- Proposition 4.1 for heavy-ball Frank–Wolfe: the rate. -/
theorem heavy_ball_rate : HeavyBallRate := Proof.hb_rate
-- DOCS_END_MAIN

end Lemmata.FrankWolfeBSS
