module

public import Lemmata.CGBasics.Smoothness
public import Lemmata.CGBasics.Interior
public import Lemmata.CGBasics.Rates

@[expose] public section

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

-- DOCS_BEGIN_MAIN
/-- Lemma 1.7: for convex functions, smoothness is equivalent to Lipschitz gradients. -/
theorem smooth_iff_lipschitz : SmoothIffLipschitz := Proof.smooth_iff_lipschitz

/-- Proposition 1.12: the Frank–Wolfe gap is bounded by the primal gap. -/
theorem gap_by_primal_gap : GapByPrimalGap := Proof.gap_by_primal_gap

/-- Lemma 2.13: the primal gap bound via strong convexity. -/
theorem primal_gap_strong_convexity : PrimalGapStrongConvexity :=
  Proof.primal_gap_strong_convexity

/-- Proposition 2.16: the scaling condition for an interior minimizer. -/
theorem scaling_interior : ScalingInterior := Proof.scaling_interior

/-- Theorem 2.17: linear convergence for an interior minimizer. -/
theorem linear_rate_interior : LinearRateInterior := Proof.linear_rate_interior

/-- Lemma 2.22: linear contraction. -/
theorem contraction_linear : ContractionLinear := Proof.contraction_linear

/-- Lemma 2.23: power contraction. -/
theorem contraction_power : ContractionPower := Proof.contraction_power
-- DOCS_END_MAIN

end Lemmata.CGBasics
