module

public import Lemmata.CGBasics.Smoothness
public import Lemmata.CGBasics.Interior
public import Lemmata.CGBasics.Rates
public import Lemmata.CGBasics.Approx
public import Lemmata.CGBasics.FixedStep
public import Lemmata.CGBasics.UniformlyConvex
public import Lemmata.CGBasics.LowerBound
public import Lemmata.FrankWolfeIntro.Main

@[expose] public section

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

-- DOCS_BEGIN_MAIN
/-- Lemma 1.7: for convex functions, smoothness is equivalent to Lipschitz gradients. -/
theorem smooth_iff_lipschitz : SmoothIffLipschitz := Proof.smooth_iff_lipschitz

/-- Proposition 1.12: the Frank–Wolfe gap is bounded by the primal gap. -/
theorem gap_by_primal_gap : GapByPrimalGap := Proof.gap_by_primal_gap

/-- Theorem 2.6: Frank–Wolfe with an approximate linear minimization oracle. -/
theorem approximate_oracle_rate : ApproximateOracleRate := Proof.approximate_oracle_rate

/-- Lemma 2.13: the primal gap bound via strong convexity. -/
theorem primal_gap_strong_convexity : PrimalGapStrongConvexity :=
  Proof.primal_gap_strong_convexity

/-- Proposition 2.16: the scaling condition for an interior minimizer. -/
theorem scaling_interior : ScalingInterior := Proof.scaling_interior

/-- Theorem 2.17: linear convergence for an interior minimizer. -/
theorem linear_rate_interior : LinearRateInterior := Proof.linear_rate_interior

/-- Lemma 2.21: contractions of mixed type. -/
theorem contraction_mixed : ContractionMixed := Proof.contraction_mixed

/-- Lemma 2.22: linear contraction. -/
theorem contraction_linear : ContractionLinear := Proof.contraction_linear

/-- Lemma 2.23: power contraction. -/
theorem contraction_power : ContractionPower := Proof.contraction_power

/-- Theorem 2.2: primal and Frank–Wolfe gap rates of vanilla Frank–Wolfe. -/
theorem vanilla_rate : VanillaRate := Proof.vanilla_rate

/-- Proposition 2.9: the value bound for any step sizes. -/
theorem fixed_step_lower_bound : FixedStepLowerBound := Lemmata.FrankWolfeIntro.fixed_lower_bound

/-- Proposition 2.9: the value bound for the open-loop rule. -/
theorem fixed_step_lower_bound_open_loop : FixedStepLowerBoundOpenLoop :=
  Lemmata.FrankWolfeIntro.fixed_lower_bound_open_loop

/-- Proposition 2.9: iterates as combinations of the first iterate. -/
theorem fixed_step_decomposition : FixedStepDecomposition := Proof.fixed_step_decomposition

/-- Theorem 2.11: Frank–Wolfe gap rate for nonconvex objectives. -/
theorem nonconvex_short_step_rate : NonconvexShortStepRate := Proof.nonconvex_short_step_rate

/-- Proposition 2.19: the scaling inequality for uniformly convex sets. -/
theorem uniformly_convex_scaling : UniformlyConvexScaling := Proof.uniformly_convex_scaling

/-- Theorem 2.20 for `q = 2`: linear rate over strongly convex sets. -/
theorem uniformly_convex_linear : UniformlyConvexLinear := Proof.uniformly_convex_linear

/-- Theorem 2.20 for `q > 2`: rates over uniformly convex sets. -/
theorem uniformly_convex_power : UniformlyConvexPower := Proof.uniformly_convex_power

/-- Theorem 2.24: rates for gradient-dominated objectives over uniformly convex sets. -/
theorem gradient_dominated_rate : GradientDominatedRate := Proof.gradient_dominated_rate

/-- Example 2.7: a primal gap lower bound from the number of vertices seen. -/
theorem simplex_lower_bound : SimplexLowerBound := Proof.simplex_lower_bound
-- DOCS_END_MAIN

end Lemmata.CGBasics
