module

public import Lemmata.CGImprovements.Proof
public import Lemmata.CGImprovements.Lazy
public import Lemmata.CGImprovements.LazyAway
public import Lemmata.CGImprovements.Sharp
public import Lemmata.CGImprovements.SharpAFW
public import Lemmata.CGImprovements.SharpSublinear
public import Lemmata.CGImprovements.NEP
public import Lemmata.CGImprovements.BCG
public import Lemmata.CGImprovements.BCGLinear
public import Lemmata.CGImprovements.SimplexDescent

@[expose] public section

namespace Lemmata.CGImprovements

-- DOCS_BEGIN_MAIN
/-- Smoothness passes the sufficient decrease test of Algorithm 3.4. -/
theorem smooth_passes_test : SmoothPassesTest := Proof.smooth_passes_test

/-- Algorithm 3.4 terminates with an estimate at most `max {M₀, τ L}`. -/
theorem adaptive_step_terminates : AdaptiveStepTerminates := Proof.adaptive_step_terminates

/-- Algorithm 3.5 (AdaFW): the rates of vanilla Frank–Wolfe with the largest estimate. -/
theorem adaptive_rate : AdaptiveRate := Proof.adaptive_rate

/-- Theorem 3.15: lazy conditional gradients with a weak separation oracle. -/
theorem lazy_rate : LazyRate := Proof.lazy_rate

/-- Theorem 3.16, with a corrected count: lazy away-step Frank–Wolfe. -/
theorem lazy_away_rate : LazyAwayRate := Proof.lazy_away_rate

/-- Lemma 3.31: the primal gap bound from sharpness. -/
theorem sharp_primal_gap : SharpPrimalGap := Proof.sharp_primal_gap

/-- Lemma 3.32: geometric sharpness. -/
theorem geometric_sharpness : GeometricSharpness := Proof.geometric_sharpness

/-- Corollary 3.33 for `θ = 1/2`: linear convergence of away-step Frank–Wolfe under sharpness. -/
theorem sharp_away_linear : SharpAwayLinear := Proof.sharp_away_linear

/-- Theorem 3.36: Frank–Wolfe with the nearest extreme point oracle. -/
theorem nep_rate : NEPRate := Proof.nep_rate

/-- Theorem 3.42, convex case with explicit constants: blended conditional gradients. -/
theorem bcg_rate : BCGRate := Proof.bcg_rate

/-- Theorem 3.42, strongly convex case with explicit constants: blended conditional gradients. -/
theorem bcg_linear_rate : BCGLinearRate := Proof.bcg_linear_rate

/-- Lemma 3.45: the simplex descent step. -/
theorem simplex_descent : SimplexDescent := Proof.simplex_descent

/-- Corollary 3.33 for `θ < 1/2`: away-step Frank–Wolfe under sharpness. -/
theorem sharp_away_sublinear : SharpAwaySublinear := Proof.sharp_away_sublinear

/-- Lemma 3.35, first half: sharp functions are gradient dominated. -/
theorem sharp_gradient_dominated : SharpGradientDominated := Proof.sharp_gradient_dominated
-- DOCS_END_MAIN

end Lemmata.CGImprovements
