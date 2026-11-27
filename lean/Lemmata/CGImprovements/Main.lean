module

public import Lemmata.CGImprovements.Proof
public import Lemmata.CGImprovements.Lazy
public import Lemmata.CGImprovements.LazyAway

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
-- DOCS_END_MAIN

end Lemmata.CGImprovements
