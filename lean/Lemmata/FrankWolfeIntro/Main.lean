module

public import Lemmata.FrankWolfeIntro.Statement
public import Lemmata.FrankWolfeIntro.Proof
public import Lemmata.FrankWolfeIntro.GapRate
public import Lemmata.FrankWolfeIntro.Adaptive
public import Lemmata.FrankWolfeIntro.Cocoercive
public import Lemmata.FrankWolfeIntro.AdaptiveProgress
public import Lemmata.FrankWolfeIntro.Caratheodory.Theorem

@[expose] public section

/-!
# The Frank–Wolfe algorithm: a short introduction

Each theorem proves the statement of the result named in its docstring, in the numbering of
arXiv:2311.05313. Lemmas 4.1 and 4.3 and Theorem 4.4 are the theorems of the core entry.
-/

namespace Lemmata.FrankWolfeIntro

open Lemmata.FrankWolfe

-- DOCS_BEGIN_MAIN
/-- Lemma 4.1 (primal, dual and Frank–Wolfe gap): the core's `gap_inequalities`. -/
theorem gaps : GapInequalities := FrankWolfe.gap_inequalities

/-- Lemma 4.2 (first-order optimality). -/
theorem first_order_optimality : FirstOrderOptimality := Proof.first_order_optimality

/-- Lemma 4.3 (primal progress from smoothness): the core's `progress_lemma`. -/
theorem primal_progress : ProgressLemma := FrankWolfe.progress_lemma

/-- Theorem 4.4 (primal convergence): the core's `standard_rate`. -/
theorem primal_convergence : StandardRate := FrankWolfe.standard_rate

/-- Theorem 4.5 (Frank–Wolfe gap convergence). -/
theorem gap_rate : GapRate := Proof.gap_rate

/-- Proposition 4.6 (a lower bound for any step sizes). -/
theorem fixed_lower_bound : FixedLowerBound := Proof.fixed_lower_bound

/-- Proposition 4.6 for the open-loop step sizes `2/(t+2)`. -/
theorem fixed_lower_bound_open_loop : FixedLowerBoundOpenLoop := Proof.fixed_lower_bound_open_loop

/-- Theorem 4.7 (convergence for nonconvex objectives). -/
theorem nonconvex_rate : NonconvexRate := Proof.nonconvex_rate

/-- Lemma 4.9 (smoothness revisited). -/
theorem smoothness_revisited : SmoothnessRevisited := Proof.smoothness_revisited

/-- Lemma 4.10 (primal progress from the adaptive test). -/
theorem adaptive_progress : AdaptiveProgress := Proof.adaptive_progress

/-- Lemma 4.11 (smoothness implies the adaptive test). -/
theorem smooth_implies_adaptive_test : SmoothImpliesAdaptiveTest :=
  Proof.smooth_implies_adaptive_test

/-- Theorem 5.1 (approximate Carathéodory). -/
theorem approximate_caratheodory : ApproximateCaratheodory := Proof.approximate_caratheodory
-- DOCS_END_MAIN

end Lemmata.FrankWolfeIntro
