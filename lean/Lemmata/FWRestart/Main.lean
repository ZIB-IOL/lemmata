module

public import Lemmata.FWRestart.Holder

@[expose] public section

namespace Lemmata.FWRestart

-- DOCS_BEGIN_MAIN
/-- Lemma 2.3: the strong Wolfe gap bounds the primal gap and vanishes exactly at the minimizers. -/
theorem strong_wolfe_gap : StrongWolfeGap := Proof.strong_wolfe_gap

/-- Lemma 3.6: a Hölderian error bound and the scaling property give the `1/(1-θ)`-strong Wolfe
primal bound. -/
theorem heb_strong_wolfe_bound : HEBStrongWolfeBound := Proof.heb_strong_wolfe_bound

/-- Theorem 7.3: vanilla Frank–Wolfe over strongly convex sets converges at the rate
`O(t^{-1/(1-θ)})` under a `(θ, c)`-Hölderian error bound. -/
theorem strongly_convex_set_rate : StronglyConvexSetRate := Proof.strongly_convex_set_rate

/-- Proposition 4.1: the number of iterations of fractional away-step Frank–Wolfe. -/
theorem fractional_complexity : FractionalComplexity := Proof.fractional_complexity

/-- Proposition 4.2: the burn-in phase of scheduled restarts. -/
theorem burn_in : BurnIn := Proof.burn_in

/-- Theorem 5.1: the rate of scheduled restarts of fractional away-step Frank–Wolfe under a
Hölderian error bound. -/
theorem restart_rate : RestartRate := Proof.restart_rate

/-- Proposition 5.3: for `r = 1` and `r = 2`, the schedule parameter `γ = 1/2` is optimal up to the
factor `e/(4(√e - 1)) ≈ 1.05`. -/
theorem robust_gamma : RobustGamma := Proof.robust_gamma

/-- Proposition 6.1: the number of iterations of fractional away-step Frank–Wolfe under Hölder
smoothness. -/
theorem holder_complexity : HolderComplexity := Proof.holder_complexity

/-- Theorem 6.2: the rate of scheduled restarts under Hölder smoothness. -/
theorem holder_restart_rate : HolderRestartRate := Proof.holder_restart_rate

/-- Proposition 6.3: the burn-in phase under Hölder smoothness. -/
theorem holder_burn_in : HolderBurnIn := Proof.holder_burn_in
-- DOCS_END_MAIN

end Lemmata.FWRestart
