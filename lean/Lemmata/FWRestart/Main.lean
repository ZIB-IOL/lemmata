module

public import Lemmata.FWRestart.Wolfe

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
-- DOCS_END_MAIN

end Lemmata.FWRestart
