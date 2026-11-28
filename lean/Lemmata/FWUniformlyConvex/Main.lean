module

public import Lemmata.FWUniformlyConvex.Local
public import Lemmata.FWUniformlyConvex.Heb
public import Lemmata.FWUniformlyConvex.Online

@[expose] public section

namespace Lemmata.FWUniformlyConvex

-- DOCS_BEGIN_MAIN
/-- Lemma 2.4: local uniform convexity at the minimizer gives the local scaling inequality. -/
theorem local_scaling_of_locally_uc : LocalScalingOfLocallyUC :=
  Proof.local_scaling_of_locally_uc

/-- Corollary 2.8: a uniformly convex superset whose normal cone at the minimizer contains
`-∇f(x⋆)` gives the local scaling inequality. -/
theorem local_scaling_of_superset : LocalScalingOfSuperset := Proof.local_scaling_of_superset

/-- Lemma 2.9: the scaling inequality of uniformly convex sets under a Hölderian error bound. -/
theorem heb_scaling : HEBScaling := Proof.heb_scaling

/-- Theorem 2.10: the rate `O(t^{-1/(1-2θ/q)})` of Frank–Wolfe with short steps over uniformly
convex sets under a Hölderian error bound. -/
theorem heb_rate : HEBRate := Proof.heb_rate
/-- Lemma 3.2: linear maximizers over uniformly convex sets depend Hölder-continuously on the
functional. -/
theorem maximizer_stability : MaximizerStability := Proof.maximizer_stability

/-- Theorem 3.1: the regret of follow the leader for online linear optimization over uniformly
convex sets. -/
theorem ftl_regret : FTLRegret := Proof.ftl_regret
-- DOCS_END_MAIN

end Lemmata.FWUniformlyConvex
