module

public import Lemmata.FWUniformlyConvex.Local
public import Lemmata.FWUniformlyConvex.Heb
public import Lemmata.FWUniformlyConvex.Online
public import Lemmata.FWUniformlyConvex.LocalRate
public import Lemmata.FWUniformlyConvex.Examples

@[expose] public section

namespace Lemmata.FWUniformlyConvex

-- DOCS_BEGIN_MAIN
/-- Lemma 2.4: local uniform convexity at the minimizer gives the local scaling inequality. -/
theorem local_scaling_of_locally_uc : LocalScalingOfLocallyUC :=
  Proof.local_scaling_of_locally_uc

/-- Corollary 2.8: a uniformly convex superset whose normal cone at the minimizer contains
`-∇f(x⋆)` gives the local scaling inequality. -/
theorem local_scaling_of_superset : LocalScalingOfSuperset := Proof.local_scaling_of_superset

/-- Lemma 2.7: under the local scaling inequality, the distance to the Frank–Wolfe vertex is
bounded by a power of the primal gap. -/
theorem fw_vertex_distance : FWVertexDistance := Proof.fw_vertex_distance

/-- Theorem 2.5, corrected: rates of Frank–Wolfe with short steps under the local scaling
inequality, after the primal gap has dropped below `1`. -/
theorem local_scaling_rate : LocalScalingRate := Proof.local_scaling_rate

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
/-- Lemma 4.2: unit balls of uniformly convex spaces are uniformly convex sets, and uniform
convexity of balls scales with the radius. -/
theorem uniformly_convex_ball : UniformlyConvexBall := Proof.uniformly_convex_ball

/-- No `L`-smooth function is `(μ, r)`-uniformly convex with `r > 2` on a nontrivial space. -/
theorem smooth_uniformly_convex_exponent : SmoothUniformlyConvexExponent :=
  Proof.smooth_uniformly_convex_exponent

/-- Lemma D.2, corrected: sublevel sets of nonnegative smooth uniformly convex functions are
uniformly convex. -/
theorem sublevel_uniformly_convex : SublevelUniformlyConvex := Proof.sublevel_uniformly_convex

/-- Lemma D.3, corrected: balls of a norm whose square is uniformly convex are uniformly convex. -/
theorem norm_ball_uniformly_convex : NormBallUniformlyConvex := Proof.norm_ball_uniformly_convex

/-- The Euclidean unit disk is not `(1, 2)`-uniformly convex, so the constants of Lemmas D.2 and D.3
as printed are too large. -/
theorem euclidean_disk_not_uc : EuclideanDiskNotUC := Proof.euclidean_disk_not_uc
-- DOCS_END_MAIN

end Lemmata.FWUniformlyConvex
