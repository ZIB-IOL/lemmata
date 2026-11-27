module

public import Lemmata.AwayStepFW.Geometry
public import Lemmata.AwayStepFW.Convergence
public import Lemmata.AwayStepFW.FCFW
public import Lemmata.AwayStepFW.FacialDistance
public import Lemmata.AwayStepFW.PyramidalEq
public import Lemmata.AwayStepFW.LowerBound
public import Lemmata.AwayStepFW.PairwiseRate
public import Lemmata.AwayStepFW.DIPFW

@[expose] public section

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

-- DOCS_BEGIN_MAIN
/-- Lemma 2.26: the pyramidal width has the scaling property. -/
theorem scaling_via_pyramidal_width : ScalingViaPyramidalWidth := Proof.scaling_via_pyramidal_width

/-- Lemma 2.27: geometric strong convexity. -/
theorem geometric_strong_convexity : GeometricStrongConvexity := Proof.geometric_strong_convexity

/-- Theorem 2.29: linear convergence of away-step Frank–Wolfe. -/
theorem away_step_convergence : AwayStepConvergence := Proof.away_step_convergence

/-- Theorem 2.34: linear convergence of fully-corrective Frank–Wolfe. -/
theorem fully_corrective_convergence : FullyCorrectiveConvergence :=
  Proof.fully_corrective_convergence

/-- Proposition 2.31, lower bound: the facial distance is a scaling constant. -/
theorem facial_distance_is_scaling : FacialDistanceScaling := fun V =>
  Proof.facialDistance_isScaling V

/-- Proposition 2.31: the pyramidal width equals the facial distance. -/
theorem pyramidal_width_eq_facial_distance : PyramidalWidthEqFacial := fun V =>
  Proof.pyramidalWidth_eq_facialDistance V

/-- Corollary 2.32 (corrected): a lower bound on the pyramidal width from inequalities. -/
theorem pyramidal_width_lower_bound : PyramidalWidthLowerBound := by
  intro E _ _ _ V ι _ a b hprop hfeas hcut
  rw [Proof.pyramidalWidth_eq_facialDistance V]
  exact Proof.lowerBound_le_facialDistance V a b hprop hfeas hcut

/-- Theorem 3.2: linear convergence of pairwise Frank–Wolfe. -/
theorem pairwise_convergence : PairwiseConvergence := Proof.pairwise_convergence

/-- Sparsity scaling (Garber and Meshi, Lemma 2) on simplex-like polytopes. -/
theorem sparsity_scaling : SparsityScaling := Proof.sparsity_scaling

/-- Feasibility of decomposition-invariant pairwise Frank–Wolfe (Garber and Meshi, Lemma 1). -/
theorem dipfw_feasible : DIPFWFeasible := Proof.dipfw_feasible

/-- Theorem 3.8 with the rate of the proof: decomposition-invariant pairwise Frank–Wolfe. -/
theorem dipfw_rate : DIPFWRate := Proof.dipfw_rate
-- DOCS_END_MAIN

end Lemmata.AwayStepFW
