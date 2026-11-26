module

public import Lemmata.AwayStepFW.Geometry
public import Lemmata.AwayStepFW.Convergence
public import Lemmata.AwayStepFW.FCFW
public import Lemmata.AwayStepFW.FacialDistance
public import Lemmata.AwayStepFW.PyramidalEq

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
-- DOCS_END_MAIN

end Lemmata.AwayStepFW
