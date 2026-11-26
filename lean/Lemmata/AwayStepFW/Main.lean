module

public import Lemmata.AwayStepFW.Geometry
public import Lemmata.AwayStepFW.Convergence
public import Lemmata.AwayStepFW.FCFW

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
-- DOCS_END_MAIN

end Lemmata.AwayStepFW
