module

public import Lemmata.FWOpenLoop.Uniform
public import Lemmata.FWOpenLoop.DIPFW
public import Lemmata.FWOpenLoop.AFW
public import Lemmata.FWOpenLoop.FaceRate

@[expose] public section

namespace Lemmata.FWOpenLoop

-- DOCS_BEGIN_MAIN
/-- Proposition 3.1: `f(x_t) - f(x⋆) ≤ 8Lδ²/(t + 3)` for the step sizes `4/(t + 4)`. -/
theorem baseline_rate : BaselineRate := Proof.baseline_rate

/-- Lemma 3.2, corrected: the Guélat–Marcotte scaling for directions of the affine hull. -/
theorem guelat_marcotte_scaling : GuelatMarcotteScaling := Proof.guelat_marcotte_scaling

/-- Lemma 3.3: the iterates approach the minimizers. -/
theorem iterates_near_optimum : IteratesNearOptimum := Proof.iterates_near_optimum

/-- Lemma 3.4: scaling from a Hölderian error bound. -/
theorem scaling_heb : ScalingHEB := Proof.scaling_heb

/-- Lemma 3.5: the sequence lemma. -/
theorem sequence_lemma : SequenceLemma := Proof.sequence_lemma

/-- Theorem 3.6: accelerated rates when the minimizers lie in the relative interior. -/
theorem interior_rate : InteriorRate := Proof.interior_rate

/-- Lemma 3.9: scaling for uniformly convex sets. -/
theorem scaling_unif : ScalingUnif := Proof.scaling_unif

/-- Theorem 3.10: accelerated rates for gradients bounded away from zero. -/
theorem exterior_rate : ExteriorRate := Proof.exterior_rate

/-- Theorem 3.12: accelerated rates without assumptions on the location of the minimizer. -/
theorem unrestricted_rate : UnrestrictedRate := Proof.unrestricted_rate
/-- Proposition 5.2: decomposition-invariant pairwise Frank–Wolfe with the step sizes `8/(t + 8)`
rounded down to powers of `1/2` converges at the rate `32Lδ²/(t + 7)`. -/
theorem dipfw_baseline : DIPFWBaseline := Proof.dipfw_baseline

/-- Theorem 5.3: decomposition-invariant pairwise Frank–Wolfe under a Hölderian error bound. -/
theorem dipfw_open_loop_rate : DIPFWOpenLoopRate := Proof.dipfw_open_loop_rate

/-- Lemma 5.5: the drop-step characterization. -/
theorem drop_step : DropStep := Proof.drop_step

/-- Lemma 5.6: at least half of the steps are progress steps. -/
theorem progress_steps : ProgressSteps := Proof.progress_steps

/-- Proposition 5.7: away-step Frank–Wolfe with open-loop step sizes converges at the rate
`16Lδ²/(t + 6)`. -/
theorem olafw_baseline : OLAFWBaseline := Proof.olafw_baseline

/-- Theorem 5.9: away-step Frank–Wolfe with open-loop step sizes under a Hölderian error bound. -/
theorem olafw_rate : OLAFWRate := Proof.olafw_rate
/-- Lemma 4.1: from some iteration on, the atoms lie in the optimal face. -/
theorem active_set_identification : ActiveSetIdentification := Proof.active_set_identification

/-- Lemma 4.2: the scaling inequality relative to the affine hull of the optimal face. -/
theorem scaling_boundary : ScalingBoundary := Proof.scaling_boundary

/-- Lemma 4.3: the distance to the affine hull of the optimal face decays like `(η_t/η_S)⁴`. -/
theorem distance_to_face : DistanceToFace := Proof.distance_to_face

/-- Lemma 4.4: a lower bound on the derivative along the optimal face, from strong convexity. -/
theorem scaling_cvx : ScalingCVX := Proof.scaling_cvx

/-- Theorem 4.5: rate `O(1/t²)` when the minimizer lies in the relative interior of a face. -/
theorem polytope_face_rate : PolytopeFaceRate := Proof.polytope_face_rate
-- DOCS_END_MAIN

end Lemmata.FWOpenLoop
