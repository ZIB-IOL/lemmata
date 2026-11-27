module

public import Lemmata.FWOpenLoop.Uniform

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
-- DOCS_END_MAIN

end Lemmata.FWOpenLoop
