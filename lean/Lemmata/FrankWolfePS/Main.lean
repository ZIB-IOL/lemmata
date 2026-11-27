module

public import Lemmata.FrankWolfePS.Proofs

@[expose] public section

namespace Lemmata.FrankWolfePS

-- DOCS_BEGIN_MAIN
/-- No tie-breaking: a body with unique linear minimizers, prescribed smoothness and diameter
at most `D` defeats every measurable method requiring no more than `T` oracle calls. -/
theorem lower_bound_unique_lmo : LowerBoundUniqueLMO := lower_bound_unique_lmo_proof

/-- Feasible methods without tie-breaking: probability `3/4`, and the expected gap. -/
theorem lower_bound_unique_feasible : LowerBoundUniqueFeasible :=
  lower_bound_unique_feasible_proof

/-- With a vertex tie rule: exact diameter `D`, probability `1/4`. -/
theorem lower_bound_vertex_rule : LowerBoundVertexRule := lower_bound_vertex_rule_proof

/-- The posterior identity: the expected final ratio `h/n` is `(d - 1)/(N - 1)`. -/
theorem posterior_ratio_identity : PosteriorIdentity := posterior_identity_proof

/-- Feasible methods: probability `3/4`, and the expected gap. -/
theorem lower_bound_feasible : LowerBoundFeasible := lower_bound_feasible_proof

/-- A distance penalty: arbitrary outputs, penalized error in probability and in mean. -/
theorem lower_bound_penalized : LowerBoundPenalized := lower_bound_penalized_proof

/-- Deterministic methods: dimension `64 (T + 1) + 1` suffices. -/
theorem lower_bound_deterministic : LowerBoundDeterministic := lower_bound_deterministic_proof

/-- The hard bodies: compact, convex, diameter `D`, exactly `β`-smooth, not uniformly convex. -/
theorem hard_body_geometry : HardBodyGeometry := hard_body_geometry_proof

/-- The explicit minimizer, and the failure of local dual sharpness there. -/
theorem hard_body_optimum : HardBodyOptimum := hard_body_optimum_proof

/-- Without jitter, the bulged body reveals the hidden set in one vertical query. -/
theorem symmetric_bulge_reveals : SymmetricBulgeReveals := symmetric_bulge_reveals_proof

/-- Rolling ball and parallel body for `β`-smooth bodies. -/
theorem rolling_ball_parallel_body : RollingBall := rolling_ball_proof

/-- The matching upper bound: a method requiring no more than `T` oracle calls. -/
theorem quadratic_upper_bound : QuadraticUpperBound := quadratic_upper_bound_proof

/-- Sliding for smooth convex objectives. -/
theorem sliding_upper_bound : SlidingUpperBound := sliding_upper_bound_proof

/-- A linear rate with inner and outer tangent balls. -/
theorem joint_linear_rate : JointLinearRate := joint_linear_rate_proof

/-- The bound of Grimmer and Liu is of order `1/T²` at fixed parameters. -/
theorem grimmer_liu_comparison : GrimmerLiuComparison := grimmer_liu_comparison_proof
-- DOCS_END_MAIN

end Lemmata.FrankWolfePS
