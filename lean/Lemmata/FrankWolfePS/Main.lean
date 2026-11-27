module

public import Lemmata.FrankWolfePS.CompactTrial
public import Lemmata.FrankWolfePS.OptimalOrder
public import Lemmata.FrankWolfePS.RandomHilbert.Result
public import Lemmata.FrankWolfePS.Proofs
public import Lemmata.FrankWolfePS.HilbertAnytimeGeometry

@[expose] public section

namespace Lemmata.FrankWolfePS

-- DOCS_BEGIN_MAIN
/-- Lower bound without tie-breaking: on some body of the class `𝒞(β, D, x₀)`, every measurable
randomized method requiring no more than `T` LMO calls fails with probability at least `1/5`. -/
theorem lower_bound_unique_lmo : LowerBoundUniqueLMO := lower_bound_unique_lmo_proof

/-- Methods with feasible outputs: probability `3/4`, and the expected primal gap. -/
theorem lower_bound_unique_feasible : LowerBoundUniqueFeasible :=
  lower_bound_unique_feasible_proof

/-- The hard bodies with the vertex LMO: diameter exactly `D`, probability `1/4`. -/
theorem lower_bound_vertex_lmo : LowerBoundVertexLMO := lower_bound_vertex_lmo_proof

/-- The expected ratio of undecided indices is `(d - 1)/(N - 1)`. -/
theorem posterior_ratio_identity : PosteriorIdentity := posterior_identity_proof

/-- The vertex LMO and methods with feasible outputs: probability `3/4`, and the expected
primal gap. -/
theorem lower_bound_feasible : LowerBoundFeasible := lower_bound_feasible_proof

/-- A penalty for infeasible outputs: the penalized error in probability and in the mean. -/
theorem lower_bound_penalized : LowerBoundPenalized := lower_bound_penalized_proof

/-- Deterministic methods: dimension `64 (T + 1) + 1` suffices. -/
theorem lower_bound_deterministic : LowerBoundDeterministic := lower_bound_deterministic_proof

/-- The hard bodies: diameter `D`, exactly `β`-smooth, not strongly convex. -/
theorem hard_body_geometry : HardBodyGeometry := hard_body_geometry_proof

/-- The minimizer of the objective on a hard body; local dual sharpness fails there. -/
theorem hard_body_optimum : HardBodyOptimum := hard_body_optimum_proof

/-- Without perturbed vertices, the lowest point of the thickened simplex reveals `I`. -/
theorem symmetric_thickening_reveals : SymmetricThickeningReveals :=
  symmetric_thickening_reveals_proof

/-- A `β`-smooth set is its inner parallel body plus a ball of radius `1/β`. -/
theorem rolling_ball_parallel_body : RollingBall := rolling_ball_proof

/-- Upper bound: Frank–Wolfe on the inner parallel body, no more than `T` LMO calls. -/
theorem quadratic_upper_bound : QuadraticUpperBound := quadratic_upper_bound_proof

/-- Smooth convex objectives: conditional gradient sliding on `K × B_{1/β}`. -/
theorem sliding_upper_bound : SlidingUpperBound := sliding_upper_bound_proof

/-- A linear rate with inner and outer tangent balls. -/
theorem tangent_balls_linear_rate : TangentBallsLinearRate := tangent_balls_linear_rate_proof

/-- The bound of Grimmer and Liu is of order `1/T²` at fixed parameters. -/
theorem grimmer_liu_comparison : GrimmerLiuComparison := grimmer_liu_comparison_proof
-- DOCS_END_MAIN

end Lemmata.FrankWolfePS
