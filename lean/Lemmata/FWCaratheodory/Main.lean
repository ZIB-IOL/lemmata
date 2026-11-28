module

public import Lemmata.FWCaratheodory.Hadamard
public import Lemmata.FWCaratheodory.Cardinality
public import Lemmata.FWCaratheodory.Uniform

@[expose] public section

namespace Lemmata.FWCaratheodory

-- DOCS_BEGIN_MAIN
/-- Lemma 3.1: `‖z - x⋆‖_p²/2` is differentiable, convex and `(p - 1)`-smooth, its derivative is
`(p - 1)`-Lipschitz with `‖f'(z)‖ = ‖z - x⋆‖_p`, and it is `√2`-sharp on every set containing
`x⋆`. -/
theorem lp_objective : LpObjective := Proof.lp_objective

/-- Theorem 8.1: approximating the barycenter of the normalized columns of a Hadamard matrix to
accuracy `ε` in `ℓ_p` needs at least `1/(ε² + 1/n)` columns. -/
theorem hadamard_lower_bound : HadamardLowerBound := Proof.hadamard_lower_bound
/-- Every Frank–Wolfe run that starts at a point of `V` and uses atoms in `V` writes `x_t` as a
convex combination of at most `t + 1` points of `V`. -/
theorem run_sparsity : RunSparsity := Proof.run_sparsity

/-- Corollary 5.1 for short steps: `O(p D²/ε²)` vertices. -/
theorem short_step_cardinality : ShortStepCardinality := Proof.short_step_cardinality

/-- Corollary 5.3: `O(p (D/r)² log(1/ε))` vertices for a target in the relative interior. -/
theorem interior_cardinality : InteriorCardinality := Proof.interior_cardinality

/-- Corollaries 5.4 and 5.5: over `(α, q)`-uniformly convex sets, `O(ε^{-2(q-1)/q})` atoms suffice,
`O(1/ε)` for strongly convex sets. -/
theorem uniformly_convex_cardinality : UniformlyConvexCardinality :=
  Proof.uniformly_convex_cardinality

/-- Corollary 7.1: `O(p/(α c) log(1/ε))` points for approximate projections onto strongly convex
sets. -/
theorem projection_cardinality : ProjectionCardinality := Proof.projection_cardinality
/-- Corollary 7.2: sparse approximate projections onto `(α, q)`-uniformly convex sets with `q > 2`.
-/
theorem uniformly_convex_projection_cardinality : UniformlyConvexProjectionCardinality :=
  Proof.uniformly_convex_projection_cardinality
-- DOCS_END_MAIN

end Lemmata.FWCaratheodory
