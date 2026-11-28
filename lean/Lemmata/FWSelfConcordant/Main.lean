module

public import Lemmata.FWSelfConcordant.Monotonic
public import Lemmata.FWSelfConcordant.Backtrack
public import Lemmata.FWSelfConcordant.Away
public import Lemmata.FWSelfConcordant.Pairwise

@[expose] public section

namespace Lemmata.FWSelfConcordant

-- DOCS_BEGIN_MAIN
/-- Theorem 2.4: monotonic Frank–Wolfe with the simple steps `2/(t + 2)` converges at the rate
`4 (T + 1)/(t + 1) max {h₀, K}` from `T` on, under the local descent property. -/
theorem monotonic_rate : MonotonicRate := Proof.monotonic_rate

/-- Theorem 2.6: the smallest Frank–Wolfe gap among the first `N` iterations is `O(1/N)`. -/
theorem monotonic_gap_rate : MonotonicGapRate := Proof.monotonic_gap_rate
/-- Theorem 2.11: Frank–Wolfe with backtracking converges linearly when the minimizer is interior
and `f` is strongly convex on the sublevel set. -/
theorem interior_linear_rate : InteriorLinearRate := Proof.interior_linear_rate

/-- Theorem 2.15: rates over uniformly convex sets when the gradient is bounded away from zero. -/
theorem uniformly_convex_gradient_rate : UniformlyConvexGradientRate :=
  Proof.uniformly_convex_gradient_rate

/-- Theorem 2.16: the rate `O(t^{-q/(q-1)})` over `(κ, q)`-uniformly convex sets under local strong
convexity. -/
theorem uniformly_convex_strong_rate : UniformlyConvexStrongRate :=
  Proof.uniformly_convex_strong_rate
/-- Theorem 3.2 for away-step Frank–Wolfe with backtracking: a linear rate over polytopes under
local strong convexity, through the pyramidal width. -/
theorem away_linear_rate : AwayLinearRate := Proof.away_linear_rate
/-- Theorem 3.2 for blended pairwise conditional gradients with backtracking: the same linear rate
over polytopes. -/
theorem pairwise_linear_rate : PairwiseLinearRate := Proof.pairwise_linear_rate
-- DOCS_END_MAIN

end Lemmata.FWSelfConcordant
