module

public import Lemmata.FrankWolfeLDS.Statement
public import Lemmata.FrankWolfeLDS.Proof.Interfaces

@[expose] public section

/-!
# Frank–Wolfe beyond `1/t` under local dual sharpness

Each theorem proves the proposition of the same name in `Statement.lean`, the result of
*Frank–Wolfe Beyond 1/t Convergence* (arXiv:2604.28006) named in its docstring. The proofs are
in `Proof/`; `Proof/Interfaces.lean` derives the statements from the development.
-/

namespace Lemmata.FrankWolfeLDS

-- DOCS_BEGIN_MAIN
/-- Proposition 2.2. -/
theorem standard_rate : StandardRate := Proof.standard_rate

/-- Proposition 3.4. -/
theorem uniformly_convex_lds : UniformlyConvexImpliesLDS := Proof.uniformly_convex_lds

/-- Theorem 3.5. -/
theorem conditional_short_step_line_search : ConditionalShortStepLineSearch := Proof.conditional_short_step_line_search

/-- Theorem 3.6. -/
theorem zero_gradient_minimizer : ZeroGradientMinimizer := Proof.zero_gradient_minimizer

/-- Proposition 3.7. -/
theorem gradient_bounded_below : GradientBoundedBelow := Proof.gradient_bounded_below

/-- Corollary 3.8. -/
theorem beyond_one_over_t : BeyondOneOverT := Proof.beyond_one_over_t

/-- Theorem 3.9. -/
theorem conditional_open_loop : ConditionalOpenLoop := Proof.conditional_open_loop

/-- Theorem 3.10. -/
theorem open_loop_rate : OpenLoopRate := Proof.open_loop_rate

/-- Theorem 4.2. -/
theorem holder_error_bound_rate : HolderErrorBoundRate := Proof.holder_error_bound_rate

/-- Lemma A.1. -/
theorem uniformly_convex_gap : UniformlyConvexGap := Proof.uniformly_convex_gap

/-- Proposition A.2. -/
theorem patch_criterion : PatchCriterion := Proof.patch_criterion
-- DOCS_END_MAIN

end Lemmata.FrankWolfeLDS
