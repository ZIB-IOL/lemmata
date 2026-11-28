module

public import Lemmata.FWCaratheodory.Hadamard

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
-- DOCS_END_MAIN

end Lemmata.FWCaratheodory
