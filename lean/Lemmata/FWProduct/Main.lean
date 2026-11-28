module

public import Lemmata.FWProduct.Objective

@[expose] public section

namespace Lemmata.FWProduct

-- DOCS_BEGIN_MAIN
/-- Proposition 5.1: the feasibility objective `(1/(2k)) ∑_{i<j} ‖x^i - x^j‖²` is convex,
`1`-smooth with a `1`-Lipschitz derivative, and `‖f'(x)‖² = 2 f(x)`, so it is `1`-PL. -/
theorem feasibility_objective : FeasibilityObjective := Proof.feasibility_objective

/-- Lemma A.2: `min {a, b}/√2 ≤ √(a²b²/(a² + b²)) < min {a, b}`, monotone in each argument. -/
theorem preparatory_bounds : PreparatoryBounds := Proof.preparatory_bounds
-- DOCS_END_MAIN

end Lemmata.FWProduct
