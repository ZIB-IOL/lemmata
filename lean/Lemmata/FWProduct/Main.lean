module

public import Lemmata.FWProduct.Objective
public import Lemmata.FWProduct.Width

@[expose] public section

namespace Lemmata.FWProduct

-- DOCS_BEGIN_MAIN
/-- Proposition 5.1: the feasibility objective `(1/(2k)) ∑_{i<j} ‖x^i - x^j‖²` is convex,
`1`-smooth with a `1`-Lipschitz derivative, and `‖f'(x)‖² = 2 f(x)`, so it is `1`-PL. -/
theorem feasibility_objective : FeasibilityObjective := Proof.feasibility_objective

/-- Lemma A.2: `min {a, b}/√2 ≤ √(a²b²/(a² + b²)) < min {a, b}`, monotone in each argument. -/
theorem preparatory_bounds : PreparatoryBounds := Proof.preparatory_bounds
/-- Corollary 4.4, the easy inequality: the affine pyramidal width is at most the pyramidal width
(the facial distance). -/
theorem affine_width_le_facial : AffineWidthLeFacial := Proof.affine_width_le_facial

/-- Theorem 4.5, the lower bound: the pyramidal width of `conv V₁ × conv V₂` is at least
`√(ŵ₁² ŵ₂²/(ŵ₁² + ŵ₂²))` for the affine pyramidal widths `ŵ₁, ŵ₂` of the factors. -/
theorem product_width_lower : ProductWidthLowerBound := Proof.product_width_lower
-- DOCS_END_MAIN

end Lemmata.FWProduct
