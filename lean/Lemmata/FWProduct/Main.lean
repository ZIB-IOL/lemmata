module

public import Lemmata.FWProduct.Objective
public import Lemmata.FWProduct.Width
public import Lemmata.FWProduct.Upper
public import Lemmata.FWProduct.Facet
public import Lemmata.FWProduct.Relint
public import Lemmata.FWProduct.KFold

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

/-- Lemma 4.3: a point of the affine hull of a face that realizes the affine pyramidal width lies in
the relative interior of the face. -/
theorem affine_width_relint : AffineWidthRelint := Proof.affine_width_relint

/-- Corollary 4.4: the affine pyramidal width equals the pyramidal width. -/
theorem affine_width_eq : AffineWidthEq := Proof.affine_width_eq

/-- Theorem 4.5, the lower bound: the pyramidal width of `conv V₁ × conv V₂` is at least
`√(ŵ₁² ŵ₂²/(ŵ₁² + ŵ₂²))` for the affine pyramidal widths `ŵ₁, ŵ₂` of the factors. -/
theorem product_width_lower : ProductWidthLowerBound := Proof.product_width_lower
/-- Theorem 4.5, the upper bound: for factors with at least two vertices, the pyramidal width of
`conv V₁ × conv V₂` is at most `√(δ₁² δ₂²/(δ₁² + δ₂²))` for the pyramidal widths `δ₁, δ₂`. -/
theorem product_width_upper : ProductWidthUpperBound := Proof.product_width_upper

/-- Theorem 4.5: the pyramidal width of a product of two polytopes is `√(δ₁² δ₂²/(δ₁² + δ₂²))`. -/
theorem product_width_eq : ProductWidthEq := Proof.product_width_eq

/-- Corollary A.3, with the exact value: the pyramidal width of a product of `k` polytopes is
`(∑ δ_i^{-2})^{-1/2}`, hence at least `min_i δ_i/√k`. -/
theorem product_width_many : ProductWidthMany := Proof.product_width_many

/-- Proposition 4.8 for two factors: away-step Frank–Wolfe over the product converges linearly
under quadratic growth, at a rate governed by `α² = ŵ₁² ŵ₂²/(ŵ₁² + ŵ₂²)`. -/
theorem product_away_linear : ProductAwayLinear := Proof.product_away_linear
/-- Proposition 4.7: the vertex-facet distance of `conv V₁ × conv V₂` is the smaller of the
vertex-facet distances of the factors. -/
theorem product_vertex_facet : ProductVertexFacet := Proof.product_vertex_facet
-- DOCS_END_MAIN

end Lemmata.FWProduct
