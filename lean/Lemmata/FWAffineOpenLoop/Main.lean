module

public import Lemmata.FWAffineOpenLoop.StrongR

@[expose] public section

namespace Lemmata.FWAffineOpenLoop

-- DOCS_BEGIN_MAIN
/-- Theorem 3.1: under strong `(M, 0)`-growth, the best duality gap is at most `η_t M`. -/
theorem pd_rate_strong_zero : PDRateStrongZero := Proof.pd_rate_strong_zero

/-- Lemma 3.3: `∏_{i=S}^{t} (1 - η_i) ≤ (η_t/η_{S-1})^ℓ`. -/
theorem product_bound : ProductBound := Proof.product_bound

/-- Lemma 3.5: `∏_{i=S}^{t} (1 - (1 - ε/ℓ) η_i) ≤ (η_t/η_{S-1})^{ℓ-ε} exp(εℓ/S)`. -/
theorem product_bound_eps : ProductBoundEps := Proof.product_bound_eps

/-- Theorem 3.2: under strong `(M, 1)`-growth, rate `O(t^{-ℓ})` for the best duality gap and the
smallest Frank–Wolfe gap. -/
theorem pd_rate_strong_one : PDRateStrongOne := Proof.pd_rate_strong_one

/-- Theorem 3.4: under strong `(M, r)`-growth, rate `O(t^{-ℓ+ε} + t^{-1/(1-r)})` for the best
duality gap and the smallest Frank–Wolfe gap. -/
theorem pd_rate_strong : PDRateStrong := Proof.pd_rate_strong
-- DOCS_END_MAIN

end Lemmata.FWAffineOpenLoop
