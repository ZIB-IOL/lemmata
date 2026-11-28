module

public import Lemmata.FWAffineOpenLoop.StrongR
public import Lemmata.FWAffineOpenLoop.Gaps
public import Lemmata.FWAffineOpenLoop.Sufficient

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

/-- Theorem 4.1: under strong `(M, 0)`- and weak `(M, r)`-growth, rate
`O(t^{-ℓ+ε} + t^{-1/(1-r)} + t^{-2})` for the primal gap, and the dichotomy of the paper. -/
theorem weak_rate : WeakRate := Proof.weak_rate

/-- Lemma 4.2: a bound on the next iteration whose primal gap is below the threshold. -/
theorem weak_restart : WeakRestart := Proof.weak_restart

/-- Theorem 5.2: under strong `(M, 0)`-growth and relaxed gaps growth along the run, rate
`O(t^{-ℓ} + t^{-1/(1-r)} + t^{-2})` for the primal gap. -/
theorem relaxed_gaps_rate : RelaxedGapsRate := Proof.relaxed_gaps_rate

/-- Theorem 5.1: the same rate under the gaps `(m, r)`-growth property. -/
theorem gaps_rate : GapsRate := Proof.gaps_rate
/-- Proposition 2.8: smoothness gives the strong `(L D², 0)`-growth property. -/
theorem smooth_strong_growth : SmoothStrongGrowth := Proof.smooth_strong_growth

/-- Proposition 3.6: uniformly convex sets with gradients bounded away from zero give strong
`(L (αλ)^{-2/p}, 2/p)`-growth. -/
theorem uniform_strong_growth : UniformStrongGrowth := Proof.uniform_strong_growth

/-- Proposition 4.3: uniformly convex sets with a Hölderian error bound give weak
`(L (μ/α)^{2/p}, 2θ/p)`-growth. -/
theorem uniform_weak_growth : UniformWeakGrowth := Proof.uniform_weak_growth

/-- Proposition 5.3: minimizers in the relative interior give gaps `(ρ/μ, θ)`-growth. -/
theorem interior_gaps_growth : InteriorGapsGrowth := Proof.interior_gaps_growth
-- DOCS_END_MAIN

end Lemmata.FWAffineOpenLoop
