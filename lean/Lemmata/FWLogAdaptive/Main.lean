module

public import Lemmata.FWLogAdaptive.Rates

@[expose] public section

namespace Lemmata.FWLogAdaptive

-- DOCS_BEGIN_MAIN
/-- The log-adaptive choice `g(t) = 2 + log(t + 1)` satisfies Assumptions A1 and A2. -/
theorem logStep_admissible : LogStepAdmissible := Proof.logStep_admissible

/-- Lemma 3.1, for `ε ≤ g(S) - 1`: `∏_{i=S}^t (1 - (1 - ε/g(i)) η_i) ≤ (η_t/η_{S-1})^{g(S)-ε}`. -/
theorem product_bound : ProductBound := Proof.product_bound

/-- Theorem 3.2: under strong `(M, r)`-growth, rate `O(g(t-1)^{1/(1-r)} η_{t-1}^k)` for the best
duality gap, `k = min {g(S) - ε, 1/(1-r)}`. -/
theorem strong_rate : StrongRate := Proof.strong_rate

/-- Theorem 3.2 for the log-adaptive step sizes: rate `Õ(t^{-1/(1-r)})`. -/
theorem log_strong_rate : LogStrongRate := Proof.log_strong_rate

/-- Theorem 4.1: under strong `(M, 0)`- and weak `(M, r)`-growth, rate
`O(g(t-1)^{1/(1-r)} η_{t-1}^k)` for the primal gap, `k = min {g(S) - ε, 1/(1-r), 2}`. -/
theorem weak_rate : WeakRate := Proof.weak_rate

/-- Theorem 4.1 for the log-adaptive step sizes: rate `Õ(t^{-1/(1-r)} + t^{-2})`. -/
theorem log_weak_rate : LogWeakRate := Proof.log_weak_rate
-- DOCS_END_MAIN

end Lemmata.FWLogAdaptive
