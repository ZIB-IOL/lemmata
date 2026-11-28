module

public import Lemmata.FWSelfConcordant.Monotonic

@[expose] public section

namespace Lemmata.FWSelfConcordant

-- DOCS_BEGIN_MAIN
/-- Theorem 2.4: monotonic Frank–Wolfe with the simple steps `2/(t + 2)` converges at the rate
`4 (T + 1)/(t + 1) max {h₀, K}` from `T` on, under the local descent property. -/
theorem monotonic_rate : MonotonicRate := Proof.monotonic_rate

/-- Theorem 2.6: the smallest Frank–Wolfe gap among the first `N` iterations is `O(1/N)`. -/
theorem monotonic_gap_rate : MonotonicGapRate := Proof.monotonic_gap_rate
-- DOCS_END_MAIN

end Lemmata.FWSelfConcordant
