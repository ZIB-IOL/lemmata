module

public import Lemmata.BPCG.Proof

@[expose] public section

namespace Lemmata.BPCG

-- DOCS_BEGIN_MAIN
/-- Theorem 3.1: BPCG converges at the rate `4 L D²/T` for convex objectives. -/
theorem convex_rate : ConvexRate := Proof.bpcg_convex_rate

/-- Theorem 3.2: BPCG converges linearly over polytopes for strongly convex objectives. -/
theorem linear_rate : LinearRate := Proof.bpcg_linear_rate
-- DOCS_END_MAIN

end Lemmata.BPCG
