module

public import Lemmata.BPCG.Proof
public import Lemmata.BPCG.Lazy
public import Lemmata.BPCG.LazyLinear

@[expose] public section

namespace Lemmata.BPCG

-- DOCS_BEGIN_MAIN
/-- Theorem 3.1: BPCG converges at the rate `4 L D²/T` for convex objectives. -/
theorem convex_rate : ConvexRate := Proof.bpcg_convex_rate

/-- Theorem 3.2: BPCG converges linearly over polytopes for strongly convex objectives. -/
theorem linear_rate : LinearRate := Proof.bpcg_linear_rate

/-- Theorem 3.6, case (B), with explicit constants: lazified BPCG for convex objectives. -/
theorem lazy_convex_rate : LazyConvexRate := Proof.lazy_convex_rate

/-- Theorem 3.6, case (A), with explicit constants: lazified BPCG for strongly convex objectives. -/
theorem lazy_linear_rate : LazyLinearRate := Proof.lazy_linear_rate
-- DOCS_END_MAIN

end Lemmata.BPCG
