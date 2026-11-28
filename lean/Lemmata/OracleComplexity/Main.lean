module

public import Lemmata.OracleComplexity.Tree

@[expose] public section

namespace Lemmata.OracleComplexity

-- DOCS_BEGIN_MAIN
/-- Lemma III.1: if every query reveals at most `C` nats about the instance, then
`H(F) ≤ C E[T] + h(P_e) + P_e log(|F| - 1)`. -/
theorem info_lower_bound : InfoLowerBound := Proof.info_lower_bound

/-- Lemma III.5: an algorithm for an emulated oracle runs with the emulating oracle, with the same
outputs and the same numbers of queries. -/
theorem emulation : Emulation := Proof.emulation
-- DOCS_END_MAIN

end Lemmata.OracleComplexity
