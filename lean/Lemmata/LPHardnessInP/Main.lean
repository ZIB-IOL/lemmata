module

public import Lemmata.LPHardnessInP.Matching.Main
public import Lemmata.LPHardnessInP.Joins.Main
public import Lemmata.LPHardnessInP.Parity.Main
public import Lemmata.LPHardnessInP.ObjectiveReversal.Main

@[expose] public section

namespace Lemmata.LPHardnessInP

-- DOCS_BEGIN_MAIN
/-
The four application theorems concern concrete combinatorial domains and
actual edge costs. Each concludes L ≤ m + 1 from an explicit shifted
nonnegative-rank lower bound and a formulation with affine certificates.
The source rank proofs and the existence part of Farkas' lemma are external.
-/
export Matching (matching_lp_lower_bound oddCut_lp_lower_bound)
export Joins (vjoin_lp_lower_bound)
export Parity (parity_matching_lp_lower_bound)
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP
