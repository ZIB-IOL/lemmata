module

public import Lemmata.LPHardnessInP.Matching.Main
public import Lemmata.LPHardnessInP.Joins.Main
public import Lemmata.LPHardnessInP.Parity.Main
public import Lemmata.LPHardnessInP.ObjectiveReversal.Main
public import Lemmata.LPHardnessInP.ParityExtension.Main

@[expose] public section

namespace Lemmata.LPHardnessInP

-- DOCS_BEGIN_MAIN
/-
The four application theorems concern concrete combinatorial domains and
actual edge costs. Each concludes L ≤ m + 1 from an explicit shifted
nonnegative-rank lower bound and a formulation with affine certificates.
The parity extension below derives the rank bound from explicit JSY
partition and entropy hypotheses. General Farkas certificate existence
and the earlier source theorems remain external.
-/
export Matching (matching_lp_lower_bound oddCut_lp_lower_bound)
export Joins (vjoin_lp_lower_bound)
export Parity (parity_matching_lp_lower_bound)
export ParityExtension (parity_lp_lower_bound_from_jsy)
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP
