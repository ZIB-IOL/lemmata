module

public import Lemmata.LazyCG.Proof
public import Lemmata.LazyCG.ParamFree
public import Lemmata.LazyCG.LPCG
public import Lemmata.LazyCG.Augment

@[expose] public section

namespace Lemmata.LazyCG

-- DOCS_BEGIN_MAIN
/-- Algorithm 2, with a minimizing linear optimization oracle, answers the weak separation oracle
correctly. -/
theorem lp_sep_via_lp_correct : LPSepViaLPCorrect := Proof.lp_sep_via_lp_correct

/-- Theorem 3.1: lazy conditional gradients converge at the rate
`2 max {C, Φ₀} (K² + 1)/(t + K² + 2)`. -/
theorem lcg_rate : LCGRate := Proof.lcg_rate

/-- Theorem 4.2: the iteration count of parameter-free lazy conditional gradients. -/
theorem param_free_rate : ParamFreeRate := Proof.param_free_rate

/-- Corollary 4.3: parameter-free lazy conditional gradients receive few negative answers. -/
theorem param_free_negatives : ParamFreeNegatives := Proof.param_free_negatives

/-- Theorem 3.2: lazy pairwise conditional gradients converge linearly on simplex-like polytopes. -/
theorem lpcg_rate : LPCGRate := Proof.lpcg_rate

/-- Proposition 6.1: weak separation through augmentation answers correctly. -/
theorem aug_sep_correct : AugSepCorrect := Proof.aug_sep_correct
-- DOCS_END_MAIN

end Lemmata.LazyCG
