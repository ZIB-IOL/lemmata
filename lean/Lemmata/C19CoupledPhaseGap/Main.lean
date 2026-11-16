module

public import Lemmata.C19CoupledPhaseGap.Statement
public import Mathlib.Tactic.Positivity

public section

namespace Lemmata.C19CoupledPhaseGap

-- DOCS_BEGIN_MAIN
/-- The C19 coupled-phase propagating eigenvalue is strictly positive. -/
theorem coupledPhaseGap : CoupledPhaseGap := by
  unfold CoupledPhaseGap
  intro psiRadius chiRadius k0 k1 k2 hpsi hchi hmode
  unfold propagatingOmegaSquared phaseStiffness
  have hpsi2 : 0 < psiRadius ^ 2 := sq_pos_of_ne_zero hpsi
  have hchi2 : 0 < chiRadius ^ 2 := sq_pos_of_ne_zero hchi
  positivity
-- DOCS_END_MAIN

end Lemmata.C19CoupledPhaseGap
