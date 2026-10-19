module

public import Mathlib.Logic.Function.Basic

public section

namespace Lemmata.SelfImplication

-- DOCS_BEGIN_MAIN
/-- Every proposition implies itself. -/
theorem self_implication (P : Prop) : P → P :=
  fun hp => hp
-- DOCS_END_MAIN

end Lemmata.SelfImplication

/-- Acceptance test: must be rejected by the cluster. -/
theorem Lemmata.SelfImplication.draft : 1 = 2 := by sorry
