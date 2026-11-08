module

public import Lemmata.RM59.Proof.SimplexSearchCheckCore
public meta import Lemmata.RM59.Proof.SimplexSearchCheckCore
public meta import Lean.Elab.Tactic.Decide

@[expose] public section

namespace Lemmata.RM59.SimplexSearchChecks

theorem chunk0_checked : chunkCheck 0 = true := by native_decide

end Lemmata.RM59.SimplexSearchChecks
