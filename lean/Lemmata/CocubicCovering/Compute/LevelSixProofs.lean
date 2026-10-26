module

public import Lemmata.CocubicCovering.Compute.LevelSixOrbit
public meta import Lemmata.CocubicCovering.Compute.LevelSixOrbit

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.LevelSixModel

theorem roots_checked : ∀ root : Fin 21, orbitChecked root = true := by
  native_decide

theorem no_state (root : Fin 21) : ¬CoreSearch.Feasible model ⟨root.val, []⟩ :=
  orbitExcludes root (roots_checked root)

end Lemmata.CocubicCovering.Compute.LevelSixModel
