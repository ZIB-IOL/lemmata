module

public import Lemmata.CocubicCovering.Compute.LevelSixModel
public meta import Lemmata.CocubicCovering.Compute.LevelSixModel
public import Lemmata.CocubicCovering.Compute.Terminal
public meta import Lemmata.CocubicCovering.Compute.Terminal

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.LevelSixModel

theorem interpretation : Terminal.Interpretation model where
  kernel := rfl
  coordinates root v allowed i :=
    Lemmata.CocubicCovering.CoveringLevelSixProblem.allowed_coordinates
      (Fin.ofNat 30 root) v allowed.1 i
  dimension _ _ allowed := allowed.1.2.2.1
  rank _ _ allowed := allowed.1.2.2.2
  inconsistent _ _ allowed := allowed.2

def terminal (state : CoreSearch.State) : Option (CoreSearch.Closed model state) :=
  Terminal.close model interpretation state

end Lemmata.CocubicCovering.Compute.LevelSixModel
