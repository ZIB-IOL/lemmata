module

public import Lemmata.CocubicCovering.Compute.SystemInputs
public meta import Lemmata.CocubicCovering.Compute.SystemInputs

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Systems

theorem checkedLast : ∀ system : Fin 7,
    Polynomial.refutes (numVars (Fin.ofNat 13 (6 + system.val))) 6
      (inputs (Fin.ofNat 13 (6 + system.val))) = true := by
  native_decide

end Lemmata.CocubicCovering.Compute.Systems
