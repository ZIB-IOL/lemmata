module

public import Lemmata.CocubicCovering.Compute.SystemInputs
public meta import Lemmata.CocubicCovering.Compute.SystemInputs

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Systems

theorem checkedFirst : ∀ system : Fin 6,
    Polynomial.refutes (numVars (Fin.ofNat 13 system.val)) 6
      (inputs (Fin.ofNat 13 system.val)) = true := by
  native_decide

end Lemmata.CocubicCovering.Compute.Systems
