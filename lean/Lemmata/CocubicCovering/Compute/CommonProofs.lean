module

public import Lemmata.CocubicCovering.Compute.CommonOrbit
public meta import Lemmata.CocubicCovering.Compute.CommonOrbit

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.CommonModel

open Lemmata.CocubicCovering
open CoveringWitness CoveringPackedWitness

theorem roots_checked : ∀ root : Fin 6, orbitChecked root = true := by
  native_decide

theorem no_allowed (root : Fin 6) (v : Vector 127) : ¬allowed root.val v := by
  intro hv
  apply orbitExcludes root (roots_checked root)
  refine ⟨v, hv, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

end Lemmata.CocubicCovering.Compute.CommonModel
