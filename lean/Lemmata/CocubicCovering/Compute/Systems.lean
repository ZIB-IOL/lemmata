module

public import Lemmata.CocubicCovering.Compute.SystemChecksFirst
public meta import Lemmata.CocubicCovering.Compute.SystemChecksFirst
public import Lemmata.CocubicCovering.Compute.SystemChecksLast
public meta import Lemmata.CocubicCovering.Compute.SystemChecksLast

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Systems

open Lemmata.CocubicCovering

theorem checked : ∀ system : Fin 13,
    Polynomial.refutes (numVars system) 6 (inputs system) = true :=
  checked_of_halves checkedFirst checkedLast

theorem unsatisfiable (system : Fin 13) :
    ¬ ∃ assignment : Nat → Field, ∀ row : Fin 87,
      CoveringIdeal.eval assignment (CoveringLevelSixSystems.input system row) = 0 := by
  intro solution
  apply Polynomial.refutes_sound _ _ _ (checked system)
  obtain ⟨assignment, solution⟩ := solution
  refine ⟨assignment, ?_⟩
  intro polynomial member
  obtain ⟨row, rfl⟩ := List.mem_ofFn.mp member
  exact (eval_eq assignment _).trans (solution row)

end Lemmata.CocubicCovering.Compute.Systems
