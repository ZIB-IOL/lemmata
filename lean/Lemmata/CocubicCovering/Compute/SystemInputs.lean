module

public import Lemmata.CocubicCovering.Compute.Soundness
public meta import Lemmata.CocubicCovering.Compute.Soundness
public import Lemmata.CocubicCovering.Proof.LevelSixSystemData
public meta import Lemmata.CocubicCovering.Proof.LevelSixSystemData

@[expose] public section

namespace Lemmata.CocubicCovering.Compute.Systems

open Lemmata.CocubicCovering

def inputs (system : Fin 13) : Polynomial.Inputs :=
  List.ofFn (CoveringLevelSixSystems.input system)

def numVars (system : Fin 13) : Nat :=
  CoveringLevelSixReconstruction.crossCount system +
    15 * (2 * CoveringLevelSixSystems.pairs system - CoveringLevelSixSystems.crossRank system)

theorem eval_eq (assignment : Nat → Field) (polynomial : List Nat) :
    Algebra.eval assignment polynomial = CoveringIdeal.eval assignment polynomial := rfl

theorem checked_of_halves
    (first : ∀ system : Fin 6,
      Polynomial.refutes (numVars (Fin.ofNat 13 system.val)) 6
        (inputs (Fin.ofNat 13 system.val)) = true)
    (last : ∀ system : Fin 7,
      Polynomial.refutes (numVars (Fin.ofNat 13 (6 + system.val))) 6
        (inputs (Fin.ofNat 13 (6 + system.val))) = true) :
    ∀ system : Fin 13, Polynomial.refutes (numVars system) 6 (inputs system) = true := by
  intro system
  by_cases small : system.val < 6
  · have index : Fin.ofNat 13 system.val = system := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt system.isLt
    simpa only [index] using first ⟨system.val, small⟩
  · let offset : Fin 7 := ⟨system.val - 6, by omega⟩
    have value : 6 + offset.val = system.val := by dsimp [offset]; omega
    have index : Fin.ofNat 13 (6 + offset.val) = system := by
      apply Fin.ext
      change (6 + offset.val) % 13 = system.val
      rw [value, Nat.mod_eq_of_lt system.isLt]
    simpa only [index] using last offset

end Lemmata.CocubicCovering.Compute.Systems
