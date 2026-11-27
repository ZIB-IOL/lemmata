module

public import Lemmata.GrothendieckLowerBounds.Data3Orbit
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public meta import Lemmata.GrothendieckLowerBounds.Data3Orbit

/-! Finite integer checks for the 301-row witness. The column signing in the
supplement specifies Bob's signs. Maximizing over Alice gives its one-norm score. -/

@[expose] public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators

/-- All entries parse, and the tables have the dimensions used by the finite sums. -/
theorem dataOrbit_wellFormed :
    (mOrbitRows.all rowWellFormed && aOrbitRows.all rowWellFormed &&
      bOrbitRows.all rowWellFormed && rowWellFormed sOrbitRow) = true ∧
    mOrbitTable.size = 301 ∧ mOrbitTable.all (·.size == 321) = true ∧
    aOrbitTable.size = 301 ∧ aOrbitTable.all (·.size == 3) = true ∧
    bOrbitTable.size = 321 ∧ bOrbitTable.all (·.size == 3) = true ∧
    sOrbitTable.size = 321 := by
  native_decide

/-- The rational row triples lie in the unit ball at denominator `10^40`. -/
theorem aOrbit_ball : ∀ i : Fin 301, ∑ k : Fin 3, aOrbitZ i k ^ 2 ≤ 10 ^ 80 := by
  native_decide

/-- The rational column triples lie in the same unit ball. -/
theorem bOrbit_ball : ∀ j : Fin 321, ∑ k : Fin 3, bOrbitZ j k ^ 2 ≤ 10 ^ 80 := by
  native_decide

/-- The vector objective multiplied by the square of the common denominator. -/
theorem objectiveOrbit :
    ∑ i : Fin 301, ∑ j : Fin 321, mOrbitZ i j * ∑ k : Fin 3, aOrbitZ i k * bOrbitZ j k =
      92422356381691369081494724621543334927103898587805286507057963067018402350722593401925517175131539945819591534 := by
  native_decide

/-- Every coordinate of the attaining column assignment is a sign. -/
theorem sOrbit_signs : ∀ j : Fin 321, sOrbitZ j = 1 ∨ sOrbitZ j = -1 := by
  native_decide

/-- The exact classical score attained by this column assignment. -/
theorem attainedOrbit :
    ∑ i : Fin 301, |∑ j : Fin 321, sOrbitZ j * mOrbitZ i j| = 641951269303647081416258863417 := by
  native_decide

end Lemmata.GrothendieckLowerBounds
