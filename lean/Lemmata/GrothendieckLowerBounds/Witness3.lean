module

public import Lemmata.GrothendieckLowerBounds.Data3
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public meta import Lemmata.GrothendieckLowerBounds.Data3

/-! # The order-three witness, checked by computation

Finite checks of the data in `Data3.lean`: every entry parses, the tables have their
stated shapes, every vector lies in the unit ball of `ℝ^3`, the value of the vectors is the
stated rational number, and the signs attain the classical value. -/

@[expose] public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators

/-- Every entry parses, and the tables have the stated shapes. -/
theorem data3_wellFormed :
    (m3Rows.all rowWellFormed && a3Rows.all rowWellFormed && b3Rows.all rowWellFormed &&
      rowWellFormed s3Row) = true ∧
    m3Table.size = 81 ∧ m3Table.all (·.size == 321) = true ∧ a3Table.size = 81 ∧
    a3Table.all (·.size == 3) = true ∧ b3Table.size = 321 ∧ b3Table.all (·.size == 3) = true ∧
    s3Table.size = 81 := by
  native_decide

/-- The row vectors lie in the unit ball: their squared numerators sum to at most `10³⁰`. -/
theorem a3_ball : ∀ i : Fin 81, ∑ k : Fin 3, a3Z i k ^ 2 ≤ 10 ^ 30 := by
  native_decide

/-- The column vectors lie in the unit ball. -/
theorem b3_ball : ∀ j : Fin 321, ∑ k : Fin 3, b3Z j k ^ 2 ≤ 10 ^ 30 := by
  native_decide

/-- The exact value of the vectors, times `10³⁰`. -/
theorem objective3 :
    ∑ i : Fin 81, ∑ j : Fin 321, m3Z i j * ∑ k : Fin 3, a3Z i k * b3Z j k = 461845159210737970564046146266219485493 := by
  native_decide

/-- The attaining assignment consists of signs. -/
theorem s3_signs : ∀ i : Fin 81, s3Z i = 1 ∨ s3Z i = -1 := by
  native_decide

/-- The signs attain the classical value. -/
theorem attained3 : ∑ j : Fin 321, |∑ i : Fin 81, s3Z i * m3Z i j| = 320975296 := by
  native_decide

end Lemmata.GrothendieckLowerBounds
