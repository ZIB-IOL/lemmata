module

public import Lemmata.GrothendieckLowerBounds.Data5
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public meta import Lemmata.GrothendieckLowerBounds.Data5

/-! # The order-five witness, checked by computation

Finite checks of the data in `Data5.lean`: every entry parses, the tables have their
stated shapes, every vector lies in the unit ball of `ℝ^5`, the value of the vectors is the
stated rational number, and the signs attain the classical value. -/

@[expose] public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators

/-- Every entry parses, and the tables have the stated shapes. -/
theorem data5_wellFormed :
    (m5Rows.all rowWellFormed && a5Rows.all rowWellFormed && b5Rows.all rowWellFormed &&
      rowWellFormed s5Row) = true ∧
    m5Table.size = 80 ∧ m5Table.all (·.size == 269) = true ∧ a5Table.size = 80 ∧
    a5Table.all (·.size == 5) = true ∧ b5Table.size = 269 ∧ b5Table.all (·.size == 5) = true ∧
    s5Table.size = 80 := by
  native_decide

/-- The row vectors lie in the unit ball: their squared numerators sum to at most `10³⁰`. -/
theorem a5_ball : ∀ i : Fin 80, ∑ k : Fin 5, a5Z i k ^ 2 ≤ 10 ^ 30 := by
  native_decide

/-- The column vectors lie in the unit ball. -/
theorem b5_ball : ∀ j : Fin 269, ∑ k : Fin 5, b5Z j k ^ 2 ≤ 10 ^ 30 := by
  native_decide

/-- The exact value of the vectors, times `10³⁰`. -/
theorem objective5 :
    ∑ i : Fin 80, ∑ j : Fin 269, m5Z i j * ∑ k : Fin 5, a5Z i k * b5Z j k = 1379089182810903048332452323838491520594 := by
  native_decide

/-- The attaining assignment consists of signs. -/
theorem s5_signs : ∀ i : Fin 80, s5Z i = 1 ∨ s5Z i = -1 := by
  native_decide

/-- The signs attain the classical value. -/
theorem attained5 : ∑ j : Fin 269, |∑ i : Fin 80, s5Z i * m5Z i j| = 919782264 := by
  native_decide

end Lemmata.GrothendieckLowerBounds
