module

public import Lemmata.GrothendieckLowerBounds.Data3Split
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public meta import Lemmata.GrothendieckLowerBounds.Data3Split

/-! # The 141-row order-three witness, checked by computation

Finite checks of the data in `Data3Split.lean`: every entry parses, the tables have their
stated shapes, every vector lies in the unit ball of `ℝ^3`, the value of the vectors is the
stated rational number, and the signs attain the classical value. -/

@[expose] public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators

/-- Every entry parses, and the tables have the stated shapes. -/
theorem dataSplit_wellFormed :
    (mSplitRows.all rowWellFormed && aSplitRows.all rowWellFormed && bSplitRows.all rowWellFormed &&
      rowWellFormed sSplitRow) = true ∧
    mSplitTable.size = 141 ∧ mSplitTable.all (·.size == 321) = true ∧ aSplitTable.size = 141 ∧
    aSplitTable.all (·.size == 3) = true ∧ bSplitTable.size = 321 ∧ bSplitTable.all (·.size == 3) = true ∧
    sSplitTable.size = 141 := by
  native_decide

/-- The row vectors lie in the unit ball: their squared numerators sum to at most `10⁷²`. -/
theorem aSplit_ball : ∀ i : Fin 141, ∑ k : Fin 3, aSplitZ i k ^ 2 ≤ 10 ^ 72 := by
  native_decide

/-- The column vectors lie in the unit ball. -/
theorem bSplit_ball : ∀ j : Fin 321, ∑ k : Fin 3, bSplitZ j k ^ 2 ≤ 10 ^ 72 := by
  native_decide

/-- The exact value of the vectors, times `10⁷²`. -/
theorem objectiveSplit :
    ∑ i : Fin 141, ∑ j : Fin 321, mSplitZ i j * ∑ k : Fin 3, aSplitZ i k * bSplitZ j k = 924161982767004923304275072475569794056604412473073157292179614339537187061744866701519909 := by
  native_decide

/-- The attaining assignment consists of signs. -/
theorem sSplit_signs : ∀ i : Fin 141, sSplitZ i = 1 ∨ sSplitZ i = -1 := by
  native_decide

/-- The signs attain the classical value. -/
theorem attainedSplit : ∑ j : Fin 321, |∑ i : Fin 141, sSplitZ i * mSplitZ i j| = 641951276514383746 := by
  native_decide

end Lemmata.GrothendieckLowerBounds
