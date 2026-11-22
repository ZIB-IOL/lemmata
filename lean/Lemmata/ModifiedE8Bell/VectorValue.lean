module

public import Lemmata.ModifiedE8Bell.Envelope
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public meta import Lemmata.ModifiedE8Bell.Statement

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators Matrix

/-- Real coefficient matrix, with the same normalization as the classical value. -/
noncomputable def realMatrix : Matrix Setting Setting ℝ := fun i j => (fourMatrix i j : ℝ) / 4

/-- The value on arbitrary real vector outputs. -/
noncomputable def vectorBell {n : ℕ} (X Y : Setting → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, realMatrix i j * ∑ k, X i k * Y j k

def UnitRows {n : ℕ} (X : Setting → Fin n → ℝ) : Prop :=
  ∀ i, ∑ k, X i k ^ 2 = 1

/-- The canonical normalized E₈ root measurements, in dimension eight. -/
noncomputable def rootMeasurements (i : Setting) (k : Coordinate) : ℝ :=
  (root i k : ℝ) / Real.sqrt 8

/-- Exact vector value, in every real dimension, with attainment in dimension eight. -/
def ExactVectorValue : Prop :=
  (∀ (n : ℕ) (X Y : Setting → Fin n → ℝ), UnitRows X → UnitRows Y →
    |vectorBell X Y| ≤ 9240) ∧
  UnitRows rootMeasurements ∧ vectorBell rootMeasurements rootMeasurements = 9240

end Lemmata.ModifiedE8Bell
