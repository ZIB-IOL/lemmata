module

public import Lemmata.ModifiedE8Bell.Compute.Raw
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Matrix.Defs

/-! # The three statements: classical value, vector value, local visibility

This module contains only definitions and the three claims, as `Prop`s; the proofs
import it. -/

@[expose] public section

namespace Lemmata.ModifiedE8Bell

open scoped BigOperators

abbrev Setting := Fin 120
abbrev Coordinate := Fin 8
abbrev Signing := Setting → Bool
abbrev IntVector := Coordinate → ℤ

/-- `true` denotes the output +1; `false` denotes -1. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Doubled canonical E₈ roots: the 56 integral lines followed by the
64 even-parity half-root lines. The order is specified in the entry. -/
def root (i : Setting) (j : Coordinate) : ℤ := (rootRows[i.val]?.getD #[])[j.val]?.getD 0

/-- Four times the integer Bell matrix `3 V Vᵀ - 13 I`, where `V = root / 2`. -/
def fourMatrix (i j : Setting) : ℤ :=
  3 * (∑ k, root i k * root j k) - if i = j then 52 else 0

/-- Four times the value on a deterministic pair of output lists. -/
def fourBell (a b : Signing) : ℤ :=
  ∑ i, ∑ j, sign (a i) * sign (b j) * fourMatrix i j

/-- The Bell value, with its original normalization. -/
def bell (a b : Signing) : ℚ := (fourBell a b : ℚ) / 4

/-- The classical bound is 6104 and is attained by deterministic outputs. -/
def ExactClassicalValue : Prop :=
  (∀ a b : Signing, |bell a b| ≤ 6104) ∧
  ∃ a b : Signing, bell a b = 6104

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

abbrev Correlation := Setting → Setting → ℝ

/-- A deterministic bipartite correlation matrix. -/
def deterministic (a b : Signing) : Correlation := fun i j => (sign (a i) : ℝ) * (sign (b j) : ℝ)

/-- Membership in the full bipartite local correlation polytope. -/
def IsLocal (M : Correlation) : Prop :=
  M ∈ convexHull ℝ (Set.range fun ab : Signing × Signing => deterministic ab.1 ab.2)

/-- Correlations of the 120 normalized E₈ root directions. -/
noncomputable def rootCorrelation : Correlation := fun i j =>
  ((∑ k, root i k * root j k : ℤ) : ℝ) / 8

/-- The endpoint is local, and no larger visibility is local. -/
def ExactVisibility : Prop :=
  IsLocal ((109/165 : ℝ) • rootCorrelation) ∧
  ∀ v : ℝ, IsLocal (v • rootCorrelation) → v ≤ 109/165

end Lemmata.ModifiedE8Bell
