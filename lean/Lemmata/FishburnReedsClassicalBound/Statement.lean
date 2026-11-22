module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace Lemmata.FishburnReedsClassicalBound

open scoped BigOperators

noncomputable section

/-- Larger index first and both root signs. The all-plus target is in ascending order. -/
abbrev Root (d : ℕ) := Σ i : Fin d, Fin i.val × Bool

def roots (d : ℕ) (r : Root d) (k : Fin d) : ℝ :=
  (if k = r.1 then 1 else 0) +
    (if k.val = r.2.1.val then (if r.2.2 then 1 else -1) else 0)

variable {R K : Type*} [Fintype R] [Fintype K]

def coord (V : R → K → ℝ) (a : R → ℝ) (k : K) : ℝ :=
  ∑ i, a i * V i k

def energy (V : R → K → ℝ) (a : R → ℝ) : ℝ :=
  ∑ k, (coord V a k)^2

def gramScore (V : R → K → ℝ) (a b : R → ℝ) : ℝ :=
  ∑ i, ∑ j, (a i * b j) * (∑ k, V i k * V j k)

def value (V : R → K → ℝ) (a b : R → ℝ) : ℝ :=
  3 * gramScore V a b - 4 * ∑ i, a i * b i

def mid (a b : R → ℝ) (i : R) : ℝ := (a i + b i) / 2
def halfDiff (a b : R → ℝ) (i : R) : ℝ := (a i - b i) / 2

def agreements (a b : R → ℝ) : ℝ := by
  classical
  exact ∑ i, if a i = b i then (1 : ℝ) else 0

def Signs (a : R → ℝ) : Prop := ∀ i, a i = 1 ∨ a i = -1

/-- The full, unconditional upper-bound target of the prose proof. -/
def FixedUpper (d : ℕ) : Prop :=
  ∀ a b : Root d → ℝ, Signs a → Signs b →
    value (roots d) a b ≤ 2*(d : ℝ)*((d : ℝ)-1)*(2*(d : ℝ)-3)

/-- Attainment together with a universal upper bound, avoiding a supremum convention. -/
def FixedClassicalValue (d : ℕ) : Prop :=
  IsGreatest {y : ℝ | ∃ a b : Root d → ℝ, Signs a ∧ Signs b ∧ value (roots d) a b = y}
    (2*(d : ℝ)*((d : ℝ)-1)*(2*(d : ℝ)-3))

/-- Rows of unit Euclidean length. -/
def UnitRows {n : ℕ} (X : R → Fin n → ℝ) : Prop := ∀ r, ∑ k, X r k ^ 2 = 1

/-- The value of `3 V Vᵀ - 4 I` on two lists of vectors in `ℝⁿ`, one per row. -/
def vectorValue [DecidableEq R] (V : R → K → ℝ) {n : ℕ} (X Y : R → Fin n → ℝ) : ℝ :=
  ∑ r, ∑ s, (3 * ∑ k, V r k * V s k - 4 * (if r = s then 1 else 0)) * ∑ l, X r l * Y s l

/-- The vector value at the fixed shift: at most `2N(3d-5)` for unit vectors in every
dimension, with equality in dimension `d`. -/
def FixedVectorValue (d : ℕ) : Prop :=
  (∀ (n : ℕ) (X Y : Root d → Fin n → ℝ), UnitRows X → UnitRows Y →
      |vectorValue (roots d) X Y| ≤ 2 * (d : ℝ) * ((d : ℝ) - 1) * (3 * (d : ℝ) - 5)) ∧
  ∃ X : Root d → Fin d → ℝ, UnitRows X ∧
      vectorValue (roots d) X X = 2 * (d : ℝ) * ((d : ℝ) - 1) * (3 * (d : ℝ) - 5)

/-- The fixed Fishburn–Reeds shift in order `d`: classical value `2N(2d-3)` and vector value
`2N(3d-5)`, `N = d(d-1)`; their ratio is `(3d-5)/(2d-3)`. -/
def FixedShift (d : ℕ) : Prop := FixedClassicalValue d ∧ FixedVectorValue d

end
end Lemmata.FishburnReedsClassicalBound
