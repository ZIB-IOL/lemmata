module

public import Mathlib

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

end
end Lemmata.FishburnReedsClassicalBound
