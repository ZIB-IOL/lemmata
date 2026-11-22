module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators

/-- A finite real matrix; no topology or matrix API is needed. -/
abbrev BellMatrix (n m : ℕ) := Fin n → Fin m → ℝ

/-- The Alice assignments are exactly real vectors with coordinates in {-1,1}. -/
def IsSign {n : ℕ} (a : Fin n → ℝ) : Prop := ∀ i, |a i| = 1

/-- Bob's signs have already been maximized out. -/
noncomputable def score {n m : ℕ} (M : BellMatrix n m) (a : Fin n → ℝ) : ℝ :=
  ∑ j, |∑ i, a i * M i j|

/-- Entrywise absolute sum, not an induced matrix norm. -/
noncomputable def entryNorm {n m : ℕ} (M : BellMatrix n m) : ℝ :=
  ∑ j, ∑ i, |M i j|

/-- A classical upper bound, stated pointwise to avoid an unnecessary maximum. -/
def ClassicalUpper {n m : ℕ} (M : BellMatrix n m) (B : ℝ) : Prop :=
  ∀ a, IsSign a → score M a ≤ B

/-- Every strategy above T has a retained representative preserving its Y score.
The condition explicitly concerns Y, not only the baseline M. -/
def NearCoverage {n m : ℕ} (M Y : BellMatrix n m) (T : ℝ)
    (S : Finset (Fin n → ℝ)) : Prop :=
  ∀ a, IsSign a → T < score M a → ∃ s ∈ S, IsSign s ∧ score Y a = score Y s

end Lemmata.GrothendieckLowerBounds
