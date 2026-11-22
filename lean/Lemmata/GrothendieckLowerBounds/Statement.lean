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

/-- The value of a Bell matrix on vectors `u i, v j ∈ ℝ^d`: `∑ M_ij ⟨u_i, v_j⟩`. -/
noncomputable def vectorObj {n m d : ℕ} (M : BellMatrix n m) (u : Fin n → Fin d → ℝ)
    (v : Fin m → Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * ∑ k, u i k * v j k

/-- Unit vectors in `ℝ^d`, one for each index. -/
def UnitVectors {n d : ℕ} (u : Fin n → Fin d → ℝ) : Prop := ∀ i, ∑ k, u i k ^ 2 = 1

/-- `K_G(d) > x`: some Bell matrix with a classical upper bound `B > 0` has a value on unit
vectors in `ℝ^d` above `x B`. Since `K_G(d)` is the supremum of the ratio of the two values,
this is exactly the statement that `K_G(d) > x`. -/
def GrothendieckLowerBound (d : ℕ) (x : ℝ) : Prop :=
  ∃ (n m : ℕ) (M : BellMatrix n m) (B : ℝ), 0 < B ∧ ClassicalUpper M B ∧
    ∃ (u : Fin n → Fin d → ℝ) (v : Fin m → Fin d → ℝ), UnitVectors u ∧ UnitVectors v ∧
      x * B < vectorObj M u v

end Lemmata.GrothendieckLowerBounds
