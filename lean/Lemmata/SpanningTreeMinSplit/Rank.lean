module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENat.Lattice

@[expose] public section

namespace Lemmata.SpanningTreeMinSplit

open scoped BigOperators

/-- A nonnegative factorization with `k` rank-one summands. -/
structure NonnegativeFactorization {I J : Type*} (M : I → J → ℝ) (k : ℕ) where
  left : Fin k → I → ℝ
  right : Fin k → J → ℝ
  left_nonneg : ∀ l i, 0 ≤ left l i
  right_nonneg : ∀ l j, 0 ≤ right l j
  reconstruct : ∀ i j, M i j = ∑ l, left l i * right l j

/-- Minimum nonnegative factorization size, with value infinity if there is no
factorization. For the matrix in this entry a finite factorization is constructed. -/
noncomputable def nonnegativeRank {I J : Type*} (M : I → J → ℝ) : ℕ∞ :=
  sInf {r | ∃ k : ℕ, r = k ∧ Nonempty (NonnegativeFactorization M k)}

/-- An actual factorization bounds nonnegative rank. -/
theorem nonnegativeRank_le {I J : Type*} {M : I → J → ℝ} {k : ℕ}
    (F : NonnegativeFactorization M k) : nonnegativeRank M ≤ (k : ℕ∞) :=
  sInf_le ⟨k, rfl, ⟨F⟩⟩

/-- Every matrix admitting a nonnegative factorization is entrywise nonnegative. -/
theorem NonnegativeFactorization.nonneg {I J : Type*} {M : I → J → ℝ} {k : ℕ}
    (F : NonnegativeFactorization M k) (i : I) (j : J) : 0 ≤ M i j := by
  rw [F.reconstruct]
  exact Finset.sum_nonneg (fun l _ => mul_nonneg (F.left_nonneg l i) (F.right_nonneg l j))

end Lemmata.SpanningTreeMinSplit
