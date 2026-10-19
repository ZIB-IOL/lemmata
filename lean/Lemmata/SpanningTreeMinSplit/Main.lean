module

public import Lemmata.SpanningTreeMinSplit.FullSlack

public section

namespace Lemmata.SpanningTreeMinSplit

-- DOCS_BEGIN_MAIN
/-- The full standard spanning-tree slack matrix has an explicit nonnegative
factorization with n(n-1)(2n-1)/6 factors, including all nonnegativity rows. -/
theorem fullSlack_factorization (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (NonnegativeFactorization (fullSlack n) (n * (n - 1) * (2 * n - 1) / 6)) := by
  let : NeZero n := ⟨by omega⟩
  simpa only [card_cert] using
    (⟨fullFactorization (n := n)⟩ : Nonempty
      (NonnegativeFactorization (fullSlack n) (Fintype.card (Cert n))))

/-- The nonnegative-rank bound for the actual full graph slack matrix. -/
theorem fullSlack_rank_bound (n : ℕ) (hn : 3 ≤ n) :
    nonnegativeRank (fullSlack n) ≤ ((n * (n - 1) * (2 * n - 1) / 6 : ℕ) : ℕ∞) := by
  obtain ⟨F⟩ := fullSlack_factorization n hn
  exact nonnegativeRank_le F
-- DOCS_END_MAIN

/-- Nonnegativity is derived from the actual factorization, not an interface field. -/
theorem fullSlack_nonnegative (n : ℕ) (hn : 3 ≤ n) (R : Row n) (T : Tree n) :
    0 ≤ fullSlack n R T := by
  obtain ⟨F⟩ := fullSlack_factorization n hn
  exact F.nonneg R T

end Lemmata.SpanningTreeMinSplit
