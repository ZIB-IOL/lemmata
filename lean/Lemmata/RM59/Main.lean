module

public import Lemmata.RM59.Proof.UpperBound

@[expose] public section

namespace Lemmata.RM59

open scoped BigOperators

-- DOCS_BEGIN_MAIN
/-- Every Boolean function on nine variables is within distance 32 of RM(5,9). -/
theorem covering_radius_upper_bound (f : BooleanFunction 9) :
    ∃ p ∈ reedMuller 9 5, weight (f + p) ≤ 32 :=
  full_bound_thirty_two f

/-- Every odd support has an affinely independent support with the same quadratic sums. -/
theorem odd_support_simplex {m : ℕ} (S : Finset (Point m)) (hodd : Odd S.card) :
    ∃ P : Finset (Point m), AffineIndependent Field ((↑) : P → Point m) ∧
      ∀ q : ANF m, DegreeLE q 2 →
        (∑ x ∈ P, evaluate q x) = ∑ x ∈ S, evaluate q x := by
  obtain ⟨P, hind, _, hmatch, _⟩ :=
    exists_affineIndependent_matchSupportMoments_two S hodd
  exact ⟨P, hind, fun q hq => hmatch.sum_evaluate q hq⟩
-- DOCS_END_MAIN

end Lemmata.RM59
