module

public import Lemmata.OracleComplexity.Statement

@[expose] public section

/-!
# The maximal oracle (Lemma VI.2)

The maximal oracle answers the set of instances that agree with the given one near the query.
Instances that agree near the query get the same answer, and any local oracle is recovered from this
answer by evaluating it at any instance of the set.
-/

namespace Lemmata.OracleComplexity

namespace Proof

theorem maximal_oracle : MaximalOracle := by
  intro ι E α _ _ F O
  refine ⟨fun i i' x h => ?_, fun hO => ?_⟩
  · ext j
    show (∀ᶠ y in nhds x, F j y = F i y) ↔ (∀ᶠ y in nhds x, F j y = F i' y)
    constructor
    · intro hj
      exact hj.mp (h.mono fun y hy hjy => hjy.trans hy)
    · intro hj
      exact hj.mp (h.mono fun y hy hjy => hjy.trans hy.symm)
  · classical
    refine ⟨fun x A => if hA : A.Nonempty then O hA.some x else Classical.arbitrary α,
      fun i x => ?_⟩
    have hA : (maxOracle F i x).Nonempty := ⟨i, Filter.Eventually.of_forall (fun _ => rfl)⟩
    show O i x = if hA : (maxOracle F i x).Nonempty then O hA.some x else Classical.arbitrary α
    simp only [hA, ↓reduceDIte]
    exact (hO _ _ x hA.some_mem).symm

end Proof

end Lemmata.OracleComplexity
