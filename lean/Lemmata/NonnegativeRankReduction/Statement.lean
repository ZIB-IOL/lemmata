module

public import Lemmata.SpanningTreeMinSplit.Main

@[expose] public section

namespace Lemmata.NonnegativeRankReduction

open Lemmata.SpanningTreeMinSplit

variable {I J I' J' : Type*}

/-- The row and column maps are independent. The multiplier and the additive
remainder may depend on both indices. -/
def ReductionIdentity (S A B : I → J → ℝ) (T : I' → J' → ℝ)
    (f : I → I') (g : J → J') : Prop :=
  ∀ i j, S i j = A i j * T (f i) (g j) + B i j

/-- A reduction transforms factorizations of the multiplier, target, and
remainder into a source factorization with the displayed number of terms.
This statement makes no assumption about the ranks of particular matrices. -/
def FactorizationReduction (S A B : I → J → ℝ) (T : I' → J' → ℝ)
    (_f : I → I') (_g : J → J') : Prop :=
  ∀ a k b : ℕ, NonnegativeFactorization A a →
    NonnegativeFactorization T k → NonnegativeFactorization B b →
      Nonempty (NonnegativeFactorization S (a * k + b))

/-- A lower bound is stated for every factorization, without postulating an
axiom or choosing a particular optimal factorization. -/
def FactorizationLowerBound (M : I → J → ℝ) (L : ℕ) : Prop :=
  ∀ k : ℕ, NonnegativeFactorization M k → L ≤ k

end Lemmata.NonnegativeRankReduction
