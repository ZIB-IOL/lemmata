module

public import Lemmata.SpanningTreeMinSplit.Main
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

@[expose] public section

namespace Lemmata.LPHardnessInP.Formulation

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit

/-- An affine LP with a common realization of the solutions and explicit
nonnegative certificates for the objective bounds.

The feasible region is given by the `m` inequalities
`0 ≤ constraintSlack l z`. The equations defining an affine hull may be
eliminated before choosing the vector space `V`. The affine objective maps
agree with `value` at every realized solution.

`certificate` is data, not a theorem that such certificates always exist.
It is the affine Farkas identity needed for the lower-bound reduction. -/
structure CertifiedLP {I J V : Type*} [AddCommGroup V] [Module ℝ V]
    (value : I → J → ℝ) (bound : I → ℝ) (m : ℕ) where
  constraintSlack : Fin m → V →ᵃ[ℝ] ℝ
  realization : J → V
  feasible : ∀ l j, 0 ≤ constraintSlack l (realization j)
  objective : I → V →ᵃ[ℝ] ℝ
  realizes : ∀ i j, objective i (realization j) = value i j
  multiplier : Fin m → I → ℝ
  multiplier_nonneg : ∀ l i, 0 ≤ multiplier l i
  offset : I → ℝ
  offset_nonneg : ∀ i, 0 ≤ offset i
  certificate : ∀ i z, objective i z - bound i =
    (∑ l, multiplier l i * constraintSlack l z) + offset i

/-- The number of factors needed for the slack matrix of a certified LP. -/
def CertifiedSlackFactorization : Prop :=
  ∀ {I J V : Type} [AddCommGroup V] [Module ℝ V]
    {value : I → J → ℝ} {bound : I → ℝ} {m : ℕ},
    CertifiedLP (V := V) value bound m →
      Nonempty (NonnegativeFactorization (fun i j => value i j - bound i) (m + 1))

end Lemmata.LPHardnessInP.Formulation
