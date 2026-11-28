module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWCaratheodory

open Lemmata.FrankWolfe

/-- The objective `f(z) = ‖z - x⋆‖²/2` of the approximate Carathéodory problem. -/
noncomputable def lpObjective {E : Type*} [NormedAddCommGroup E] (xStar : E) (z : E) : ℝ :=
  ‖z - xStar‖ ^ 2 / 2

/-- **Lemma 3.1** (the objective). Let `2 ≤ p < ∞`, `x⋆ ∈ ℓ_p^n` and `f(z) = ‖z - x⋆‖_p²/2`. Then
`f` is differentiable and convex, satisfies the quadratic upper bound
`f(y) ≤ f(x) + f'(x)(y - x) + (p - 1)/2 ‖y - x‖_p²` (it is `(p - 1)`-smooth), has a
`(p - 1)`-Lipschitz derivative, and `‖f'(z)‖ = ‖z - x⋆‖_p`, so that `f(z) = ‖f'(z)‖²/2` and `f` is
`1`-gradient dominated. On every set `C` containing `x⋆`, `f` satisfies a `(√2, 1/2)`-Hölderian
error bound (it is `√2`-sharp). -/
def LpObjective : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ xStar : PiLp p (fun _ : Fin n => ℝ),
      Differentiable ℝ (lpObjective xStar) ∧ ConvexOn ℝ Set.univ (lpObjective xStar) ∧
      (∀ x y, lpObjective xStar y ≤ lpObjective xStar x + fderiv ℝ (lpObjective xStar) x (y - x) +
        (p.toReal - 1) / 2 * ‖y - x‖ ^ 2) ∧
      LipschitzWith (Real.toNNReal (p.toReal - 1)) (fderiv ℝ (lpObjective xStar)) ∧
      (∀ z, ‖fderiv ℝ (lpObjective xStar) z‖ = ‖z - xStar‖) ∧
      ∀ C : Set (PiLp p (fun _ : Fin n => ℝ)), xStar ∈ C →
        IsHolderErrorBound C (lpObjective xStar) (Real.sqrt 2) (1 / 2)

/-- The `j`-th column of a matrix `H`, normalized by `n^{1/p}`, as a point of `ℓ_p^n`. -/
noncomputable def hadamardVertex {n : ℕ} (p : ENNReal) (H : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    PiLp p (fun _ : Fin n => ℝ) :=
  WithLp.toLp p (fun i => H i j / (n : ℝ) ^ (1 / p.toReal))

/-- The barycenter of the normalized columns. For Sylvester's Hadamard matrix it is
`e₁/n^{1/p}`. -/
noncomputable def hadamardCenter {n : ℕ} (p : ENNReal) (H : Matrix (Fin n) (Fin n) ℝ) :
    PiLp p (fun _ : Fin n => ℝ) :=
  (1 / (n : ℝ)) • ∑ j, hadamardVertex p H j

/-- **Theorem 8.1** (a lower bound). Let `2 ≤ p < ∞` and let `H` be a Hadamard matrix of order
`n`: its entries are `±1` and its columns are orthogonal. If a point `x` of the convex hull of the
normalized columns `H_j/n^{1/p}`, `j ∈ S`, satisfies `‖x - x⋆‖_p ≤ ε` for the barycenter `x⋆` of all
normalized columns, then `|S| ≥ 1/(ε² + 1/n)`. -/
def HadamardLowerBound : Prop :=
  ∀ (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)], 2 ≤ p → p ≠ ⊤ →
    ∀ H : Matrix (Fin n) (Fin n) ℝ, (∀ i j, H i j = 1 ∨ H i j = -1) →
      (∀ j k, j ≠ k → ∑ i, H i j * H i k = 0) →
      ∀ (ε : ℝ) (S : Finset (Fin n)) (x : PiLp p (fun _ : Fin n => ℝ)),
        x ∈ convexHull ℝ (hadamardVertex p H '' ↑S) → ‖x - hadamardCenter p H‖ ≤ ε →
          1 ≤ (S.card : ℝ) * (ε ^ 2 + 1 / n)

end Lemmata.FWCaratheodory
