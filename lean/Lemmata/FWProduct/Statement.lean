module

public import Lemmata.FrankWolfe.Statement
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Statements

-- DOCS_BEGIN_STATEMENT
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe

universe u

/-- The objective `f(x) = (1/(2k)) ∑_{i < j} ‖x^i - x^j‖²` of the approximate feasibility problem
for an intersection of `k` sets, on the Euclidean product of `k` copies of `E`. -/
noncomputable def feasibilityObjective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (x : PiLp 2 (fun _ : Fin k => E)) : ℝ :=
  1 / (2 * k) * ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖ ^ 2

/-- **Proposition 5.1** (convexity, smoothness and PL). On the Euclidean product of `k` copies of a
real inner product space, the objective `f(x) = (1/(2k)) ∑_{i < j} ‖x^i - x^j‖²` is differentiable
and convex, satisfies the quadratic upper bound with constant `1` (it is `1`-smooth), has a
`1`-Lipschitz derivative, and `‖f'(x)‖² = 2 f(x)`; since `f ≥ 0`, it is `1`-PL:
`‖f'(x)‖²/2 ≥ f(x) - f(y)` for all `x, y`. -/
def FeasibilityObjective : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ),
    Differentiable ℝ (feasibilityObjective (E := E) k) ∧
      ConvexOn ℝ Set.univ (feasibilityObjective (E := E) k) ∧
      (∀ x y, feasibilityObjective k y ≤ feasibilityObjective k x +
        fderiv ℝ (feasibilityObjective (E := E) k) x (y - x) + 1 / 2 * ‖y - x‖ ^ 2) ∧
      LipschitzWith 1 (fderiv ℝ (feasibilityObjective (E := E) k)) ∧
      ∀ x, ‖fderiv ℝ (feasibilityObjective (E := E) k) x‖ ^ 2 = 2 * feasibilityObjective k x

/-- **Lemma A.2** (preparatory bounds). For `a, b > 0`,
`min {a, b}/√2 ≤ √(a²b²/(a² + b²)) < min {a, b}`, and `√(a²b²/(a² + b²))` is nondecreasing in
`a` (and, by symmetry, in `b`). -/
def PreparatoryBounds : Prop :=
  (∀ a b : ℝ, 0 < a → 0 < b →
    min a b / Real.sqrt 2 ≤ Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) ∧
      Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) < min a b) ∧
  ∀ a a' b : ℝ, 0 < a → a ≤ a' → 0 < b →
    Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) ≤ Real.sqrt (a' ^ 2 * b ^ 2 / (a' ^ 2 + b ^ 2))

end Lemmata.FWProduct
