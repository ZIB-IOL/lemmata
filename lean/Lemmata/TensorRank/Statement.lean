module

public import Lemmata.TensorRank.Def.Asymptotic
public import Lemmata.TensorRank.Def.Graph
public import Lemmata.TensorRank.Def.Formats
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

def SquareRootBound : Prop :=
  ∀ (I : Type) [Fintype I] [Nonempty I] (V : I → Type) [∀ i, Fintype (V i)]
    (T : Tensor ℂ I V),
    Tensor.asymptoticRank T ≤ Real.sqrt (∏ i, (Fintype.card (V i) : ℝ))

def CubicalSquareRootBound : Prop :=
  ∀ (k n : ℕ), 0 < k → ∀ T : Tensor ℂ (Fin k) (fun _ => Fin n),
    Tensor.asymptoticRank T ≤ (n : ℝ) ^ ((k : ℝ) / 2)

def CompleteGraphBounds : Prop :=
  ∀ (k n : ℕ), 2 ≤ k → 1 ≤ n →
    (n : ℝ) ^ ((k * k / 4 : ℕ) : ℝ) ≤ Tensor.asymptoticRank (completeGraph k n) ∧
    Tensor.asymptoticRank (completeGraph k n) ≤ (n : ℝ) ^ ((k : ℝ) ^ 2 / 4)

def EvenCompleteGraphRank : Prop :=
  ∀ (r n : ℕ), 0 < r → 1 ≤ n →
    Tensor.asymptoticRank (completeGraph (2 * r) n) = (n : ℝ) ^ (r ^ 2)

def EvenCubicalMaximum : Prop :=
  ∀ (r n : ℕ), 0 < r → IsGreatest (cubicalRanks (r + r) n) ((n : ℝ) ^ r)

def EvenCubicalNonsingular : Prop :=
  ∀ (r n : ℕ), 0 < r → ∀ T : Cubical (r + r) n, (balancedMatrix r n T).det ≠ 0 →
      Tensor.asymptoticRank T = (n : ℝ) ^ r

end Lemmata.TensorRank
