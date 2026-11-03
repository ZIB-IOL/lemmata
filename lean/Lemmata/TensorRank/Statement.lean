module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.Asymptotic
public import Lemmata.TensorRank.Def.Graph
public import Lemmata.TensorRank.Def.Formats
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

variable {𝕜 : Type*} [Field 𝕜]

def SquareRootBound : Prop :=
  ∀ (I : Type) [Fintype I] [Nonempty I] (V : I → Type) [∀ i, Fintype (V i)]
    (T : Tensor 𝕜 I V),
    Tensor.asymptoticRank T ≤ Real.sqrt (∏ i, (Fintype.card (V i) : ℝ))

def CubicalSquareRootBound : Prop :=
  ∀ (k n : ℕ), 0 < k → ∀ T : Tensor 𝕜 (Fin k) (fun _ => Fin n),
    Tensor.asymptoticRank T ≤ (n : ℝ) ^ ((k : ℝ) / 2)

def CompleteGraphBounds : Prop :=
  ∀ (k n : ℕ), 2 ≤ k → 1 ≤ n →
    (n : ℝ) ^ ((k * k / 4 : ℕ) : ℝ) ≤ Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k n) ∧
    Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k n) ≤ (n : ℝ) ^ ((k : ℝ) ^ 2 / 4)

def EvenCompleteGraphRank : Prop :=
  ∀ (r n : ℕ), 0 < r → 1 ≤ n →
    Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) (2 * r) n) = (n : ℝ) ^ (r ^ 2)

def EvenCubicalMaximum : Prop :=
  ∀ (r n : ℕ), 0 < r → IsGreatest (cubicalRanks (𝕜 := 𝕜) (r + r) n) ((n : ℝ) ^ r)

def EvenCubicalNonsingular : Prop :=
  ∀ (r n : ℕ), 0 < r → ∀ T : Cubical (𝕜 := 𝕜) (r + r) n, (balancedMatrix (𝕜 := 𝕜) r n T).det ≠ 0 →
      Tensor.asymptoticRank T = (n : ℝ) ^ r

end Lemmata.TensorRank
