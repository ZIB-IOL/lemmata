module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Statement

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

variable {𝕜 : Type*} [Field 𝕜]

theorem cubical_of_squareRoot (h : SquareRootBound (𝕜 := 𝕜)) : CubicalSquareRootBound (𝕜 := 𝕜) := by
  intro k n hk T
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  calc
    Tensor.asymptoticRank T ≤ Real.sqrt (∏ _ : Fin k, (Fintype.card (Fin n) : ℝ)) :=
      h (Fin k) (fun _ => Fin n) T
    _ = Real.sqrt ((n : ℝ) ^ k) := by simp
    _ = (n : ℝ) ^ ((k : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (Nat.cast_nonneg n), mul_one_div]

end Lemmata.TensorRank
