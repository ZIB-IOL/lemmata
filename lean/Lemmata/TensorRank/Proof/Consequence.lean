module

public import Lemmata.TensorRank.Statement

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.TensorRank

theorem cubical_of_squareRoot (h : SquareRootBound) : CubicalSquareRootBound := by
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
