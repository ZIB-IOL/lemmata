module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank.Profile

theorem forward_difference_le {g : ℕ → ℝ}
    (hconc : ∀ b, 1 ≤ b → g b + g (b + 2) ≤ 2 * g (b + 1))
    (b : ℕ) (hb : 1 ≤ b) (l : ℕ) :
    g (b + l + 1) - g (b + l) ≤ g (b + 1) - g b := by
  induction l with
  | zero => simp
  | succ l ih =>
      have h := hconc (b + l) (by omega)
      rw [show b + l + 2 = b + (l + 1) + 1 by omega,
        show b + l + 1 = b + (l + 1) by omega] at h
      rw [show b + l + 1 = b + (l + 1) by omega] at ih
      nlinarith

theorem secant_le {g : ℕ → ℝ}
    (hconc : ∀ b, 1 ≤ b → g b + g (b + 2) ≤ 2 * g (b + 1))
    (b : ℕ) (hb : 1 ≤ b) (l : ℕ) :
    g (b + l) ≤ g b + (l : ℝ) * (g (b + 1) - g b) := by
  induction l with
  | zero => simp
  | succ l ih =>
      have h := forward_difference_le hconc b hb l
      rw [show b + l + 1 = b + (l + 1) by omega] at h
      push_cast
      nlinarith

theorem step_of_tripling {g : ℕ → ℝ}
    (hconc : ∀ b, 1 ≤ b → g b + g (b + 2) ≤ 2 * g (b + 1))
    (b s : ℕ) (hb : 1 ≤ b) (htrip : 3 * g b ≤ g (3 * b + s)) :
    (1 + 2 / (2 * b + s : ℕ)) * g b ≤ g (b + 1) := by
  have hl : (0 : ℝ) < (2 * b + s : ℕ) := by exact_mod_cast (by omega : 0 < 2 * b + s)
  have h := secant_le hconc b hb (2 * b + s)
  rw [show b + (2 * b + s) = 3 * b + s by omega] at h
  have hh : 2 * g b / ((2 * b + s : ℕ) : ℝ) ≤ g (b + 1) - g b := by
    apply (div_le_iff₀ hl).2
    nlinarith
  have he : (1 + 2 / ((2 * b + s : ℕ) : ℝ)) * g b =
      g b + 2 * g b / ((2 * b + s : ℕ) : ℝ) := by
    ring
  rw [he]
  linarith

theorem step_of_displacement_bound {g : ℕ → ℝ}
    (hconc : ∀ b, 1 ≤ b → g b + g (b + 2) ≤ 2 * g (b + 1))
    (b s K : ℕ) (hb : 1 ≤ b) (hg : 0 ≤ g b)
    (htrip : 3 * g b ≤ g (3 * b + s)) (hK : 2 * b + s ≤ K) :
    (1 + 2 / (K : ℝ)) * g b ≤ g (b + 1) := by
  apply le_trans _ (step_of_tripling hconc b s hb htrip)
  apply mul_le_mul_of_nonneg_right _ hg
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by norm_num)
    (by exact_mod_cast (by omega : 0 < 2 * b + s)) (by exact_mod_cast hK)

end Lemmata.TensorRank.Profile
