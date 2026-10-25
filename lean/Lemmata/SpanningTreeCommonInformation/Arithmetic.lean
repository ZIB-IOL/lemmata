module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.SpanningTreeCommonInformation

/-- An elementary power bound; no tree-counting theorem is involved. -/
theorem adjacent_product_le_two_pow (n : ℕ) (hn : 3 ≤ n) :
    n * (n - 1) ≤ 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h : ∀ m : ℕ, (m + 3) * (m + 2) ≤ 2 ^ (m + 3) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hp : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 3) := by
        rw [show m + 1 + 3 = (m + 3) + 1 by omega, pow_succ]
        omega
      rw [hp]
      nlinarith
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h m

/-- The same estimate with real-valued cardinalities. -/
theorem adjacent_product_le_two_pow_real (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) * ((n : ℝ) - 1) ≤ (2 : ℝ) ^ n := by
  have h : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast adjacent_product_le_two_pow n hn
  simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] using h

private theorem power_split_three (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ n = 8 * (2 : ℝ) ^ (n - 3) := by
  conv_lhs => rw [show n = (n - 3) + 3 by omega]
  rw [pow_add]
  norm_num
  ring

private theorem power_split_two (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ (n - 2) = 2 * (2 : ℝ) ^ (n - 3) := by
  rw [show n - 2 = (n - 3) + 1 by omega, pow_succ]
  ring

private theorem count_ceiling_large (n : ℕ) (hn : 6 ≤ n) {r d : ℝ}
    (hr : r ≤ 12 * (2 : ℝ) ^ (n - 3))
    (hd : (n : ℝ) * (2 : ℝ) ^ (n - 3) ≤ d) :
    ((n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6) * r ≤
      4 * (n : ℝ) ^ 2 * d := by
  have hN : (6 : ℝ) ≤ n := by exact_mod_cast hn
  let k : ℝ := (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6
  let p : ℝ := (2 : ℝ) ^ (n - 3)
  have hp : 0 ≤ p := by positivity
  have hk0 : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
      (by linarith)) (by norm_num)
  have hk : 3 * k ≤ (n : ℝ) ^ 3 := by
    dsimp [k]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
      (show (0 : ℝ) ≤ 3 * (n : ℝ) - 1 by linarith)]
  change k * r ≤ 4 * (n : ℝ) ^ 2 * d
  calc
    k * r ≤ k * (12 * p) := mul_le_mul_of_nonneg_left hr hk0
    _ = (3 * k) * (4 * p) := by ring
    _ ≤ (n : ℝ) ^ 3 * (4 * p) := mul_le_mul_of_nonneg_right hk (by positivity)
    _ = 4 * (n : ℝ) ^ 2 * ((n : ℝ) * p) := by ring
    _ ≤ 4 * (n : ℝ) ^ 2 * d := mul_le_mul_of_nonneg_left hd (by positivity)

/-- Constant-four entropy-ceiling arithmetic for the full canonical rows. -/
theorem full_count_ceiling (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6) *
      ((2 : ℝ) ^ n - (n : ℝ) - 2 + (n : ℝ) * ((n : ℝ) - 1) / 2) ≤
    4 * (n : ℝ) ^ 2 * (((n : ℝ) - 3) * (2 : ℝ) ^ (n - 2) + (n : ℝ)) := by
  by_cases h6 : 6 ≤ n
  · have hN : (6 : ℝ) ≤ n := by exact_mod_cast h6
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (n - 3) := by positivity
    apply count_ceiling_large n h6
    · have he := adjacent_product_le_two_pow_real n hn
      rw [power_split_three n hn] at he ⊢
      nlinarith
    · rw [power_split_two n hn]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 6 by linarith) hp]
  · have : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num

/-- Constant-four arithmetic also holds when only subtour rows are present. -/
theorem subtour_count_ceiling (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6) *
      ((2 : ℝ) ^ n - (n : ℝ) - 2) ≤
    4 * (n : ℝ) ^ 2 * (((n : ℝ) - 3) * (2 : ℝ) ^ (n - 2) + 1) := by
  by_cases h6 : 6 ≤ n
  · have hN : (6 : ℝ) ≤ n := by exact_mod_cast h6
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (n - 3) := by positivity
    apply count_ceiling_large n h6
    · rw [power_split_three n hn]
      nlinarith
    · rw [power_split_two n hn]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 6 by linarith) hp]
  · have : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num

end Lemmata.SpanningTreeCommonInformation
