module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

public section

namespace Lemmata.FishburnReedsClassicalBound

noncomputable section

def rowNumber (x : ℝ) : ℝ := x * (x - 1)
def q6 (x : ℝ) : ℝ := 6 * rowNumber x * (x - 2)
def c6 (x k : ℝ) : ℝ := 4 * rowNumber x * (x - 2) + 12 * k
def r4 (x : ℝ) : ℝ := (3*x - 5) / (2*x - 3)
def r6 (x k : ℝ) : ℝ := q6 x / c6 x k

private theorem c6_pos {x k : ℝ} (hx : 3 ≤ x) (hk : 0 ≤ k) : 0 < c6 x k := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  unfold c6 rowNumber
  positivity

private theorem shift_comparison_real {x k : ℝ}
    (hx : 8 ≤ x) (hk : 0 ≤ k) (h3 : 3*k ≤ x) : r4 x < r6 x k := by
  have hs : 0 < (x-1)*(x-2) - 2*(3*x-5) := by
    nlinarith [sq_nonneg (x-8)]
  have hp := mul_pos (show 0 < x by linarith) hs
  have hm := mul_le_mul_of_nonneg_right h3 (show 0 ≤ 2*(3*x-5) by linarith)
  unfold r4 r6
  apply (div_lt_div_iff₀ (show 0 < 2*x-3 by linarith) (c6_pos (by linarith : 3 ≤ x) hk)).2
  unfold q6 c6 rowNumber
  nlinarith only [hp, hm]

/-- Comparison of the two explicit numeric formulas, including the exceptional residue at seven. -/
theorem shift_comparison (d : ℕ) (hd : 7 ≤ d) : r4 d < r6 d ((d / 3 : ℕ) : ℝ) := by
  by_cases he : d = 7
  · subst d
    norm_num [r4, r6, q6, c6, rowNumber]
  · have h8 : 8 ≤ d := by omega
    have h3 : 3 * (d / 3) ≤ d := by omega
    apply shift_comparison_real
    · exact_mod_cast h8
    · positivity
    · exact_mod_cast h3

end
end Lemmata.FishburnReedsClassicalBound
