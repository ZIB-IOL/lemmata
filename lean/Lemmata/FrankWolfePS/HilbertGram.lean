module

public import Lemmata.FrankWolfePS.HilbertPrefix
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Ring

/-! The Gram operator of the gradient construction on every finitely supported chart. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Finset Filter
open scoped BigOperators Topology

/-- The paper's weights, indexed starting at zero. -/
noncomputable def weight (i : ℕ) : ℝ := (1/2)^i / 64

theorem weight_pos (i : ℕ) : 0 < weight i := by unfold weight; positivity

theorem weight_anti : Antitone weight := by
  intro i j hij
  unfold weight
  exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij) (by norm_num)

theorem weight_small (i : ℕ) : weight i ≤ 1/64 := by simpa [weight] using weight_anti (Nat.zero_le i)

theorem weight_half {i j : ℕ} (h : i < j) : weight j ≤ weight i/2 := by
  calc
    _ ≤ weight (i+1) := weight_anti h
    _ = _ := by simp [weight, pow_succ]; ring

theorem weight_limit : Tendsto weight atTop (𝓝 0) := by
  unfold weight
  simpa only [zero_div] using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1:ℝ)/2 < 1 by norm_num)).div_const 64

theorem sum_weight_le (s : Finset ℕ) : ∑ i ∈ s, weight i ≤ 1/32 := by
  unfold weight
  simp only [div_eq_mul_inv, ← sum_mul]
  have h := summable_geometric_two.sum_le_tsum s (fun i _ => by positivity)
  rw [tsum_geometric_two] at h
  linarith

/-- A coordinate of the paper's Gram operator. -/
noncomputable def gram (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  x j - ∑' i, x i * weight (max i j)

/-- Squared energy in the Gram chart. On a finite prefix both sums are finite. -/
noncomputable def energy (x : ℕ → ℝ) : ℝ := ∑' i, x i * gram x i

theorem gram_prefix {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i = 0) (j : ℕ) :
    gram x j = x j - ∑ i ∈ range n, x i * weight (max i j) := by
  unfold gram
  rw [tsum_eq_sum (s:=range n) (fun i hi => by simp [hx i (by simpa using hi)])]

theorem gram_tail {n j : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i = 0) (hj : n ≤ j) :
    gram x j = -(∑ i ∈ range n, x i) * weight j := by
  rw [gram_prefix hx, hx j hj, tail_sum (range n) j weight x
    (fun i hi => le_trans (mem_range.mp hi).le hj)]
  ring

/-- The lower spectral bound for the actual double sum, for arbitrary signed finite charts. -/
theorem energy_lower {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i = 0) :
    (31:ℝ)/32 * (∑ i ∈ range n, (x i)^2) ≤ energy x := by
  let S := range n
  let w := fun i j => weight (max i j)
  have pair (i j : ℕ) : 2 * (x i * (x j * w i j)) ≤
      (x i)^2 * weight j + (x j)^2 * weight i := by
    have wi : w i j ≤ weight i := weight_anti (Nat.le_max_left ..)
    have wj : w i j ≤ weight j := weight_anti (Nat.le_max_right ..)
    nlinarith [mul_nonneg (weight_pos (max i j)).le (sq_nonneg (x i-x j)),
      mul_le_mul_of_nonneg_left wj (sq_nonneg (x i)), mul_le_mul_of_nonneg_left wi (sq_nonneg (x j))]
  have twice := sum_le_sum (s:=S) (fun i _ => sum_le_sum (s:=S) (fun j _ => pair i j))
  simp only [← mul_sum, sum_add_distrib, ← sum_mul] at twice
  have bound := mul_le_mul_of_nonneg_left (sum_weight_le S)
    (sum_nonneg (s:=S) (fun i _ => sq_nonneg (x i)))
  have en : energy x = (∑ i ∈ S, (x i)^2) -
      ∑ i ∈ S, x i * ∑ j ∈ S, x j * w i j := by
    unfold energy
    rw [tsum_eq_sum (s:=S) (fun i hi => by simp [hx i (by simpa [S] using hi)]), ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [gram_prefix hx]
    simp [S,w,max_comm,mul_sub,sq]
  rw [en]
  nlinarith

/-- Upper Gram bound, including signed finite coefficients. -/
theorem energy_upper {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i = 0) :
    energy x ≤ (33:ℝ)/32 * (∑ i ∈ range n, (x i)^2) := by
  let S := range n
  let w := fun i j => weight (max i j)
  have pair (i j : ℕ) : -(2 * (x i * (x j * w i j))) ≤
      (x i)^2 * weight j + (x j)^2 * weight i := by
    have wi : w i j ≤ weight i := weight_anti (Nat.le_max_left ..)
    have wj : w i j ≤ weight j := weight_anti (Nat.le_max_right ..)
    nlinarith [mul_nonneg (weight_pos (max i j)).le (sq_nonneg (x i+x j)),
      mul_le_mul_of_nonneg_left wj (sq_nonneg (x i)), mul_le_mul_of_nonneg_left wi (sq_nonneg (x j))]
  have twice := sum_le_sum (s:=S) (fun i _ => sum_le_sum (s:=S) (fun j _ => pair i j))
  simp only [sum_neg_distrib, ← mul_sum, sum_add_distrib, ← sum_mul] at twice
  have bound := mul_le_mul_of_nonneg_left (sum_weight_le S)
    (sum_nonneg (s:=S) (fun i _ => sq_nonneg (x i)))
  have en : energy x = (∑ i ∈ S, (x i)^2) -
      ∑ i ∈ S, x i * ∑ j ∈ S, x j * w i j := by
    unfold energy
    rw [tsum_eq_sum (s:=S) (fun i hi => by simp [hx i (by simpa [S] using hi)]), ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [gram_prefix hx]
    simp [S,w,max_comm,mul_sub,sq]
  rw [en]
  nlinarith

end Lemmata.FrankWolfePS.Hilbert
