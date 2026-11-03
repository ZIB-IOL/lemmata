module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.GraphExponent
public import Lemmata.TensorRank.Proof.LogarithmicGrowth
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.CyclicExponent

variable {𝕜 : Type*} [Field 𝕜]

/-- The graph dimension consumed while shortening lengths from `n` to `1`. -/
def inputProduct (k n : ℕ) : ℕ :=
  ∏ b ∈ Finset.Ico 1 n, (k * b) ^ 4

/-- The graph dimension returned while shortening lengths from `n` to `1`. -/
def outputProduct (k n : ℕ) : ℕ :=
  ∏ b ∈ Finset.Ico 1 n, (k * b + 2) ^ 4

noncomputable def logGain (k n : ℕ) : ℝ :=
  ∑ b ∈ Finset.Ico 1 n, Real.log (1 + 2 / ((k * b : ℕ) : ℝ))

@[simp] theorem inputProduct_one (k : ℕ) : inputProduct k 1 = 1 := by
  simp [inputProduct]

@[simp] theorem outputProduct_one (k : ℕ) : outputProduct k 1 = 1 := by
  simp [outputProduct]

@[simp] theorem logGain_one (k : ℕ) : logGain k 1 = 0 := by
  simp [logGain]

theorem inputProduct_succ (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    inputProduct k (n + 1) = inputProduct k n * (k * n) ^ 4 := by
  exact Finset.prod_Ico_succ_top hn _

theorem outputProduct_succ (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    outputProduct k (n + 1) = outputProduct k n * (k * n + 2) ^ 4 := by
  exact Finset.prod_Ico_succ_top hn _

theorem logGain_succ (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    logGain k (n + 1) = logGain k n + Real.log (1 + 2 / ((k * n : ℕ) : ℝ)) := by
  exact Finset.sum_Ico_succ_top hn _

theorem inputProduct_pos {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    0 < inputProduct k n := by
  apply Finset.prod_pos
  intro b hb
  have hb1 : 1 ≤ b := (Finset.mem_Ico.mp hb).1
  exact pow_pos (Nat.mul_pos (by omega) (by omega)) 4

theorem outputProduct_pos (k n : ℕ) : 0 < outputProduct k n := by
  apply Finset.prod_pos
  intro b _
  exact pow_pos (by omega) 4

/-- Concavity supplies a telescoping lower bound for one cyclic round. -/
theorem log_gain_step {k : ℕ} (hk : 2 ≤ k) (b : ℕ) (hb : 1 ≤ b) :
    (2 / (k : ℝ)) * (Real.log (b + 1 : ℕ) - Real.log b) ≤
      Real.log (1 + 2 / ((k * b : ℕ) : ℝ)) := by
  cases k with
  | zero => omega
  | succ m =>
      have hm : 1 ≤ m := by omega
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have h := LogarithmicGrowth.diagonal_log_gain hm b hb
      apply (mul_le_mul_iff_right₀ hm0).mp
      convert h using 1 <;> push_cast <;> ring

theorem logGain_ge {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    (2 / (k : ℝ)) * Real.log n ≤ logGain k n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [logGain_succ k hn]
      have h := log_gain_step hk n hn
      nlinarith

private theorem log_factor {s : ℕ} (hs : 0 < s) :
    Real.log (((s + 2) ^ 4 : ℕ) : ℝ) - Real.log ((s ^ 4 : ℕ) : ℝ) =
      4 * Real.log (1 + 2 / (s : ℝ)) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have he : 1 + 2 / (s : ℝ) = ((s : ℝ) + 2) / s := by
    field_simp
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow, he,
    Real.log_div (by positivity) hs0.ne']
  push_cast
  ring

/-- The logarithm of the returned-to-consumed dimension ratio is the round gain. -/
theorem log_product_gain {k : ℕ} (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    Real.log (outputProduct k n : ℝ) - Real.log (inputProduct k n : ℝ) =
      4 * logGain k n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hkn : 0 < k * n := Nat.mul_pos (by omega) (by omega)
      have hU : (inputProduct k n : ℝ) ≠ 0 := by
        exact_mod_cast (inputProduct_pos hk n).ne'
      have hV : (outputProduct k n : ℝ) ≠ 0 := by
        exact_mod_cast (outputProduct_pos k n).ne'
      have hu : (((k * n) ^ 4 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (pow_pos hkn 4).ne'
      have hv : (((k * n + 2) ^ 4 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show 0 < (k * n + 2) ^ 4 by positivity).ne'
      rw [outputProduct_succ k hn, inputProduct_succ k hn, logGain_succ k hn,
        Nat.cast_mul, Nat.cast_mul, Real.log_mul hV hv, Real.log_mul hU hu]
      have hf := log_factor hkn
      linarith

/-- The analytic endpoint uses only the accumulated logarithmic resource inequality. -/
theorem exponent_le_quarter_square_of_log_bounds {k : ℕ} (hk : 2 ≤ k)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hbound : ∀ n : ℕ, 2 ≤ n →
      γ * (4 * logGain k n) ≤
        2 * (k : ℝ) * Real.log ((1 + (k - 1) * (n - 1) : ℕ) : ℝ)) :
    γ ≤ (k : ℝ) ^ 2 / 4 := by
  by_contra h
  have hlt : (k : ℝ) ^ 2 / 4 < γ := lt_of_not_ge h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hgap : 2 * (k : ℝ) < 8 * γ / k := by
    apply (lt_div_iff₀ hk0).mpr
    nlinarith
  obtain ⟨n, hn, hstrict⟩ := LogarithmicGrowth.exists_log_gap (k - 1)
    (8 * γ / k) (2 * (k : ℝ)) 0 (by positivity) hgap
  have hgain := logGain_ge hk n (by omega)
  have hmul := mul_le_mul_of_nonneg_left hgain (show 0 ≤ 4 * γ by positivity)
  have hupper : (8 * γ / k) * Real.log n ≤
      2 * (k : ℝ) * Real.log ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) := by
    calc
      _ = (4 * γ) * ((2 / (k : ℝ)) * Real.log n) := by ring
      _ ≤ (4 * γ) * logGain k n := hmul
      _ = γ * (4 * logGain k n) := by ring
      _ ≤ _ := hbound n hn
  linarith

/-- Taking logarithms of the finite endpoint comparison yields the limiting exponent. -/
theorem exponent_le_quarter_square_of_power_comparisons {k : ℕ} (hk : 2 ≤ k)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hcomp : ∀ n : ℕ, 2 ≤ n →
      (outputProduct k n : ℝ) ^ γ ≤
        ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) ^ (2 * k) *
          (inputProduct k n : ℝ) ^ γ) :
    γ ≤ (k : ℝ) ^ 2 / 4 := by
  apply exponent_le_quarter_square_of_log_bounds hk hγ
  intro n hn
  have hU : (0 : ℝ) < inputProduct k n := by
    exact_mod_cast inputProduct_pos (by omega : 1 ≤ k) n
  have hV : (0 : ℝ) < outputProduct k n := by
    exact_mod_cast outputProduct_pos k n
  have hD : (0 : ℝ) < ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hV γ) (hcomp n hn)
  rw [Real.log_mul (pow_pos hD (2 * k)).ne' (Real.rpow_pos_of_pos hU γ).ne',
    Real.log_pow, Real.log_rpow hV, Real.log_rpow hU] at hlog
  have hg := log_product_gain (by omega : 1 ≤ k) n (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlog
  calc
    γ * (4 * logGain k n) =
        γ * (Real.log (outputProduct k n : ℝ) - Real.log (inputProduct k n : ℝ)) := by
      rw [hg]
    _ ≤ _ := by nlinarith

private theorem graph_rank_formula {k d : ℕ} (hd : 1 ≤ d) :
    Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k d) =
      (d : ℝ) ^ graphExponent (𝕜 := 𝕜) k := by
  by_cases h : d = 1
  · subst d
    simp [asymptoticRank_completeGraph_one]
  · exact asymptoticRank_completeGraph (by omega)

/-- Cyclic rounds need only an upper bound on the initial polynomial resource. -/
theorem graphExponent_le_quarter_square_of_comparisons {k : ℕ} (hk : 2 ≤ k)
    (hcomp : ∀ n : ℕ, 2 ≤ n →
      Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k (outputProduct k n)) ≤
        ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) ^ (2 * k) *
          Tensor.asymptoticRank (completeGraph (𝕜 := 𝕜) k (inputProduct k n))) :
    graphExponent (𝕜 := 𝕜) k ≤ (k : ℝ) ^ 2 / 4 := by
  apply exponent_le_quarter_square_of_power_comparisons hk (graphExponent_nonneg k)
  intro n hn
  have h := hcomp n hn
  rw [graph_rank_formula (by have := outputProduct_pos k n; omega),
    graph_rank_formula (by have := inputProduct_pos (by omega : 1 ≤ k) n; omega)] at h
  exact h

end Lemmata.TensorRank.CyclicExponent
