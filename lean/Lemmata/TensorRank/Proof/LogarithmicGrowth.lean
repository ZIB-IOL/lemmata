module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.LogarithmicGrowth

variable {m : ℕ}

theorem diagonal_factor (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ (2 * (m : ℝ) / (m + 1)) ≤
      (1 + 2 / (((m + 1) * n : ℕ) : ℝ)) ^ m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk : (1 : ℝ) ≤ ((m : ℝ) + 1) / 2 := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h := one_add_mul_self_le_rpow_one_add
    (s := 2 / (((m : ℝ) + 1) * n)) (by
      have hs : (0 : ℝ) ≤ 2 / (((m : ℝ) + 1) * n) := by positivity
      linarith) hk
  have he : 1 + ((m : ℝ) + 1) / 2 * (2 / (((m : ℝ) + 1) * n)) = 1 + 1 / n := by
    field_simp
  rw [he] at h
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + 1 / (n : ℝ)) h
    (show 0 ≤ 2 * (m : ℝ) / (m + 1) by positivity)
  rw [← Real.rpow_mul (by positivity)] at hh
  have hp : (((m : ℝ) + 1) / 2) * (2 * m / (m + 1)) = m := by field_simp
  rw [hp, Real.rpow_natCast] at hh
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hh

theorem diagonal_log_gain (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    (2 * (m : ℝ) / (m + 1)) * (Real.log (n + 1 : ℕ) - Real.log n) ≤
      m * Real.log (1 + 2 / (((m + 1) * n : ℕ) : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := Real.log_le_log
    (Real.rpow_pos_of_pos (by positivity : 0 < 1 + 1 / (n : ℝ)) _)
    (diagonal_factor hm n hn)
  rw [Real.log_rpow (by positivity), Real.log_pow] at h
  have he : 1 + 1 / (n : ℝ) = ((n + 1 : ℕ) : ℝ) / n := by
    push_cast
    field_simp
  rw [he, Real.log_div (by positivity) hn0.ne'] at h
  exact h

theorem exists_log_gap (m : ℕ) (α β C : ℝ) (hβ : 0 ≤ β) (hαβ : β < α) :
    ∃ n : ℕ, 2 ≤ n ∧
      β * Real.log ((1 + m * (n - 1) : ℕ) : ℝ) + C < α * Real.log n := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let A := (α - β) * Real.log (2 : ℝ)
  have hA : 0 < A := mul_pos (sub_pos.mpr hαβ) hlog
  obtain ⟨q, hq⟩ := exists_nat_gt ((C + β * Real.log ((m + 1 : ℕ) : ℝ)) / A)
  let n := 2 ^ (q + 1)
  have hn : 2 ≤ n := by
    exact (show 2 ^ 1 ≤ 2 ^ (q + 1) from
      Nat.pow_le_pow_right (by decide) (by omega))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdegree : 1 + m * (n - 1) ≤ (m + 1) * n := by
    have hs := Nat.mul_le_mul_left m (Nat.sub_le n 1)
    nlinarith
  have hdlog : Real.log ((1 + m * (n - 1) : ℕ) : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) + Real.log n := by
    calc
      _ ≤ Real.log (((m + 1) * n : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hdegree)
      _ = _ := by
        rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have hlogn : Real.log (n : ℝ) = ((q : ℝ) + 1) * Real.log (2 : ℝ) := by
    simp only [n, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add, Nat.cast_one]
  have hqA : C + β * Real.log ((m + 1 : ℕ) : ℝ) < (q : ℝ) * A :=
    (div_lt_iff₀ hA).mp hq
  have hgap : C + β * Real.log ((m + 1 : ℕ) : ℝ) < (α - β) * Real.log n := by
    calc
      _ < ((q : ℝ) + 1) * A := by nlinarith
      _ = _ := by rw [hlogn]; dsimp [A]; ring
  refine ⟨n, hn, ?_⟩
  have hb := mul_le_mul_of_nonneg_left hdlog hβ
  nlinarith

end Lemmata.TensorRank.LogarithmicGrowth
