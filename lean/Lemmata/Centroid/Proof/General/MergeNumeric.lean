module

public import Lemmata.Centroid.Proof.General.Numeric
public import Lemmata.Centroid.Proof.General.AverageBound

@[expose] public section

namespace Lemmata.Centroid.General

theorem generalBound_le_support_succ (N : ℕ) : generalBound N ≤ supportBound N + 1 := by
  by_cases hN : N ≤ 1
  · simp only [generalBound, supportBound, hN, ite_true]
  · simp only [generalBound, supportBound, hN, ite_false, supportBoundAt]
    split_ifs with hs
    · simp only [generalBoundAt]
      split_ifs with h₀ h₁
      · simp [h₀]
      · simp [h₁, Nat.add_assoc]
      · have hp := Nat.sub_le (N - generalIndex N * (generalIndex N + 1)) 1
        nlinarith [Nat.mul_le_mul_left (N - generalIndex N * (generalIndex N + 1)) hp]
    · omega

theorem generalBoundAt_base_le (n s : ℕ) : n ^ 3 + 1 ≤ generalBoundAt n s := by
  unfold generalBoundAt
  split_ifs <;> omega

theorem large_merge_bound {N n s d₁ d₂ : ℕ} {u v : ℝ}
    (hn : 0 < n) (hs : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s)
    (hu : 2 * (n : ℝ) ≤ u) (hv : 2 * (n : ℝ) ≤ v) (huv : u + v ≤ N)
    (hd₁ : (d₁ : ℝ) ≤ 1 + envelope u) (hd₂ : (d₂ : ℝ) ≤ 1 + envelope v) :
    d₁ + d₂ ≤ generalBound N := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN₂ : 2 ≤ N := by nlinarith
  have hfeas : 4 * n ≤ N := by exact_mod_cast (show 4 * (n : ℝ) ≤ N by linarith)
  have he := envelope_pair_bound (l := 2 * n) (by positivity) hu hv huv
  have hsmall := envelope_two_mul_le hnR.le
  have hsum : (d₁ + d₂ : ℕ) < (generalBound N : ℝ) + 1 := by
    rw [generalBound_eq hN₂ hs hN]
    by_cases hsn : s ≤ n
    · have hn₂ : 2 ≤ n := by
        by_contra h
        have : n = 1 := by omega
        subst n
        omega
      have ht : 0 ≤ (N : ℝ) - 2 * n := by linarith
      have htupper : (N : ℝ) - 2 * n ≤ (n : ℝ) ^ 2 := by
        have hNR : (N : ℝ) = n * (n + 1) + s := by exact_mod_cast hN
        have hsR : (s : ℝ) ≤ n := by exact_mod_cast hsn
        nlinarith
      have hf := envelope_mono ht (sq_nonneg (n : ℝ)) htupper
      have hstrict := envelope_square_lt (n := (n : ℝ)) (by exact_mod_cast hn₂)
      have hbase := generalBoundAt_base_le n s
      have hbaseR : (n : ℝ) ^ 3 + 1 ≤ generalBoundAt n s := by exact_mod_cast hbase
      push_cast
      linarith
    · have ht : 0 < (N : ℝ) - 2 * n := by linarith
      have hNR : (N : ℝ) = n * (n + 1) + s := by exact_mod_cast hN
      have hsR : (s : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hs
      have htupper : (N : ℝ) - 2 * n ≤ (n : ℝ) ^ 2 + 3 * n := by nlinarith
      have hstrict := envelope_lt_mul hnR ht htupper
      have hbase : n ^ 3 + n * s + 1 ≤ generalBoundAt n s := by
        simp only [generalBoundAt, show s ≠ 0 by omega, show s ≠ 1 by omega,
          hsn, ite_false]
        omega
      have hbaseR : (n : ℝ) ^ 3 + n * s + 1 ≤ generalBoundAt n s := by exact_mod_cast hbase
      push_cast
      nlinarith
  have : d₁ + d₂ < generalBound N + 1 := by exact_mod_cast hsum
  omega

end Lemmata.Centroid.General
