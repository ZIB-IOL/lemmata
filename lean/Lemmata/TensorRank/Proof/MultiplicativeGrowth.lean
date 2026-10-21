module

public import Lemmata.TensorRank.Proof.PowerBounds
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

set_option autoImplicit false

open Classical

namespace Lemmata.TensorRank

theorem map_nat_power {f : ℕ → ℝ} (h1 : f 1 = 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (b q : ℕ) : f (b ^ q) = f b ^ q := by
  induction q with
  | zero => simpa using h1
  | succ q ih => rw [pow_succ, hmul, ih, pow_succ]

theorem monotone_multiplicative_le_rpow {f : ℕ → ℝ} (h1 : f 1 = 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hmono : Monotone f)
    {b d : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d) :
    f b ≤ (b : ℝ) ^ (Real.log (f d) / Real.log (d : ℝ)) := by
  have hbase (a : ℕ) (ha : 1 ≤ a) : 1 ≤ f a := by simpa only [h1] using hmono ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  have hlogd : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  let a : ℝ := Real.log (b : ℝ) / Real.log (d : ℝ)
  have ha : 0 < a := div_pos hlogb hlogd
  have hr : 1 ≤ f d := hbase d (by omega)
  have hr0 : 0 < f d := zero_lt_one.trans_le hr
  have hh : f b ≤ (f d) ^ a := by
    apply le_of_polynomial_power_bound (zero_le_one.trans (hbase b (by omega)))
      (Real.rpow_nonneg hr0.le _) (f d) hr0 0
    intro n _
    let q : ℕ := ⌈(n : ℝ) * a⌉₊
    have hdim : b ^ n ≤ d ^ q := by
      have hl := mul_le_mul_of_nonneg_right (Nat.le_ceil ((n : ℝ) * a)) hlogd.le
      have he : (n : ℝ) * a * Real.log (d : ℝ) = n * Real.log (b : ℝ) := by
        dsimp only [a]
        rw [mul_assoc, div_mul_cancel₀ _ hlogd.ne']
      rw [he] at hl
      have hp : (b : ℝ) ^ n ≤ (d : ℝ) ^ q :=
        (Real.log_le_log_iff (pow_pos hb0 _) (pow_pos hd0 _)).mp (by
          simpa only [Real.log_pow] using hl)
      exact_mod_cast hp
    have hf : f b ^ n ≤ f d ^ q := by
      simpa only [map_nat_power h1 hmul] using hmono hdim
    have hq : (q : ℝ) ≤ (n : ℝ) * a + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) ha.le)).le
    calc
      _ ≤ f d ^ q := hf
      _ = f d ^ (q : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ f d ^ ((n : ℝ) * a + 1) := Real.rpow_le_rpow_of_exponent_le hr hq
      _ = f d * ((n : ℝ) + 1) ^ 0 * (f d ^ a) ^ n := by
        rw [Real.rpow_add hr0, Real.rpow_one, mul_comm (n : ℝ) a,
          Real.rpow_mul_natCast hr0.le, pow_zero, mul_one, mul_comm]
  have he : f d ^ a = (b : ℝ) ^ (Real.log (f d) / Real.log (d : ℝ)) := by
    rw [Real.rpow_def_of_pos hr0, Real.rpow_def_of_pos hb0]
    congr 1
    dsimp only [a]
    ring
  exact hh.trans_eq he

theorem monotone_multiplicative_log_ratio {f : ℕ → ℝ} (h1 : f 1 = 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hmono : Monotone f)
    {b d : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d) :
    Real.log (f b) / Real.log (b : ℝ) = Real.log (f d) / Real.log (d : ℝ) := by
  have hle (b d : ℕ) (hb : 2 ≤ b) (hd : 2 ≤ d) :
      Real.log (f b) / Real.log (b : ℝ) ≤ Real.log (f d) / Real.log (d : ℝ) := by
    have hpos : 0 < f b := by
      have h : 1 ≤ f b := by simpa only [h1] using hmono (by omega : 1 ≤ b)
      exact zero_lt_one.trans_le h
    have hlog := Real.log_le_log hpos (monotone_multiplicative_le_rpow h1 hmul hmono hb hd)
    rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < b))] at hlog
    exact (div_le_iff₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < b)))).mpr hlog
  exact le_antisymm (hle b d hb hd) (hle d b hd hb)

theorem monotone_multiplicative_eq_rpow {f : ℕ → ℝ} (h1 : f 1 = 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hmono : Monotone f)
    {b : ℕ} (hb : 1 ≤ b) : f b = (b : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  by_cases hb1 : b = 1
  · subst b
    simp only [h1, Nat.cast_one, Real.one_rpow]
  · have hb2 : 2 ≤ b := by omega
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hf : 0 < f b := by
      have h : 1 ≤ f b := by simpa only [h1] using hmono hb
      exact zero_lt_one.trans_le h
    have he := (div_eq_iff (Real.log_pos (by exact_mod_cast (by omega : 1 < b))).ne').mp
      (monotone_multiplicative_log_ratio h1 hmul hmono hb2 (by omega : 2 ≤ 2))
    simp only [Nat.cast_ofNat] at he
    rw [Real.rpow_def_of_pos hb0, mul_comm (Real.log (b : ℝ)), ← he, Real.exp_log hf]

end Lemmata.TensorRank
