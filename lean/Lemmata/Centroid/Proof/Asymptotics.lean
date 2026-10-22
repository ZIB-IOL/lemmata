module

public import Lemmata.Centroid.Def.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Lemmata.Centroid

open Filter
open scoped Topology

private theorem cubic_squeeze (q b : ℕ → ℝ) (a c C D : ℝ)
    (h : ∀ᶠ N in atTop,
      0 ≤ q N ∧ a * Real.sqrt N - C ≤ q N ∧ q N ≤ a * Real.sqrt N ∧
      c * q N ^ 3 ≤ b N ∧ b N ≤ c * (q N + D) ^ 3) :
    Tendsto (fun N : ℕ => b N / (N : ℝ) ^ (3 / 2 : ℝ)) atTop (𝓝 (c * a ^ 3)) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hC := hs.const_div_atTop C
  have hD := hs.const_div_atTop D
  have hp : ∀ᶠ N : ℕ in atTop, 0 < Real.sqrt N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hq : Tendsto (fun N : ℕ => q N / Real.sqrt N) atTop (𝓝 a) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub hC) tendsto_const_nhds
    · filter_upwards [h, hp] with N hN hpos
      apply (le_div_iff₀ hpos).2
      have : (a - C / Real.sqrt N) * Real.sqrt N = a * Real.sqrt N - C := by
        field_simp
      simpa only [this] using hN.2.1
    · filter_upwards [h, hp] with N hN hpos
      exact (div_le_iff₀ hpos).2 hN.2.2.1
  have hqD : Tendsto (fun N : ℕ => (q N + D) / Real.sqrt N) atTop (𝓝 a) := by
    simpa only [add_div, add_zero] using hq.add hD
  have hroot : ∀ N : ℕ, (Real.sqrt N) ^ 3 = (N : ℝ) ^ (3 / 2 : ℝ) := by
    intro N
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds.mul (hq.pow 3)) (tendsto_const_nhds.mul (hqD.pow 3))
  · filter_upwards [h, hp] with N hN hpos
    rw [← hroot, div_pow, ← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right (pow_pos hpos 3)).2 hN.2.2.2.1
  · filter_upwards [h, hp] with N hN hpos
    rw [← hroot, div_pow, ← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right (pow_pos hpos 3)).2 hN.2.2.2.2

private theorem general_cubic_bounds {q s : ℕ} (hs : s ≤ 2 * q + 1) :
    q ^ 3 ≤ generalBoundAt q s ∧ generalBoundAt q s ≤ (q + 4) ^ 3 := by
  have hsq : s ^ 2 ≤ (2 * q + 1) ^ 2 := Nat.pow_le_pow_left hs 2
  have hprod : q * s ≤ (2 * q + 1) ^ 2 := by nlinarith
  have hsub : (s - q - 1) ^ 2 - q ≤ s ^ 2 :=
    (Nat.sub_le _ _).trans (Nat.pow_le_pow_left (by omega) 2)
  have hpred : s * (s - 1) ≤ s ^ 2 := by nlinarith [Nat.sub_le s 1]
  unfold generalBoundAt
  split_ifs <;> constructor <;> nlinarith

private theorem six_mul_choose_three (q : ℕ) :
    6 * (q + 2).choose 3 = q * (q + 1) * (q + 2) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hstep := Nat.choose_succ_succ' (q + 2) 2
    have htwo := two_mul_choose_two_succ (q + 1)
    have heq : q + 1 + 2 = (q + 2) + 1 := by omega
    rw [heq, hstep]
    nlinarith

private theorem symmetric_cubic_bounds {q s : ℕ} (hs : s ≤ q + 1) :
    q ^ 3 ≤ 6 * symmetricBoundAt q s ∧ 6 * symmetricBoundAt q s ≤ (q + 6) ^ 3 := by
  have hchoose := six_mul_choose_three q
  have hchoose2 : s.choose 2 ≤ s ^ 2 := by
    rw [Nat.choose_two_right]
    have : s * (s - 1) ≤ s ^ 2 := by nlinarith [Nat.sub_le s 1]
    exact (Nat.div_le_self _ _).trans this
  have hsquare : s ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left hs 2
  have hmax : max s (s.choose 2) ≤ (q + 1) ^ 2 := by
    exact max_le (by nlinarith) (hchoose2.trans hsquare)
  unfold symmetricBoundAt
  constructor
  · have hprod : q ^ 3 ≤ q * (q + 1) * (q + 2) := by
      calc
        q ^ 3 = q * q * q := by ring
        _ ≤ q * (q + 1) * (q + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left q (by omega)) (by omega)
    calc
      q ^ 3 ≤ q * (q + 1) * (q + 2) := hprod
      _ = 6 * (q + 2).choose 3 := hchoose.symm
      _ ≤ 6 * ((q + 2).choose 3 + 1 + max s (s.choose 2)) :=
        Nat.mul_le_mul_left 6 (by omega)
  · nlinarith

theorem generalBound_asymptotic :
    Tendsto (fun N : ℕ => (generalBound N : ℝ) / (N : ℝ) ^ (3 / 2 : ℝ))
      atTop (𝓝 1) := by
  have h := cubic_squeeze (fun N => generalIndex N) (fun N => generalBound N) 1 1 2 4 ?_
  · simpa using h
  filter_upwards [eventually_ge_atTop 2] with N hN
  let q := generalIndex N
  let s := N - q * (q + 1)
  have hs : s ≤ 2 * q + 1 := general_remainder_le hN
  have hdecomp : N = q * (q + 1) + s := general_decomposition N
  have hb := general_cubic_bounds hs
  rw [← generalBound_eq hN hs hdecomp] at hb
  have hbase : (q : ℝ) * ((q : ℝ) + 1) ≤ N := by exact_mod_cast generalIndex_base_le N
  have hupper : (N : ℝ) ≤ ((q : ℝ) + 2) ^ 2 := by exact_mod_cast (show N ≤ (q + 2) ^ 2 by nlinarith)
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hq : (0 : ℝ) ≤ q := by positivity
  have hsq := Real.sqrt_nonneg (N : ℝ)
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · simpa only [one_mul] using (show (q : ℝ) ^ 3 ≤ (generalBound N : ℝ) by
      exact_mod_cast hb.1)
  · simpa only [one_mul] using (show (generalBound N : ℝ) ≤ ((q : ℝ) + 4) ^ 3 by
      exact_mod_cast hb.2)

theorem symmetricBound_asymptotic :
    Tendsto (fun N : ℕ => (symmetricBound N : ℝ) / (N : ℝ) ^ (3 / 2 : ℝ))
      atTop (𝓝 (Real.sqrt 2 / 3)) := by
  have h := cubic_squeeze (fun N => symmetricIndex N) (fun N => symmetricBound N)
    (Real.sqrt 2) (1 / 6) 3 6 ?_
  · have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have heq : (1 / 6 : ℝ) * Real.sqrt 2 ^ 3 = Real.sqrt 2 / 3 := by
      rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hsqrt]
      ring
    simpa only [heq] using h
  filter_upwards [eventually_ge_atTop 2] with N hN
  let q := symmetricIndex N
  let s := N - symmetricBase q
  have hs : s ≤ q + 1 := symmetric_remainder_le N
  have hdecomp : N = symmetricBase q + s := symmetric_decomposition N
  have hb := symmetric_cubic_bounds hs
  rw [← symmetricBound_eq hN hs hdecomp] at hb
  have htwo : 2 * symmetricBase q = q * (q + 3) := by
    rw [symmetricBase_eq_choose]
    have hchoose := two_mul_choose_two_succ (q + 1)
    have hpos := Nat.choose_pos (show 2 ≤ q + 2 by omega)
    rw [show q + 1 + 1 = q + 2 by omega] at hchoose
    nlinarith [Nat.sub_add_cancel (show 1 ≤ (q + 2).choose 2 by omega)]
  have hbase : (q : ℝ) * ((q : ℝ) + 3) ≤ 2 * N := by
    exact_mod_cast (show q * (q + 3) ≤ 2 * N by omega)
  have hupper : (2 : ℝ) * N ≤ ((q : ℝ) + 3) ^ 2 := by
    exact_mod_cast (show 2 * N ≤ (q + 3) ^ 2 by nlinarith)
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have htwoRoot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (Real.sqrt 2 * Real.sqrt N) ^ 2 = 2 * N := by
    rw [mul_pow, hroot, htwoRoot]
  have hq : (0 : ℝ) ≤ q := by positivity
  have hsqnonneg : 0 ≤ Real.sqrt 2 * Real.sqrt N := by positivity
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have hcast : (q : ℝ) ^ 3 ≤ 6 * (symmetricBound N : ℝ) := by exact_mod_cast hb.1
    linarith
  · have hcast : 6 * (symmetricBound N : ℝ) ≤ ((q : ℝ) + 6) ^ 3 := by exact_mod_cast hb.2
    linarith

end Lemmata.Centroid
