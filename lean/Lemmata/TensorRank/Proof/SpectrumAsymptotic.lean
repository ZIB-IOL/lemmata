module

public import Lemmata.TensorRank.Proof.SpectrumExtension
public import Lemmata.TensorRank.Proof.SpectrumPoint
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

set_option autoImplicit false

open Filter Set
open scoped Topology
open Classical

namespace Lemmata.TensorRank.Spectrum.StrassenPreorder

variable {S : Type*} [CommSemiring S] (p : StrassenPreorder S)

def OneLeNonzero : Prop := ∀ a, a ≠ 0 → p.Rel 1 a

@[simp] theorem rank_zero : p.rank 0 = 0 := by
  simpa only [Nat.cast_zero] using p.rank_nat 0

theorem rel_zero_iff (a : S) : p.Rel a 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    obtain ⟨n, hn⟩ := p.cofinal 1 a ha
    have hz : p.Rel (1 : S) 0 := p.trans hn (by
      simpa only [mul_zero] using p.mul (p.refl (n : S)) h)
    have := (p.nat_iff 1 0).mp (by simpa only [Nat.cast_one, Nat.cast_zero] using hz)
    omega
  · rintro rfl
    exact p.refl _

@[simp] theorem rank_eq_zero_iff (a : S) : p.rank a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hr := p.rel_rank a
    rw [h, Nat.cast_zero] at hr
    exact (p.rel_zero_iff a).mp hr
  · rintro rfl
    exact p.rank_zero

include p in
theorem pow_ne_zero {a : S} (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  induction n with
  | zero => simpa only [pow_zero] using p.one_ne_zero
  | succ n ih => simpa only [pow_succ] using p.mul_ne_zero ih ha

theorem one_le_rank_power {a : S} (ha : a ≠ 0) (n : ℕ) : 1 ≤ p.rank (a ^ n) :=
  Nat.one_le_iff_ne_zero.mpr (fun h => p.pow_ne_zero ha n ((p.rank_eq_zero_iff _).mp h))

theorem one_le_asymptoticRank {a : S} (ha : a ≠ 0) : 1 ≤ p.asymptoticRank a := by
  apply le_ciInf
  intro n
  apply Real.one_le_rpow
  · exact_mod_cast p.one_le_rank_power ha (n + 1)
  · positivity

@[simp] theorem asymptoticRank_zero : p.asymptoticRank 0 = 0 := by
  apply le_antisymm _ (p.asymptoticRank_nonneg _)
  simpa only [p.rank_zero, Nat.cast_zero] using p.asymptoticRank_le_rank 0

@[simp] theorem asymptoticRank_nat (m : ℕ) : p.asymptoticRank (m : S) = m := by
  have he (n : ℕ) : (p.rank ((m : S) ^ (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹) = m := by
    rw [← Nat.cast_pow, p.rank_nat, Nat.cast_pow]
    simpa only [Nat.cast_succ, Nat.succ_eq_add_one] using
      Real.pow_rpow_inv_natCast (Nat.cast_nonneg m) (Nat.succ_ne_zero n)
  unfold asymptoticRank
  simp_rw [he]
  simp

theorem asymptoticRank_le_pow_root (a : S) {n : ℕ} (hn : 0 < n) :
    p.asymptoticRank a ≤ (p.rank (a ^ n) : ℝ) ^ ((n : ℝ)⁻¹) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa only [Nat.cast_succ, Nat.succ_eq_add_one] using p.asymptoticRank_le_root a m

theorem tendsto_power_rank_root (a : S) :
    Tendsto (fun n : ℕ => (p.rank (a ^ n) : ℝ) ^ ((n : ℝ)⁻¹))
      atTop (𝓝 (p.asymptoticRank a)) := by
  by_cases ha : a = 0
  · subst a
    rw [p.asymptoticRank_zero]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [zero_pow (Nat.ne_of_gt hn), p.rank_zero, Nat.cast_zero,
      Real.zero_rpow (by positivity : (n : ℝ)⁻¹ ≠ 0)]
  let r (n : ℕ) : ℝ := p.rank (a ^ n)
  have hr (n : ℕ) : 1 ≤ r n := by
    change (1 : ℝ) ≤ (p.rank (a ^ n) : ℝ)
    exact_mod_cast p.one_le_rank_power ha n
  have hpos (n : ℕ) : 0 < r n := zero_lt_one.trans_le (hr n)
  have hs : Subadditive (fun n => Real.log (r n)) := by
    intro m n
    calc
      _ ≤ Real.log (r m * r n) := by
        apply Real.log_le_log (hpos _)
        dsimp only [r]
        rw [pow_add]
        exact_mod_cast p.rank_mul_le (a ^ m) (a ^ n)
      _ = _ := Real.log_mul (hpos m).ne' (hpos n).ne'
  have hb : BddBelow (range fun n : ℕ => Real.log (r n) / (n : ℝ)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (Real.log_nonneg (hr n)) (Nat.cast_nonneg _)⟩
  have he (n : ℕ) : (r n) ^ ((n : ℝ)⁻¹) = Real.exp (Real.log (r n) / (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (hpos n), div_eq_mul_inv]
  have ht : Tendsto (fun n : ℕ => (r n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 (Real.exp hs.lim)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp (hs.tendsto_lim hb)).congr (fun n => (he n).symm)
  have hv : p.asymptoticRank a = Real.exp hs.lim := by
    apply le_antisymm
    · exact ge_of_tendsto ht (by
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
        exact p.asymptoticRank_le_pow_root a hn)
    · apply le_ciInf
      intro n
      rw [show (p.rank (a ^ (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹) =
        Real.exp (Real.log (r (n + 1)) / ((n + 1 : ℕ) : ℝ)) by
          simpa only [Nat.cast_add, Nat.cast_one] using he (n + 1)]
      exact Real.exp_le_exp.mpr (hs.lim_le_div hb (Nat.succ_ne_zero n))
  simpa only [hv] using ht

theorem asymptoticRank_pow (a : S) (q : ℕ) :
    p.asymptoticRank (a ^ q) = p.asymptoticRank a ^ q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simpa only [pow_zero, Nat.cast_one] using p.asymptoticRank_nat 1
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have ht := ((p.tendsto_power_rank_root a).comp (tendsto_id.const_mul_atTop' hq)).pow q
  have he (n : ℕ) :
      ((p.rank (a ^ (q * n)) : ℝ) ^ (((q * n : ℕ) : ℝ)⁻¹)) ^ q =
        (p.rank ((a ^ q) ^ n) : ℝ) ^ ((n : ℝ)⁻¹) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) _ q, ← pow_mul]
    congr 1
    rw [Nat.cast_mul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hq0, mul_one]
  exact tendsto_nhds_unique (p.tendsto_power_rank_root (a ^ q)) (ht.congr he)

theorem asymptoticRank_mul_le (a b : S) :
    p.asymptoticRank (a * b) ≤ p.asymptoticRank a * p.asymptoticRank b := by
  apply le_of_tendsto_of_tendsto' (p.tendsto_power_rank_root (a * b))
    ((p.tendsto_power_rank_root a).mul (p.tendsto_power_rank_root b))
  intro n
  rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · rw [mul_pow]
    exact_mod_cast p.rank_mul_le (a ^ n) (b ^ n)
  · positivity

private theorem tendsto_ceil_normalized (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {l : ℝ}
    (h : Tendsto (fun n : ℕ => f n / ((n : ℝ) + 1)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (⌈f n⌉₊ : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 l) := by
  have hz : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun n : ℕ => ((⌈f n⌉₊ : ℝ) - f n) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    apply squeeze_zero _ _ hz
    · exact fun n => div_nonneg (sub_nonneg.mpr (Nat.le_ceil _)) (by positivity)
    · intro n
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc := Nat.ceil_lt_add_one (hf n)
      linarith
  simpa only [zero_add] using (he.add h).congr (fun n => show
    ((⌈f n⌉₊ : ℝ) - f n) / ((n : ℝ) + 1) + f n / ((n : ℝ) + 1) =
      (⌈f n⌉₊ : ℝ) / ((n : ℝ) + 1) by ring)

theorem asymptoticRank_nat_mul (hp : p.OneLeNonzero) (m : ℕ) (a : S) :
    p.asymptoticRank ((m : S) * a) = (m : ℝ) * p.asymptoticRank a := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, zero_mul, p.asymptoticRank_zero]
  by_cases ha : a = 0
  · subst a
    simp only [mul_zero, p.asymptoticRank_zero]
  apply le_antisymm
  · simpa only [p.asymptoticRank_nat] using p.asymptoticRank_mul_le (m : S) a
  by_cases hm1 : m = 1
  · subst m
    simp only [Nat.cast_one, one_mul]
    exact le_refl _
  let ρ := p.asymptoticRank a
  let A := p.asymptoticRank ((m : S) * a)
  change (m : ℝ) * ρ ≤ A
  have hρ1 : 1 ≤ ρ := p.one_le_asymptoticRank ha
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ1
  have hmono : ρ ≤ A := p.asymptoticRank_mono (by
    simpa only [Nat.cast_one, one_mul] using
      p.mul ((p.nat_iff 1 m).mpr (by omega)) (p.refl a))
  have hA0 : 0 < A := hρ0.trans_le hmono
  by_cases hρ : ρ = 1
  · have hbase := p.asymptoticRank_mono (p.mul (p.refl (m : S)) (hp a ha))
    rw [mul_one, p.asymptoticRank_nat] at hbase
    simpa only [hρ, mul_one] using hbase
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlogρ : 0 < Real.log ρ := Real.log_pos (lt_of_le_of_ne hρ1 (Ne.symm hρ))
  have hr0 (n : ℕ) : 0 < (p.rank (a ^ (n + 1)) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le (p.one_le_rank_power ha (n + 1))
  let f (n : ℕ) : ℝ := Real.log (p.rank (a ^ (n + 1)) : ℝ) / Real.log (m : ℝ)
  let q (n : ℕ) : ℕ := ⌈f n⌉₊
  have hf (n : ℕ) : 0 ≤ f n := div_nonneg
    (Real.log_nonneg (by exact_mod_cast p.one_le_rank_power ha (n + 1))) hlogm.le
  have ht : Tendsto (fun n : ℕ => Real.log (p.rank (a ^ (n + 1)) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (Real.log ρ)) := by
    apply (((p.tendsto_power_rank_root a).comp (tendsto_add_atTop_nat 1)).log hρ0.ne').congr
    intro n
    dsimp only [Function.comp_def]
    rw [Real.log_rpow (hr0 n), Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]
  have htf : Tendsto (fun n : ℕ => f n / ((n : ℝ) + 1))
      atTop (𝓝 (Real.log ρ / Real.log (m : ℝ))) := by
    apply (ht.div_const (Real.log (m : ℝ))).congr
    intro n
    dsimp only [f]
    ring
  have hq := tendsto_ceil_normalized f hf htf
  have hbound (n : ℕ) : p.rank (a ^ (n + 1)) ≤ m ^ q n := by
    have hc := mul_le_mul_of_nonneg_right (Nat.le_ceil (f n)) hlogm.le
    change (Real.log (p.rank (a ^ (n + 1)) : ℝ) / Real.log (m : ℝ)) * Real.log (m : ℝ) ≤ _ at hc
    rw [div_mul_cancel₀ _ hlogm.ne'] at hc
    have hr : (p.rank (a ^ (n + 1)) : ℝ) ≤ (m : ℝ) ^ q n :=
      (Real.log_le_log_iff (hr0 n) (pow_pos hm0 _)).mp (by simpa only [Real.log_pow] using hc)
    exact_mod_cast hr
  have hseq (n : ℕ) : Real.log ρ ≤ ((q n : ℝ) / ((n : ℝ) + 1)) * (Real.log A - Real.log ρ) := by
    have hb := p.trans (p.rel_rank (a ^ (n + 1))) ((p.nat_iff _ _).mpr (hbound n))
    have he : p.Rel (a ^ (n + 1 + q n)) (((m : S) * a) ^ q n) := by
      simpa only [Nat.cast_pow, ← pow_add, ← mul_pow] using p.mul hb (p.refl (a ^ q n))
    have hv := p.asymptoticRank_mono he
    rw [p.asymptoticRank_pow, p.asymptoticRank_pow] at hv
    have hl := Real.log_le_log (pow_pos hρ0 _) hv
    rw [Real.log_pow, Real.log_pow] at hl
    simp only [Nat.cast_add, Nat.cast_one] at hl
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith
  have hlim := ge_of_tendsto' (hq.mul_const (Real.log A - Real.log ρ)) hseq
  have hh := mul_le_mul_of_nonneg_right hlim hlogm.le
  have he : (Real.log ρ / Real.log (m : ℝ)) * (Real.log A - Real.log ρ) * Real.log (m : ℝ) =
      Real.log ρ * (Real.log A - Real.log ρ) := by
    field_simp
  rw [he] at hh
  have hc := (mul_le_mul_iff_right₀ hlogρ).mp hh
  apply (Real.log_le_log_iff (mul_pos hm0 hρ0) hA0).mp
  rw [Real.log_mul hm0.ne' hρ0.ne']
  linarith

end Lemmata.TensorRank.Spectrum.StrassenPreorder
