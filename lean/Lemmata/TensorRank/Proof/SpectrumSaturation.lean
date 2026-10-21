module

public import Lemmata.TensorRank.Proof.SpectrumAsymptotic

@[expose] public section

set_option autoImplicit false

open Filter Set
open scoped Topology
open Classical

namespace Lemmata.TensorRank.Spectrum.StrassenPreorder

variable {S : Type*} [CommSemiring S] (p : StrassenPreorder S)

theorem rank_antitone {q : StrassenPreorder S} (hpq : p ≤ q) (a : S) :
    q.rank a ≤ p.rank a :=
  (q.rank_le_iff _ _).mpr (hpq _ _ (p.rel_rank a))

theorem asymptoticRank_antitone {q : StrassenPreorder S} (hpq : p ≤ q) (a : S) :
    q.asymptoticRank a ≤ p.asymptoticRank a := by
  apply le_ciInf
  intro n
  exact (q.asymptoticRank_le_root a n).trans (Real.rpow_le_rpow (Nat.cast_nonneg _)
    (by exact_mod_cast p.rank_antitone hpq (a ^ (n + 1))) (by positivity))

theorem oneLeNonzero_mono {q : StrassenPreorder S} (hp : p.OneLeNonzero) (hpq : p ≤ q) :
    q.OneLeNonzero := fun a ha => hpq _ _ (hp a ha)

theorem asymptoticRank_le_linearValue (hp : p.OneLeNonzero) (a : S) :
    p.asymptoticRank a ≤ p.linearValue a := by
  apply ge_of_tendsto (p.tendsto_linearValue a)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  apply (le_div_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr
  have h := p.asymptoticRank_le_rank ((n : S) * a)
  rw [p.asymptoticRank_nat_mul hp] at h
  simpa only [mul_comm] using h

theorem asymptoticRank_le_of_constant_power_bound (a : S) (C b : ℝ)
    (hC : 0 < C) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, 0 < n → (p.rank (a ^ n) : ℝ) ≤ C * b ^ n) :
    p.asymptoticRank a ≤ b := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => C ^ ((n : ℝ)⁻¹) * b) atTop (𝓝 b) := by
    simpa only [Real.rpow_zero, one_mul] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).rpow hi
        (Or.inl hC.ne')).mul_const b
  apply le_of_tendsto_of_tendsto (p.tendsto_power_rank_root a) ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  calc
    _ ≤ (C * b ^ n) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (h n hn) (by positivity)
    _ = _ := by rw [Real.mul_rpow hC.le (pow_nonneg hb _),
      Real.pow_rpow_inv_natCast hb (Nat.ne_of_gt hn)]

theorem asymptoticRank_eq_of_rank_bounds {q : StrassenPreorder S} (hpq : p ≤ q)
    (h : ∀ a, p.asymptoticRank a ≤ (q.rank a : ℝ)) (a : S) :
    p.asymptoticRank a = q.asymptoticRank a := by
  apply le_antisymm _ (p.asymptoticRank_antitone hpq a)
  apply le_ciInf
  intro n
  have hh := Real.rpow_le_rpow (pow_nonneg (p.asymptoticRank_nonneg a) (n + 1))
    (by simpa only [p.asymptoticRank_pow] using h (a ^ (n + 1)))
    (by positivity : 0 ≤ (n + 1 : ℝ)⁻¹)
  simpa only [show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by simp,
    Real.pow_rpow_inv_natCast (p.asymptoticRank_nonneg a) (Nat.succ_ne_zero n)] using hh

theorem add_catalyst_iterate {a b c : S} (h : p.Rel (a + c) (b + c)) (n : ℕ) :
    p.Rel ((n : S) * a + c) ((n : S) * b + c) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul, zero_add] using p.refl c
  | succ n ih =>
    have h₁ : p.Rel (((n : S) + 1) * a + c) ((n : S) * b + (a + c)) := by
      convert p.add ih (p.refl a) using 1 <;> ring
    have h₂ := p.add (p.refl ((n : S) * b)) h
    simpa only [Nat.cast_succ, add_mul, one_mul, add_assoc] using p.trans h₁ h₂

theorem asymptoticRank_addClosure (hp : p.OneLeNonzero) (a : S) :
    p.addClosure.asymptoticRank a = p.asymptoticRank a := by
  symm
  apply p.asymptoticRank_eq_of_rank_bounds (q := p.addClosure)
    (fun _ _ h => ⟨0, by simpa only [add_zero] using h⟩)
  intro b
  obtain ⟨c, hc⟩ := p.addClosure.rel_rank b
  let r := p.addClosure.rank b
  have hr (n : ℕ) : p.rank ((n : S) * b) ≤ n * r + p.rank c := by
    have h₁ : p.Rel ((n : S) * b) ((n : S) * b + c) := by
      simpa only [add_zero] using p.add (p.refl ((n : S) * b)) (p.zero_le c)
    exact (p.rank_mono (p.trans h₁ (p.add_catalyst_iterate hc n))).trans
      (by simpa only [← Nat.cast_mul, p.rank_nat] using p.rank_add_le ((n * r : ℕ) : S) c)
  have ht : Tendsto (fun n : ℕ => (r : ℝ) + (p.rank c : ℝ) / (n : ℝ)) atTop (𝓝 (r : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (r : ℝ)) atTop (𝓝 (r : ℝ))).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (p.rank c : ℝ)) atTop
        (𝓝 (p.rank c : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
  apply (p.asymptoticRank_le_linearValue hp b).trans
  apply le_of_tendsto_of_tendsto (p.tendsto_linearValue b) ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  apply (div_le_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr
  rw [add_mul, div_mul_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℝ) ≠ 0)]
  exact_mod_cast (by simpa only [Nat.mul_comm] using hr n :
    p.rank ((n : S) * b) ≤ r * n + p.rank c)

theorem mul_catalyst_iterate {a b c : S} (h : p.Rel (a * c) (b * c)) (n : ℕ) :
    p.Rel (a ^ n * c) (b ^ n * c) := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using p.refl c
  | succ n ih =>
    have h₁ : p.Rel (a ^ (n + 1) * c) (b ^ n * (a * c)) := by
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using p.mul ih (p.refl a)
    have h₂ := p.mul (p.refl (b ^ n)) h
    simpa only [pow_succ, mul_assoc] using p.trans h₁ h₂

theorem asymptoticRank_mulClosure (hc : p.AddCancellative) (a : S) :
    (p.mulClosure hc).asymptoticRank a = p.asymptoticRank a := by
  symm
  apply p.asymptoticRank_eq_of_rank_bounds (q := p.mulClosure hc)
    (fun _ _ h => ⟨1, p.one_ne_zero, by simpa only [mul_one] using h⟩)
  intro b
  obtain ⟨c, hcz, hbc⟩ := (p.mulClosure hc).rel_rank b
  let r := (p.mulClosure hc).rank b
  obtain ⟨m, hm⟩ := p.cofinal 1 c hcz
  have hb (n : ℕ) : p.rank (b ^ n) ≤ (m * p.rank c) * r ^ n := by
    have h₁ : p.Rel (b ^ n) ((m : S) * (b ^ n * c)) := by
      convert p.mul (p.refl (b ^ n)) hm using 1 <;> ring
    have h₂ := p.mul (p.refl (m : S)) (p.mul_catalyst_iterate hbc n)
    have h₃ : p.Rel ((m : S) * ((r : S) ^ n * c))
        ((m : S) * ((r : S) ^ n) * (p.rank c : S)) := by
      simpa only [mul_assoc] using p.mul (p.refl ((m : S) * ((r : S) ^ n))) (p.rel_rank c)
    have h₄ : p.Rel (b ^ n) (((m * p.rank c) * r ^ n : ℕ) : S) := by
      convert p.trans (p.trans h₁ h₂) h₃ using 1
      simp only [Nat.cast_mul, Nat.cast_pow]
      ring
    exact (p.rank_le_iff _ _).mpr h₄
  apply p.asymptoticRank_le_of_constant_power_bound b
    ((m * p.rank c : ℕ) + 1 : ℝ) r (by positivity) (Nat.cast_nonneg _)
  intro n _
  calc
    (p.rank (b ^ n) : ℝ) ≤ (m * p.rank c : ℕ) * (r : ℝ) ^ n := by exact_mod_cast hb n
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (Nat.cast_nonneg r) n)

theorem addClosure_addCancellative : p.addClosure.AddCancellative := by
  rintro a b c ⟨d, h⟩
  exact ⟨c + d, by simpa only [add_assoc] using h⟩

theorem mulClosure_addCancellative (hc : p.AddCancellative) :
    (p.mulClosure hc).AddCancellative := by
  rintro a b c ⟨d, hd, h⟩
  exact ⟨d, hd, hc _ _ (c * d) (by simpa only [add_mul] using h)⟩

theorem mulClosure_mulCancellative (hc : p.AddCancellative) :
    (p.mulClosure hc).MulCancellative := by
  rintro a b c hcz ⟨d, hd, h⟩
  exact ⟨c * d, p.mul_ne_zero hcz hd, by simpa only [mul_assoc] using h⟩

def saturated : StrassenPreorder S := p.addClosure.mulClosure p.addClosure_addCancellative

theorem le_saturated : p ≤ p.saturated := fun _ _ h =>
  ⟨1, p.one_ne_zero, 0, by simpa only [mul_one, add_zero] using h⟩

theorem saturated_addCancellative : p.saturated.AddCancellative :=
  p.addClosure.mulClosure_addCancellative p.addClosure_addCancellative

theorem saturated_mulCancellative : p.saturated.MulCancellative :=
  p.addClosure.mulClosure_mulCancellative p.addClosure_addCancellative

theorem asymptoticRank_saturated (hp : p.OneLeNonzero) (a : S) :
    p.saturated.asymptoticRank a = p.asymptoticRank a := by
  rw [saturated, p.addClosure.asymptoticRank_mulClosure, p.asymptoticRank_addClosure hp]

end Lemmata.TensorRank.Spectrum.StrassenPreorder
