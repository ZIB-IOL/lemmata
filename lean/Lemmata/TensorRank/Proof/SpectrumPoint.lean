module

public import Lemmata.TensorRank.Proof.SpectrumRank
public import Mathlib.Order.Filter.AtTopBot.Ring

@[expose] public section

set_option autoImplicit false

open Filter Set
open scoped Topology
open Classical

namespace Lemmata.TensorRank.Spectrum.StrassenPreorder

variable {S : Type*} [CommSemiring S] (p : StrassenPreorder S)

theorem scalarRank_subadditive (a : S) :
    Subadditive (fun n : ℕ => (p.rank ((n : S) * a) : ℝ)) := by
  intro m n
  simp only [Nat.cast_add, add_mul]
  exact_mod_cast p.rank_add_le ((m : S) * a) ((n : S) * a)

noncomputable def linearValue (a : S) : ℝ := (scalarRank_subadditive p a).lim

theorem tendsto_linearValue (a : S) :
    Tendsto (fun n : ℕ => (p.rank ((n : S) * a) : ℝ) / n) atTop (𝓝 (p.linearValue a)) :=
  (scalarRank_subadditive p a).tendsto_lim
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩

theorem linearValue_nonneg (a : S) : 0 ≤ p.linearValue a :=
  ge_of_tendsto' (p.tendsto_linearValue a)
    (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem linearValue_mono {a b : S} (h : p.Rel a b) : p.linearValue a ≤ p.linearValue b := by
  apply le_of_tendsto_of_tendsto' (p.tendsto_linearValue a) (p.tendsto_linearValue b)
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast p.rank_mono (p.mul (p.refl (n : S)) h)

@[simp] theorem linearValue_nat (m : ℕ) : p.linearValue (m : S) = m := by
  apply tendsto_nhds_unique (p.tendsto_linearValue (m : S))
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (m : ℝ)) atTop (𝓝 (m : ℝ))).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  change (m : ℝ) = (p.rank ((n : S) * (m : S)) : ℝ) / n
  rw [← Nat.cast_mul, p.rank_nat, Nat.cast_mul]
  field_simp

theorem pred_rank_le (ht : ∀ a b, p.Rel a b ∨ p.Rel b a) (a : S) :
    p.Rel ((p.rank a - 1 : ℕ) : S) a := by
  by_cases h0 : p.rank a = 0
  · simpa only [h0, Nat.zero_sub, Nat.cast_zero] using p.zero_le a
  · have hn : ¬ p.Rel a ((p.rank a - 1 : ℕ) : S) := by
      intro h
      have := (p.rank_le_iff _ _).mpr h
      omega
    exact (ht _ _).resolve_right hn

theorem linearValue_add (ht : ∀ a b, p.Rel a b ∨ p.Rel b a) (a b : S) :
    p.linearValue (a + b) = p.linearValue a + p.linearValue b := by
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto' (p.tendsto_linearValue (a + b))
      ((p.tendsto_linearValue a).add (p.tendsto_linearValue b))
    intro n
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (by simpa only [mul_add] using p.rank_add_le ((n : S) * a) ((n : S) * b))
  · have hzero : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    have hl := (p.tendsto_linearValue (a + b)).add hzero
    rw [add_zero] at hl
    apply le_of_tendsto_of_tendsto' ((p.tendsto_linearValue a).add (p.tendsto_linearValue b)) hl
    intro n
    have hf : (p.rank ((n : S) * a) - 1) + (p.rank ((n : S) * b) - 1) ≤
        p.rank ((n : S) * (a + b)) := by
      have h := p.rank_mono (p.add (p.pred_rank_le ht ((n : S) * a))
        (p.pred_rank_le ht ((n : S) * b)))
      simpa only [← Nat.cast_add, p.rank_nat, ← mul_add] using h
    have hnat : p.rank ((n : S) * a) + p.rank ((n : S) * b) ≤
        p.rank ((n : S) * (a + b)) + 2 := by omega
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast hnat

private theorem linearValue_square (ht : ∀ a b, p.Rel a b ∨ p.Rel b a) (a : S) :
    p.linearValue (a * a) = p.linearValue a * p.linearValue a := by
  have hm : Tendsto (fun n : ℕ =>
      (p.rank (((n * n : ℕ) : S) * (a * a)) : ℝ) / ((n : ℝ) * n))
      atTop (𝓝 (p.linearValue (a * a))) := by
    simpa only [Function.comp_def, Nat.cast_mul] using
      (p.tendsto_linearValue (a * a)).comp tendsto_mul_self_atTop
  have hp := (p.tendsto_linearValue a).mul (p.tendsto_linearValue a)
  have upper (n : ℕ) : p.rank (((n * n : ℕ) : S) * (a * a)) ≤
      p.rank ((n : S) * a) * p.rank ((n : S) * a) := by
    have he : ((n * n : ℕ) : S) * (a * a) = ((n : S) * a) * ((n : S) * a) := by
      rw [Nat.cast_mul]
      ring
    rw [he]
    exact p.rank_mul_le _ _
  have lower (n : ℕ) : p.rank ((n : S) * a) * p.rank ((n : S) * a) ≤
      p.rank (((n * n : ℕ) : S) * (a * a)) + 2 * p.rank ((n : S) * a) + 1 := by
    have hf := p.rank_mono (p.mul (p.pred_rank_le ht ((n : S) * a))
      (p.pred_rank_le ht ((n : S) * a)))
    have he : ((n : S) * a) * ((n : S) * a) = ((n * n : ℕ) : S) * (a * a) := by
      rw [Nat.cast_mul]
      ring
    rw [← Nat.cast_mul, p.rank_nat, he] at hf
    have hr : p.rank ((n : S) * a) ≤ p.rank ((n : S) * a) - 1 + 1 := by omega
    have hpred := Nat.sub_le (p.rank ((n : S) * a)) 1
    nlinarith [Nat.mul_self_le_mul_self hr]
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto' hm hp
    intro n
    rw [div_mul_div_comm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast upper n
  · have hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
      exact (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0)).congr (fun n => one_div (n : ℝ))
    have he := (((p.tendsto_linearValue a).const_mul 2).add hz).mul hz
    simp only [mul_zero] at he
    have hm' := hm.add he
    rw [add_zero] at hm'
    apply le_of_tendsto_of_tendsto hp hm'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hid : (p.rank (((n * n : ℕ) : S) * (a * a)) : ℝ) / ((n : ℝ) * n) +
        (2 * ((p.rank ((n : S) * a) : ℝ) / n) + (n : ℝ)⁻¹) * (n : ℝ)⁻¹ =
        ((p.rank (((n * n : ℕ) : S) * (a * a)) : ℝ) +
          2 * p.rank ((n : S) * a) + 1) / ((n : ℝ) * n) := by
      field_simp [hn']
      ring
    rw [hid, div_mul_div_comm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast lower n

theorem linearValue_mul (ht : ∀ a b, p.Rel a b ∨ p.Rel b a) (a b : S) :
    p.linearValue (a * b) = p.linearValue a * p.linearValue b := by
  have h := p.linearValue_square ht (a + b)
  have he : (a + b) * (a + b) = (a * a + a * b) + (a * b + b * b) := by ring
  rw [he] at h
  simp only [p.linearValue_add ht, p.linearValue_square ht] at h
  nlinarith

noncomputable def pointOfTotal (ht : ∀ a b, p.Rel a b ∨ p.Rel b a) : Point p :=
  ⟨{ toFun := p.linearValue
     map_zero' := by simpa only [Nat.cast_zero] using p.linearValue_nat 0
     map_one' := by simpa only [Nat.cast_one] using p.linearValue_nat 1
     map_add' := p.linearValue_add ht
     map_mul' := p.linearValue_mul ht }, fun h => p.linearValue_mono h⟩

end Lemmata.TensorRank.Spectrum.StrassenPreorder
