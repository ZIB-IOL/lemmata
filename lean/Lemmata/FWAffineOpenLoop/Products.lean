module

public import Lemmata.FWAffineOpenLoop.Statement
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# Products of step sizes (Lemmas 3.3 and 3.5)

For `η_t = ℓ/(t + ℓ)` with `ℓ ∈ ℕ`, `∏_{i=S}^{t} (1 - η_i) ≤ ((S - 1 + ℓ)/(t + ℓ))^ℓ` follows by
induction from Bernoulli's inequality, and `∑_{i=S}^{t} 1/i ≤ ℓ/S + log((t + ℓ)/(S - 1 + ℓ))`
bounds the correction `∏ (1 + ε/i)` in Lemma 3.5.
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FWOpenLoop

theorem eta_nat (ℓ i : ℕ) : eta ℓ (i : ℤ) = (ℓ : ℝ) / ((i : ℝ) + ℓ) := by
  simp [eta]

theorem eta_pred (ℓ i : ℕ) : eta ℓ ((i : ℤ) - 1) = (ℓ : ℝ) / ((i : ℝ) - 1 + ℓ) := by
  simp [eta]

/-- `η_t/η_{S-1} = (S - 1 + ℓ)/(t + ℓ)`. -/
theorem eta_ratio (ℓ S t : ℕ) (hℓ : 1 ≤ ℓ) (hS : 1 ≤ S) :
    eta ℓ t / eta ℓ ((S : ℤ) - 1) = ((S : ℝ) - 1 + ℓ) / (t + ℓ) := by
  rw [eta_nat, eta_pred]
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have h1 : (0 : ℝ) < (t : ℝ) + ℓ := by positivity
  have h2 : (0 : ℝ) < (S : ℝ) - 1 + ℓ := by linarith
  field_simp

/-- Bernoulli: `(j + 1)/(j + 1 + ℓ) ≤ ((j + ℓ)/(j + 1 + ℓ))^ℓ` for `j ≥ 0`. -/
theorem bernoulli_step (ℓ : ℕ) {j : ℝ} (hj : 0 ≤ j) :
    (j + 1) / (j + 1 + ℓ) ≤ ((j + ℓ) / (j + 1 + ℓ)) ^ ℓ := by
  have hpos : 0 < j + 1 + ℓ := by positivity
  have hle : (-2 : ℝ) ≤ -1 / (j + 1 + ℓ) := by
    rw [le_div_iff₀ hpos]; have : (0 : ℝ) ≤ ℓ := by positivity
    linarith
  have h := one_add_mul_le_pow hle ℓ
  have e1 : 1 + (ℓ : ℝ) * (-1 / (j + 1 + ℓ)) = (j + 1) / (j + 1 + ℓ) := by field_simp; ring
  have e2 : 1 + -1 / (j + 1 + ℓ) = (j + ℓ) / (j + 1 + ℓ) := by field_simp; ring
  rw [e1, e2] at h
  exact h

/-- **Lemma 3.3**, in closed form. -/
theorem product_bound_closed (ℓ S : ℕ) (hℓ : 1 ≤ ℓ) (hS : 1 ≤ S) :
    ∀ t, S ≤ t → ∏ i ∈ Finset.Icc S t, (1 - eta ℓ i) ≤ (((S : ℝ) - 1 + ℓ) / (t + ℓ)) ^ ℓ := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.prod_singleton, eta_nat]
    have h := bernoulli_step ℓ (show (0 : ℝ) ≤ (S : ℝ) - 1 by linarith)
    have e1 : 1 - (ℓ : ℝ) / ((S : ℝ) + ℓ) = ((S : ℝ) - 1 + 1) / ((S : ℝ) - 1 + 1 + ℓ) := by
      have : (0 : ℝ) < (S : ℝ) + ℓ := by positivity
      field_simp; ring
    have e2 : ((S : ℝ) - 1 + ℓ) / ((S : ℝ) - 1 + 1 + ℓ) = ((S : ℝ) - 1 + ℓ) / ((S : ℝ) + ℓ) := by
      ring_nf
    rw [e1]; rw [e2] at h; exact h
  | succ t ht ih =>
    rw [Finset.prod_Icc_succ_top (by omega), eta_nat]
    have ht0 : (0 : ℝ) ≤ t := by positivity
    have hpos : (0 : ℝ) < (t : ℝ) + ℓ := by positivity
    have hpos1 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) + ℓ := by positivity
    have hfac : 1 - (ℓ : ℝ) / (((t + 1 : ℕ) : ℝ) + ℓ) = ((t : ℝ) + 1) / ((t : ℝ) + 1 + ℓ) := by
      push_cast; field_simp; ring
    have hb := bernoulli_step ℓ ht0
    have hS0 : (0 : ℝ) ≤ ((S : ℝ) - 1 + ℓ) / (t + ℓ) := by
      apply div_nonneg _ hpos.le; linarith
    rw [hfac]
    calc (∏ i ∈ Finset.Icc S t, (1 - eta ℓ i)) * (((t : ℝ) + 1) / ((t : ℝ) + 1 + ℓ))
        ≤ (((S : ℝ) - 1 + ℓ) / (t + ℓ)) ^ ℓ * (((t : ℝ) + 1) / ((t : ℝ) + 1 + ℓ)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ (((S : ℝ) - 1 + ℓ) / (t + ℓ)) ^ ℓ * (((t : ℝ) + ℓ) / ((t : ℝ) + 1 + ℓ)) ^ ℓ :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (((S : ℝ) - 1 + ℓ) / (((t + 1 : ℕ) : ℝ) + ℓ)) ^ ℓ := by
          rw [← mul_pow]; congr 1; push_cast; field_simp

/-- `∑_{i=S}^{t} (1/i - 1/(i + ℓ)) ≤ ℓ (1/S - 1/(t + 1))`. -/
theorem sum_inv_sub_le (ℓ S : ℕ) (hℓ : 1 ≤ ℓ) (hS : 1 ≤ S) :
    ∀ t, S ≤ t → ∑ i ∈ Finset.Icc S t, (1 / (i : ℝ) - 1 / ((i : ℝ) + ℓ)) ≤
      ℓ * (1 / (S : ℝ) - 1 / ((t : ℝ) + 1)) := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have key : ∀ i : ℕ, 1 ≤ i →
      1 / (i : ℝ) - 1 / ((i : ℝ) + ℓ) ≤ ℓ * (1 / (i : ℝ) - 1 / ((i : ℝ) + 1)) := by
    intro i hi
    have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hi0 : (0 : ℝ) < i := by linarith
    have e1 : 1 / (i : ℝ) - 1 / ((i : ℝ) + ℓ) = ℓ / ((i : ℝ) * ((i : ℝ) + ℓ)) := by
      field_simp; ring
    have e2 : (ℓ : ℝ) * (1 / (i : ℝ) - 1 / ((i : ℝ) + 1)) = ℓ / ((i : ℝ) * ((i : ℝ) + 1)) := by
      field_simp; ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]; exact key S hS
  | succ t ht ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := key (t + 1) (by omega)
    push_cast at this ⊢
    have e : (ℓ : ℝ) * (1 / (S : ℝ) - 1 / ((t : ℝ) + 1)) +
        ℓ * (1 / ((t : ℝ) + 1) - 1 / ((t : ℝ) + 1 + 1)) =
        ℓ * (1 / (S : ℝ) - 1 / ((t : ℝ) + 1 + 1)) := by ring
    linarith

/-- `∑_{i=S}^{t} 1/(i + ℓ) ≤ log((t + ℓ)/(S - 1 + ℓ))`. -/
theorem sum_inv_le_log (ℓ S : ℕ) (hℓ : 1 ≤ ℓ) (hS : 1 ≤ S) :
    ∀ t, S ≤ t → ∑ i ∈ Finset.Icc S t, 1 / ((i : ℝ) + ℓ) ≤
      Real.log (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)) := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have key : ∀ j : ℝ, 1 < j → 1 / j ≤ Real.log (j / (j - 1)) := by
    intro j hj
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < j / (j - 1) from
      div_pos (by linarith) (by linarith))
    rw [inv_div] at h
    have e : 1 - (j - 1) / j = 1 / j := by field_simp; ring
    linarith
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have := key ((S : ℝ) + ℓ) (by linarith)
    rwa [show (S : ℝ) + ℓ - 1 = (S : ℝ) - 1 + ℓ by ring] at this
  | succ t ht ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ht0 : (0 : ℝ) ≤ t := by positivity
    have := key (((t + 1 : ℕ) : ℝ) + ℓ) (by push_cast; linarith)
    have hpos1 : (0 : ℝ) < (S : ℝ) - 1 + ℓ := by linarith
    have hpos2 : (0 : ℝ) < (t : ℝ) + ℓ := by positivity
    have hlog : Real.log (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)) +
        Real.log ((((t + 1 : ℕ) : ℝ) + ℓ) / (((t + 1 : ℕ) : ℝ) + ℓ - 1)) =
        Real.log ((((t + 1 : ℕ) : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)) := by
      rw [← Real.log_mul (div_pos hpos2 hpos1).ne' (by
        push_cast; apply div_ne_zero <;> linarith)]
      congr 1
      push_cast
      have hne : (t : ℝ) + ℓ ≠ 0 := hpos2.ne'
      rw [show (t : ℝ) + 1 + ℓ - 1 = (t : ℝ) + ℓ by ring]
      field_simp
    linarith

/-- `∑_{i=S}^{t} 1/i ≤ ℓ/S + log((t + ℓ)/(S - 1 + ℓ))`. -/
theorem harmonic_tail (ℓ S t : ℕ) (hℓ : 1 ≤ ℓ) (hS : 1 ≤ S) (ht : S ≤ t) :
    ∑ i ∈ Finset.Icc S t, 1 / (i : ℝ) ≤ ℓ / S + Real.log (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)) := by
  have h1 := sum_inv_sub_le ℓ S hℓ hS t ht
  have h2 := sum_inv_le_log ℓ S hℓ hS t ht
  have hsplit : ∑ i ∈ Finset.Icc S t, 1 / (i : ℝ) =
      ∑ i ∈ Finset.Icc S t, (1 / (i : ℝ) - 1 / ((i : ℝ) + ℓ)) +
        ∑ i ∈ Finset.Icc S t, 1 / ((i : ℝ) + ℓ) := by
    rw [← Finset.sum_add_distrib]; congr 1; ext i; ring
  have h3 : (ℓ : ℝ) * (1 / (S : ℝ) - 1 / ((t : ℝ) + 1)) ≤ ℓ / S := by
    have : 0 ≤ (ℓ : ℝ) * (1 / ((t : ℝ) + 1)) := by positivity
    have e : (ℓ : ℝ) * (1 / (S : ℝ) - 1 / ((t : ℝ) + 1)) = ℓ / S - ℓ * (1 / ((t : ℝ) + 1)) := by
      ring
    linarith
  linarith

/-- `∏ (1 + a_i) ≤ exp(∑ a_i)` for `a_i ≥ 0`. -/
theorem prod_one_add_le_exp {s : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun i hi => by linarith [ha i hi])
  intro i _
  have := Real.add_one_le_exp (a i)
  linarith

/-- **Lemma 3.5**, in closed form. -/
theorem product_bound_eps_closed (ℓ S t : ℕ) (ε : ℝ) (hℓ : 1 ≤ ℓ) (hS : 1 ≤ S) (ht : S ≤ t)
    (hε : ε ∈ Set.Icc (0 : ℝ) ℓ) :
    ∏ i ∈ Finset.Icc S t, (1 - (1 - ε / ℓ) * eta ℓ i) ≤
      (((S : ℝ) - 1 + ℓ) / (t + ℓ)) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / S) := by
  obtain ⟨hε0, hεℓ⟩ := hε
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hfac : ∀ i ∈ Finset.Icc S t,
      1 - (1 - ε / ℓ) * eta ℓ i = (1 - eta ℓ i) * (1 + ε / (i : ℝ)) := by
    intro i hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast le_trans hS (Finset.mem_Icc.mp hi).1
    rw [eta_nat]
    have : (0 : ℝ) < (i : ℝ) + ℓ := by positivity
    field_simp; ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  have hP := product_bound_closed ℓ S hℓ hS t ht
  have hnn1 : 0 ≤ ∏ i ∈ Finset.Icc S t, (1 - eta ℓ i) := by
    apply Finset.prod_nonneg; intro i hi
    rw [eta_nat, sub_nonneg, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ i := by positivity
    linarith
  have hE : ∏ i ∈ Finset.Icc S t, (1 + ε / (i : ℝ)) ≤
      Real.exp (ε * ℓ / S) * (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)) ^ ε := by
    have h1 := prod_one_add_le_exp (s := Finset.Icc S t) (a := fun i => ε / (i : ℝ))
      (fun i _ => by positivity)
    have h2 : ∑ i ∈ Finset.Icc S t, ε / (i : ℝ) ≤
        ε * (ℓ / S + Real.log (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ))) := by
      have := harmonic_tail ℓ S t hℓ hS ht
      have e : ∑ i ∈ Finset.Icc S t, ε / (i : ℝ) = ε * ∑ i ∈ Finset.Icc S t, 1 / (i : ℝ) := by
        rw [Finset.mul_sum]; congr 1; ext i; ring
      rw [e]; exact mul_le_mul_of_nonneg_left this hε0
    have hq : 0 < ((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ) := by
      apply div_pos (by positivity); linarith
    calc ∏ i ∈ Finset.Icc S t, (1 + ε / (i : ℝ)) ≤ Real.exp (∑ i ∈ Finset.Icc S t, ε / (i : ℝ)) :=
          h1
      _ ≤ Real.exp (ε * (ℓ / S + Real.log (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)))) :=
          Real.exp_le_exp.mpr h2
      _ = Real.exp (ε * ℓ / S) * (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)) ^ ε := by
          rw [mul_add, Real.exp_add, Real.rpow_def_of_pos hq]
          congr 1 <;> ring_nf
  have hq0 : 0 < ((S : ℝ) - 1 + ℓ) / ((t : ℝ) + ℓ) := by
    apply div_pos (by linarith) (by positivity)
  calc (∏ i ∈ Finset.Icc S t, (1 - eta ℓ i)) * ∏ i ∈ Finset.Icc S t, (1 + ε / (i : ℝ))
      ≤ (((S : ℝ) - 1 + ℓ) / (t + ℓ)) ^ ℓ *
          (Real.exp (ε * ℓ / S) * (((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ)) ^ ε) :=
        mul_le_mul hP hE (Finset.prod_nonneg fun i _ => by positivity) (by positivity)
    _ = (((S : ℝ) - 1 + ℓ) / (t + ℓ)) ^ ((ℓ : ℝ) - ε) * Real.exp (ε * ℓ / S) := by
        rw [show ((t : ℝ) + ℓ) / ((S : ℝ) - 1 + ℓ) = (((S : ℝ) - 1 + ℓ) / (t + ℓ))⁻¹ by
          rw [inv_div], Real.inv_rpow hq0.le, Real.rpow_sub hq0, Real.rpow_natCast]
        field_simp

/-- `log((t + ℓ + 1)/(R + ℓ)) ≤ ∑_{j=R}^{t} 1/(j + ℓ)`. -/
theorem log_le_sum_inv (ℓ R : ℕ) (hℓ : 1 ≤ ℓ) :
    ∀ t, R ≤ t → Real.log (((t : ℝ) + ℓ + 1) / ((R : ℝ) + ℓ)) ≤
      ∑ j ∈ Finset.Icc R t, 1 / ((j : ℝ) + ℓ) := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have key : ∀ y : ℝ, 0 < y → Real.log ((y + 1) / y) ≤ 1 / y := by
    intro y hy
    have h := Real.log_le_sub_one_of_pos (show 0 < (y + 1) / y by positivity)
    have e : (y + 1) / y - 1 = 1 / y := by field_simp; ring
    linarith
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have := key ((R : ℝ) + ℓ) (by positivity)
    rwa [show (R : ℝ) + ℓ + 1 = ((R : ℝ) + ℓ) + 1 by ring]
  | succ t ht ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := key (((t + 1 : ℕ) : ℝ) + ℓ) (by positivity)
    have hpos1 : (0 : ℝ) < (R : ℝ) + ℓ := by positivity
    have hpos2 : (0 : ℝ) < (t : ℝ) + ℓ + 1 := by positivity
    have hlog : Real.log ((((t + 1 : ℕ) : ℝ) + ℓ + 1) / ((R : ℝ) + ℓ)) =
        Real.log (((t : ℝ) + ℓ + 1) / ((R : ℝ) + ℓ)) +
          Real.log (((((t + 1 : ℕ) : ℝ) + ℓ) + 1) / (((t + 1 : ℕ) : ℝ) + ℓ)) := by
      rw [← Real.log_mul (div_pos hpos2 hpos1).ne' (by push_cast; positivity)]
      congr 1
      push_cast
      have hne : (t : ℝ) + 1 + ℓ ≠ 0 := by positivity
      field_simp
      ring
    rw [hlog]
    linarith

/-- `(1 + 2/ℓ)^ℓ ≤ e²`, and more generally `(1 + 2/ℓ)^k ≤ e^{2k/ℓ}` for `k ≥ 0`. -/
theorem one_add_two_div_rpow_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {k : ℝ} (hk : 0 ≤ k) :
    (1 + 2 / (ℓ : ℝ)) ^ k ≤ Real.exp (2 * k / ℓ) := by
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓr : (0 : ℝ) < ℓ := by linarith
  have h1 : 1 + 2 / (ℓ : ℝ) ≤ Real.exp (2 / ℓ) := by
    have := Real.add_one_le_exp (2 / (ℓ : ℝ)); linarith
  calc (1 + 2 / (ℓ : ℝ)) ^ k ≤ (Real.exp (2 / ℓ)) ^ k :=
        Real.rpow_le_rpow (by positivity) h1 hk
    _ = Real.exp (2 * k / ℓ) := by rw [← Real.exp_mul]; ring_nf

end Lemmata.FWAffineOpenLoop
