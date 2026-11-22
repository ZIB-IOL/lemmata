module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

/-! Parseval for the unnormalized evaluations at the m odd roots of unity
of order dividing 2m, including deterministic sign rows of the Bell model. -/

@[expose] public section

namespace Lemmata.SymmetricBellFacetLifting.Recovery.BellFourier

open scoped BigOperators ComplexConjugate
open Finset Complex

variable {m : ℕ} [NeZero m]

/-- A half-step twist at the positive representative of a setting. -/
noncomputable def twist (j : ZMod m) : ℂ :=
  Complex.exp (((Real.pi * j.val / m : ℝ) : ℂ) * Complex.I)

/-- The Bell transform in ordinary setting labels j=0,...,m-1. The frequency
label k=0,...,m-1 denotes the odd harmonic 2k+1. -/
noncomputable def amplitude (a : ZMod m → ℂ) (k : ZMod m) : ℂ :=
  ∑ j, a j * Complex.exp (((Real.pi * (2 * k.val + 1) * j.val / m : ℝ) : ℂ) * Complex.I)

private theorem char_conj (x : ZMod m) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

private theorem char_orth (j l : ZMod m) :
    (∑ k, ZMod.stdAddChar (j*k) * conj (ZMod.stdAddChar (l*k))) =
      if j = l then (m : ℂ) else 0 := by
  simp_rw [char_conj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  by_cases h : j = l
  · subst l
    simp [ZMod.card]
  · simp only [h, ↓reduceIte]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m (sub_ne_zero.mpr h))

private noncomputable def dftPlus (f : ZMod m → ℂ) (k : ZMod m) : ℂ :=
  ∑ j, f j * ZMod.stdAddChar (j*k)

private theorem dftPlus_parseval (f : ZMod m → ℂ) :
    ∑ k, ‖dftPlus f k‖ ^ 2 = (m : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  have hexp (k : ZMod m) : dftPlus f k * conj (dftPlus f k) =
      ∑ j, ∑ l, (f j * conj (f l)) *
        (ZMod.stdAddChar (j*k) * conj (ZMod.stdAddChar (l*k))) := by
    simp only [dftPlus, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have h : ∑ k, dftPlus f k * conj (dftPlus f k) =
      (m : ℂ) * ∑ j, f j * conj (f j) := calc
    _ = ∑ j, ∑ l, ∑ k, (f j * conj (f l)) *
        (ZMod.stdAddChar (j*k) * conj (ZMod.stdAddChar (l*k))) := by
      simp_rw [hexp]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      simp_rw [← Finset.mul_sum, char_orth]
      simp [Finset.mul_sum, mul_comm]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

private theorem twist_norm (j : ZMod m) : ‖twist j‖ = 1 := by
  simp [twist, Complex.norm_exp]

private theorem amplitude_dft (a : ZMod m → ℂ) (k : ZMod m) :
    amplitude a k = dftPlus (fun j => a j * twist j) k := by
  unfold amplitude dftPlus
  apply Finset.sum_congr rfl
  intro j _
  have hh := ZMod.stdAddChar_coe (N := m) ((j.val : ℤ) * (k.val : ℤ))
  push_cast at hh
  simp only [ZMod.natCast_zmod_val] at hh
  dsimp only [twist]
  rw [hh, mul_assoc (a j) (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Parseval's identity with the unnormalized Bell convention, on every
positive number of settings and for every complex one-party row. -/
theorem parseval (a : ZMod m → ℂ) :
    ∑ k, ‖amplitude a k‖ ^ 2 = (m : ℝ) * ∑ j, ‖a j‖ ^ 2 := by
  simp_rw [amplitude_dft]
  rw [dftPlus_parseval]
  simp [twist_norm]

/-- A deterministic row with Boolean outcomes stored as the signs ±1. -/
def signs (s : ZMod m → Bool) (j : ZMod m) : ℂ := if s j then 1 else -1

/-- Every deterministic strategy has total odd-harmonic energy exactly m². -/
theorem signs_parseval (s : ZMod m → Bool) :
    ∑ k, ‖amplitude (signs s) k‖ ^ 2 = (m : ℝ) ^ 2 := by
  rw [parseval]
  have h (j : ZMod m) : ‖signs s j‖ = 1 := by simp [signs, apply_ite norm]
  simp [h, ZMod.card, pow_two]

/-- Index of the conjugate odd root. -/
def reflect (k : ZMod m) : ZMod m := -1 - k

omit [NeZero m] in
@[simp] theorem reflect_reflect (k : ZMod m) : reflect (reflect k) = k := by
  unfold reflect
  ring

private theorem twist_sq (j : ZMod m) : twist j ^ 2 = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, twist, pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem twist_conj (j : ZMod m) : conj (twist j) = twist j * conj (ZMod.stdAddChar j) := by
  have h : twist j * conj (twist j) = 1 := by rw [Complex.mul_conj', twist_norm]; norm_num
  rw [← twist_sq, map_pow]
  calc
    _ = (twist j * conj (twist j)) * conj (twist j) := by rw [h, one_mul]
    _ = _ := by ring

/-- The two odd modes related by k ↦ -1-k have conjugate amplitudes
on an actual real sign row. -/
theorem conjugate_amplitude (s : ZMod m → Bool) (k : ZMod m) :
    conj (amplitude (signs s) k) = amplitude (signs s) (reflect k) := by
  simp only [amplitude_dft, dftPlus, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hk : j * reflect k = -j + -(j*k) := by unfold reflect; ring
  have hs : conj (signs s j) = signs s j := by cases hh : s j <;> simp [signs, hh]
  rw [hk, AddChar.map_add_eq_mul, ← char_conj, ← char_conj, hs, twist_conj]
  ring

theorem amplitude_reflect_norm (s : ZMod m → Bool) (k : ZMod m) :
    ‖amplitude (signs s) (reflect k)‖ = ‖amplitude (signs s) k‖ := by
  rw [← conjugate_amplitude, Complex.norm_conj]

end Lemmata.SymmetricBellFacetLifting.Recovery.BellFourier
