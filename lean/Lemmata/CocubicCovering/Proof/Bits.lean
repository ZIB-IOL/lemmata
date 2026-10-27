module

public import Lemmata.CocubicCovering.Proof.Polynomial
public meta import Lemmata.CocubicCovering.Proof.Polynomial
public import Mathlib.Combinatorics.Colex

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringBits

open CoveringPolynomial
open scoped BigOperators

def decodeMask {n : ℕ} (mask : ℕ) : Vector n :=
  fun i => ofBool (mask.testBit i.val)

def bitSupport {n : ℕ} (v : Vector n) : Finset ℕ :=
  (Finset.univ.filter fun i : Fin n => toBool (v i)).image Fin.val

def encodeVector {n : ℕ} (v : Vector n) : ℕ :=
  ∑ i ∈ bitSupport v, 2 ^ i

@[simp] theorem mem_bitSupport {n : ℕ} (v : Vector n) (i : Fin n) :
    i.val ∈ bitSupport v ↔ toBool (v i) = true := by
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hji' : j = i := Fin.ext hji
    simpa only [hji'] using (Finset.mem_filter.mp hj).2
  · intro hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

theorem testBit_encodeVector {n : ℕ} (v : Vector n) (i : Fin n) :
    (encodeVector v).testBit i.val = toBool (v i) := by
  have hindices : (encodeVector v).bitIndices.toFinset = bitSupport v :=
    Finset.toFinset_bitIndices_sum_two_pow (bitSupport v)
  apply Bool.eq_iff_iff.mpr
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, hindices, mem_bitSupport]

@[simp] theorem decodeMask_encodeVector {n : ℕ} (v : Vector n) :
    decodeMask (encodeVector v) = v := by
  funext i
  simp only [decodeMask, testBit_encodeVector, ofBool_toBool]

theorem encodeVector_lt {n : ℕ} (v : Vector n) : encodeVector v < 2 ^ n := by
  apply Nat.geomSum_lt (by decide)
  intro i hi
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
  exact hji ▸ j.isLt

@[simp] theorem decodeMask_zero (n : ℕ) : decodeMask 0 = (0 : Vector n) := by
  funext i
  simp [decodeMask]

theorem decodeMask_xor {n : ℕ} (a b : ℕ) :
    decodeMask (a ^^^ b) = (decodeMask a : Vector n) + decodeMask b := by
  funext i
  simp only [decodeMask, Nat.testBit_xor, ofBool_xor, Pi.add_apply]

@[simp] theorem encodeVector_zero (n : ℕ) : encodeVector (0 : Vector n) = 0 := by
  have hzero : CoveringPolynomial.toBool (0 : Field) = false := by
    simpa only [ofBool_false] using toBool_ofBool false
  simp [encodeVector, bitSupport, hzero]

@[simp] theorem encodeVector_eq_zero_iff {n : ℕ} (v : Vector n) :
    encodeVector v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hv := decodeMask_encodeVector v
    rw [h, decodeMask_zero] at hv
    exact hv.symm
  · rintro rfl
    exact encodeVector_zero n

theorem encodeVector_ne_zero_iff {n : ℕ} (v : Vector n) :
    encodeVector v ≠ 0 ↔ v ≠ 0 :=
  not_congr (encodeVector_eq_zero_iff v)

theorem encodeVector_injective (n : ℕ) :
    Function.Injective (encodeVector : Vector n → ℕ) :=
  Function.LeftInverse.injective decodeMask_encodeVector

theorem exists_bounded_mask {n : ℕ} (v : Vector n) :
    ∃ mask < 2 ^ n, decodeMask mask = v :=
  ⟨encodeVector v, encodeVector_lt v, decodeMask_encodeVector v⟩

theorem encodeVector_decodeMask {n mask : ℕ} (hmask : mask < 2 ^ n) :
    encodeVector (decodeMask mask : Vector n) = mask := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hbit := testBit_encodeVector (decodeMask mask : Vector n) ⟨i, hi⟩
    simpa only [decodeMask, toBool_ofBool] using hbit
  · have hpow : 2 ^ n ≤ 2 ^ i :=
      Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow ((encodeVector_lt (decodeMask mask : Vector n)).trans_le hpow),
      Nat.testBit_lt_two_pow (hmask.trans_le hpow)]

theorem decodeMask_eq_zero_iff {n mask : ℕ} (hmask : mask < 2 ^ n) :
    (decodeMask mask : Vector n) = 0 ↔ mask = 0 := by
  constructor
  · intro h
    have he := congrArg encodeVector h
    rw [encodeVector_decodeMask hmask, encodeVector_zero] at he
    exact he
  · rintro rfl
    exact decodeMask_zero n

theorem decodeMask_mod_two_pow {n : ℕ} (mask : ℕ) :
    (decodeMask (mask % 2 ^ n) : Vector n) = decodeMask mask := by
  funext i
  simp [decodeMask, Nat.testBit_mod_two_pow, i.isLt]

theorem encodeVector_decodeMask_mod {n : ℕ} (mask : ℕ) :
    encodeVector (decodeMask mask : Vector n) = mask % 2 ^ n := by
  rw [← decodeMask_mod_two_pow mask]
  exact encodeVector_decodeMask (Nat.mod_lt _ (Nat.pow_pos (by decide)))

end Lemmata.CocubicCovering.CoveringBits
