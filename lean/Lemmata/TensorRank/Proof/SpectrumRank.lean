module

public import Lemmata.TensorRank.Def.Spectrum
public import Mathlib.Analysis.Subadditive

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology
open Classical

namespace Lemmata.TensorRank.Spectrum

variable {S : Type*} [CommSemiring S]

namespace StrassenPreorder

variable (p : StrassenPreorder S)

theorem rel_rank (a : S) : p.Rel a (p.rank a) := Nat.find_spec (p.bounded a)

theorem rank_le_iff (a : S) (n : ℕ) : p.rank a ≤ n ↔ p.Rel a n := by
  constructor
  · intro h
    exact p.trans (p.rel_rank a) ((p.nat_iff _ _).mpr h)
  · intro h
    exact Nat.find_le (p := fun m : ℕ => p.Rel a (m : S)) h

theorem rank_mono {a b : S} (h : p.Rel a b) : p.rank a ≤ p.rank b :=
  (p.rank_le_iff _ _).mpr (p.trans h (p.rel_rank b))

@[simp] theorem rank_nat (n : ℕ) : p.rank (n : S) = n :=
  le_antisymm ((p.rank_le_iff _ _).mpr (p.refl _)) ((p.nat_iff _ _).mp (p.rel_rank _))

theorem rank_add_le (a b : S) : p.rank (a + b) ≤ p.rank a + p.rank b := by
  apply (p.rank_le_iff _ _).mpr
  simpa only [Nat.cast_add] using p.add (p.rel_rank a) (p.rel_rank b)

theorem rank_mul_le (a b : S) : p.rank (a * b) ≤ p.rank a * p.rank b := by
  apply (p.rank_le_iff _ _).mpr
  simpa only [Nat.cast_mul] using p.mul (p.rel_rank a) (p.rel_rank b)

theorem pow_mono {a b : S} (h : p.Rel a b) (n : ℕ) : p.Rel (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using p.refl (1 : S)
  | succ n ih => simpa only [pow_succ] using p.mul ih h

theorem asymptoticRank_nonneg (a : S) : 0 ≤ p.asymptoticRank a := by
  apply le_ciInf
  intro n
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem asymptoticRank_le_root (a : S) (n : ℕ) :
    p.asymptoticRank a ≤ (p.rank (a ^ (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹) :=
  ciInf_le ⟨0, by rintro _ ⟨m, rfl⟩; exact Real.rpow_nonneg (Nat.cast_nonneg _) _⟩ n

theorem asymptoticRank_le_rank (a : S) : p.asymptoticRank a ≤ p.rank a := by
  simpa only [Nat.zero_add, pow_one, Nat.cast_zero, zero_add, inv_one, Real.rpow_one] using
    p.asymptoticRank_le_root a 0

theorem asymptoticRank_mono {a b : S} (h : p.Rel a b) :
    p.asymptoticRank a ≤ p.asymptoticRank b := by
  apply ciInf_mono ⟨0, by rintro _ ⟨m, rfl⟩; exact Real.rpow_nonneg (Nat.cast_nonneg _) _⟩
  intro n
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast p.rank_mono (p.pow_mono h (n + 1))
  · positivity

end StrassenPreorder

namespace Point

variable {p : StrassenPreorder S} (f : Point p)

theorem nonneg (a : S) : 0 ≤ f a := by
  simpa only [map_zero] using f.prop (p.zero_le a)

theorem le_rank (a : S) : f a ≤ p.rank a := by
  simpa only [map_natCast] using f.prop (p.rel_rank a)

theorem le_asymptoticRank (a : S) : f a ≤ p.asymptoticRank a := by
  apply le_ciInf
  intro n
  have h : f a ^ (n + 1) ≤ (p.rank (a ^ (n + 1)) : ℝ) := by
    simpa only [map_pow] using f.le_rank (a ^ (n + 1))
  have he := Real.rpow_le_rpow (pow_nonneg (f.nonneg a) _) h
    (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n + 1))
  have hid : ((f a) ^ (n + 1)) ^ ((n + 1 : ℝ)⁻¹) = f a := by
    simpa only [Nat.cast_succ, Nat.succ_eq_add_one] using
      Real.pow_rpow_inv_natCast (f.nonneg a) (Nat.succ_ne_zero n)
  rwa [hid] at he

end Point
end Lemmata.TensorRank.Spectrum
