module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option autoImplicit false

open Classical

namespace Lemmata.TensorRank.Spectrum

structure StrassenPreorder (S : Type*) [CommSemiring S] where
  Rel : S → S → Prop
  refl : ∀ a, Rel a a
  trans : ∀ {a b c}, Rel a b → Rel b c → Rel a c
  zero_le : ∀ a, Rel 0 a
  nat_iff : ∀ m n : ℕ, Rel m n ↔ m ≤ n
  add : ∀ {a b c d}, Rel a b → Rel c d → Rel (a + c) (b + d)
  mul : ∀ {a b c d}, Rel a b → Rel c d → Rel (a * c) (b * d)
  cofinal : ∀ a b, b ≠ 0 → ∃ n : ℕ, Rel a (n * b)

namespace StrassenPreorder

variable {S : Type*} [CommSemiring S] (p : StrassenPreorder S)

include p in
theorem one_ne_zero : (1 : S) ≠ 0 := by
  intro h
  have he : p.Rel (1 : ℕ) (0 : ℕ) := by
    simpa only [Nat.cast_one, Nat.cast_zero, h] using p.refl (0 : S)
  have := (p.nat_iff 1 0).mp he
  omega

theorem bounded (a : S) : ∃ n : ℕ, p.Rel a n := by
  obtain ⟨n, h⟩ := p.cofinal a 1 p.one_ne_zero
  exact ⟨n, by simpa only [mul_one] using h⟩

noncomputable def rank (a : S) : ℕ := Nat.find (p.bounded a)

noncomputable def asymptoticRank (a : S) : ℝ :=
  ⨅ n : ℕ, (p.rank (a ^ (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)

end StrassenPreorder

def Point {S : Type*} [CommSemiring S] (p : StrassenPreorder S) :=
  {f : S →+* ℝ // ∀ {a b}, p.Rel a b → f a ≤ f b}

instance {S : Type*} [CommSemiring S] {p : StrassenPreorder S} :
    CoeFun (Point p) (fun _ => S → ℝ) := ⟨fun f => f.val⟩

end Lemmata.TensorRank.Spectrum
