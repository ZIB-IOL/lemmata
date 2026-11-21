module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Int.Basic

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

def admissible (n : ℕ) : Prop := n % 15 = 1 ∨ n % 15 = 6

instance (n : ℕ) : Decidable (admissible n) := by
  unfold admissible
  infer_instance

/-- The orders used in the construction, including the empty and single-block
systems used as ingredients. -/
def constructible (n : ℕ) : Prop :=
  admissible n ∧ (n = 1 ∨ n = 6 ∨ n = 31 ∨ n = 66 ∨ n = 76 ∨ 81 < n)

instance (n : ℕ) : Decidable (constructible n) := by
  unfold constructible
  infer_instance

/-- Among four consecutive candidates, each of 5, 7, and 11 rules out at most one. -/
private theorem coprimeCandidate (a : ℕ) (ha : a % 6 = 1 ∨ a % 6 = 5) :
    ∃ j ≤ 3, (a+6*j).Coprime 2310 := by
  by_contra! bad
  have misses (j : ℕ) (hj : j ≤ 3) :
      5 ∣ a+6*j ∨ 7 ∣ a+6*j ∨ 11 ∣ a+6*j := by
    by_contra! h
    apply bad j hj
    have unit (p : ℕ) (prime : p.Prime) (hn : ¬ p ∣ a+6*j) :
        (a+6*j).Coprime p := (prime.coprime_iff_not_dvd.mpr hn).symm
    change (a+6*j).Coprime (2*3*5*7*11)
    simp only [Nat.coprime_mul_iff_right]
    exact ⟨⟨⟨⟨unit 2 (by decide) (by omega), unit 3 (by decide) (by omega)⟩,
      unit 5 (by decide) h.1⟩, unit 7 (by decide) h.2.1⟩, unit 11 (by decide) h.2.2⟩
  have h₀ := misses 0 (by decide)
  have h₁ := misses 1 (by decide)
  have h₂ := misses 2 (by decide)
  have h₃ := misses 3 (by decide)
  omega

/-- In n = 65t + 15r + e, increasing t by 6 and decreasing r by 26
preserves n. Four consecutive choices suffice for coprimality. -/
theorem reduceUpper {n : ℕ} (bound : 8726 ≤ n) (admiss : admissible n) :
    ∃ t r e : ℕ, n = 65*t+15*r+e ∧ (e = 1 ∨ e = 6) ∧ r ≤ t ∧
      13 ≤ t ∧ t.Coprime 2310 ∧ constructible (5*t+e) ∧ constructible (15*r+e) ∧
      13*(5*t+e) < n ∧ 15*r+e ≤ 1641 := by
  obtain ⟨e, s, m, shape⟩ : ∃ e s m : ℕ,
      (n % 15 = 1 ∧ e = 6 ∧ s = 5 ∧ m = 6) ∨
      (n % 15 = 6 ∧ e = 1 ∧ s = 1 ∧ m = 5) := by
    rcases admiss with h | h
    · exact ⟨6, 5, 6, Or.inl ⟨h, rfl, rfl, rfl⟩⟩
    · exact ⟨1, 1, 5, Or.inr ⟨h, rfl, rfl, rfl⟩⟩
  let u := (n-(65*s+15*m+e))/15
  let a := s+6*(u/26-3)
  have residue : a % 6 = 1 ∨ a % 6 = 5 := by
    rcases shape with ⟨_,rfl,rfl,rfl⟩ | ⟨_,rfl,rfl,rfl⟩ <;> dsimp [a] <;> omega
  obtain ⟨j, hj, cop⟩ := coprimeCandidate a residue
  let t := a+6*j
  let r := m+u%26+26*(3-j)
  refine ⟨t, r, e, ?_, ?_, ?_, ?_, cop, ?_, ?_, ?_, ?_⟩ <;>
    rcases shape with ⟨hn,rfl,rfl,rfl⟩ | ⟨hn,rfl,rfl,rfl⟩ <;>
    dsimp [constructible, admissible, t, r, a, u] at * <;> omega

end Lemmata.SteinerSixSpectrum
