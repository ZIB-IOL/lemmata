module

public import Lemmata.TensorRank.Proof.ProfileGrowth
public import Lemmata.TensorRank.Proof.PowerBounds
public import Mathlib.Data.Finset.Card

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

namespace Lemmata.TensorRank.Profile

variable {m : ℕ}

def Positive (a : Fin m → ℕ) : Prop := ∀ i, 1 ≤ a i

def Nonnegative (P : (Fin m → ℕ) → ℝ) : Prop := ∀ a, Positive a → 0 ≤ P a

def Concavity (P : (Fin m → ℕ) → ℝ) : Prop :=
  ∀ a, Positive a → ∀ j b, 1 ≤ b →
    P (Function.update a j b) + P (Function.update a j (b + 2)) ≤
      2 * P (Function.update a j (b + 1))

def Tripling (P : (Fin m → ℕ) → ℝ) : Prop :=
  ∀ a, Positive a → ∀ j b, 1 ≤ b →
    3 * P (Function.update a j b) ≤
      P (Function.update a j (3 * b + ∑ i ∈ Finset.univ.erase j, (a i - 1)))

theorem coordinate_step {P : (Fin m → ℕ) → ℝ}
    (hP : Nonnegative P) (hc : Concavity P) (ht : Tripling P)
    (a : Fin m → ℕ) (ha : Positive a) (j : Fin m) (n : ℕ) (hn : 1 ≤ n)
    (haj : a j = n) (hbound : ∀ i, a i ≤ n + 1) :
    (1 + 2 / (((m + 1) * n : ℕ) : ℝ)) * P a ≤ P (Function.update a j (n + 1)) := by
  let g : ℕ → ℝ := fun b => P (Function.update a j b)
  have hgn : g n = P a := by simp only [g, ← haj, Function.update_eq_self]
  have hs : (∑ i ∈ Finset.univ.erase j, (a i - 1)) ≤ (m - 1) * n := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.erase j, n :=
        Finset.sum_le_sum (fun i _ => by have := hbound i; omega)
      _ = _ := by simp
  have hK : 2 * n + ∑ i ∈ Finset.univ.erase j, (a i - 1) ≤ (m + 1) * n := by
    have he : 2 * n + (m - 1) * n = (m + 1) * n := by
      rw [show m + 1 = (m - 1) + 2 by have := j.isLt; omega]
      ring
    exact (Nat.add_le_add_left hs _).trans_eq he
  have h := step_of_displacement_bound (g := g) (hc a ha j)
    n (∑ i ∈ Finset.univ.erase j, (a i - 1)) ((m + 1) * n) hn
    (by rw [hgn]; exact hP a ha) (ht a ha j n hn) hK
  simpa only [hgn] using h

def raised (n : ℕ) (A : Finset (Fin m)) : Fin m → ℕ :=
  fun i => if i ∈ A then n + 1 else n

theorem raised_positive (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin m)) : Positive (raised n A) := by
  intro i
  unfold raised
  split <;> omega

theorem partial_diagonal_step {P : (Fin m → ℕ) → ℝ}
    (hP : Nonnegative P) (hc : Concavity P) (ht : Tripling P)
    (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin m)) :
    (1 + 2 / (((m + 1) * n : ℕ) : ℝ)) ^ A.card * P (fun _ => n) ≤ P (raised n A) := by
  induction A using Finset.induction_on with
  | empty =>
      have he : raised n (∅ : Finset (Fin m)) = (fun _ => n) := by
        funext i
        simp [raised]
      rw [he]
      simp
  | @insert j A hj ih =>
      let f : ℝ := 1 + 2 / (((m + 1) * n : ℕ) : ℝ)
      have hf : 0 ≤ f := by dsimp [f]; positivity
      have hs := coordinate_step hP hc ht (raised n A) (raised_positive n hn A) j n hn
        (by simp [raised, hj]) (fun i => by unfold raised; split <;> omega)
      have he : Function.update (raised n A) j (n + 1) = raised n (insert j A) := by
        funext i
        by_cases hi : i = j <;> simp [raised, hi]
      rw [he] at hs
      calc
        _ = f * (f ^ A.card * P (fun _ => n)) := by
          rw [Finset.card_insert_of_notMem hj, pow_succ]
          ring
        _ ≤ f * P (raised n A) := mul_le_mul_of_nonneg_left ih hf
        _ ≤ _ := hs

theorem diagonal_step {P : (Fin m → ℕ) → ℝ}
    (hP : Nonnegative P) (hc : Concavity P) (ht : Tripling P)
    (n : ℕ) (hn : 1 ≤ n) :
    (1 + 2 / (((m + 1) * n : ℕ) : ℝ)) ^ m * P (fun _ => n) ≤ P (fun _ => n + 1) := by
  have he : raised n (Finset.univ : Finset (Fin m)) = (fun _ => n + 1) := by
    funext i
    simp [raised]
  simpa only [Finset.card_univ, Fintype.card_fin, he]
    using partial_diagonal_step hP hc ht n hn Finset.univ

theorem diagonal_factor (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ (2 * (m : ℝ) / (m + 1)) ≤
      (1 + 2 / (((m + 1) * n : ℕ) : ℝ)) ^ m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk : (1 : ℝ) ≤ ((m : ℝ) + 1) / 2 := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h := one_add_mul_self_le_rpow_one_add
    (s := 2 / (((m : ℝ) + 1) * n)) (by
      have hs : (0 : ℝ) ≤ 2 / (((m : ℝ) + 1) * n) := by positivity
      linarith) hk
  have he : 1 + ((m : ℝ) + 1) / 2 * (2 / (((m : ℝ) + 1) * n)) = 1 + 1 / n := by
    field_simp
  rw [he] at h
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + 1 / (n : ℝ)) h
    (show 0 ≤ 2 * (m : ℝ) / (m + 1) by positivity)
  rw [← Real.rpow_mul (by positivity)] at hh
  have hp : (((m : ℝ) + 1) / 2) * (2 * m / (m + 1)) = m := by field_simp
  rw [hp, Real.rpow_natCast] at hh
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hh

theorem diagonal_growth {P : (Fin m → ℕ) → ℝ}
    (hm : 1 ≤ m) (hP : Nonnegative P) (hc : Concavity P) (ht : Tripling P)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (2 * (m : ℝ) / (m + 1)) * P (fun _ => 1) ≤ P (fun _ => n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      let α : ℝ := 2 * m / (m + 1)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have he : (1 + 1 / (n : ℝ)) * n = n + 1 := by field_simp
      have hp : (1 + 1 / (n : ℝ)) ^ α * (n : ℝ) ^ α = ((n : ℝ) + 1) ^ α := by
        rw [← Real.mul_rpow (by positivity) hn0.le, he]
      calc
        _ = (1 + 1 / (n : ℝ)) ^ α * ((n : ℝ) ^ α * P (fun _ => 1)) := by
          rw [← mul_assoc, hp, Nat.cast_add, Nat.cast_one]
        _ ≤ (1 + 1 / (n : ℝ)) ^ α * P (fun _ => n) :=
          mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg (by positivity) _)
        _ ≤ (1 + 2 / (((m + 1) * n : ℕ) : ℝ)) ^ m * P (fun _ => n) :=
          mul_le_mul_of_nonneg_right (diagonal_factor hm n hn) (hP _ (fun _ => hn))
        _ ≤ _ := diagonal_step hP hc ht n hn

theorem exponent_le {P : (Fin m → ℕ) → ℝ}
    (hm : 1 ≤ m) (hP : Nonnegative P) (hc : Concavity P) (ht : Tripling P)
    (hunit : 1 ≤ P (fun _ => 1)) (β : ℝ) (hβ : 0 ≤ β)
    (hupper : ∀ n : ℕ, 1 ≤ n →
      P (fun _ => n) ≤ ((1 + m * (n - 1) : ℕ) : ℝ) ^ β) :
    2 * (m : ℝ) / (m + 1) ≤ β := by
  let α : ℝ := 2 * m / (m + 1)
  have hb (n : ℕ) (hn : 1 ≤ n) :
      (n : ℝ) ^ α ≤ ((m : ℝ) + 1) ^ β * (n : ℝ) ^ β := by
    have hs : 1 + m * (n - 1) ≤ (m + 1) * n := by
      have hh : m * (n - 1) ≤ m * n := Nat.mul_le_mul_left m (Nat.sub_le _ _)
      nlinarith
    calc
      _ ≤ (n : ℝ) ^ α * P (fun _ => 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit (Real.rpow_nonneg (by positivity) α)
      _ ≤ P (fun _ => n) := diagonal_growth hm hP hc ht n hn
      _ ≤ ((1 + m * (n - 1) : ℕ) : ℝ) ^ β := hupper n hn
      _ ≤ (((m + 1) * n : ℕ) : ℝ) ^ β :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hs) hβ
      _ = _ := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.mul_rpow (by positivity) (by positivity)]
  have hp : (2 : ℝ) ^ α ≤ (2 : ℝ) ^ β := by
    apply le_of_polynomial_power_bound (by positivity) (by positivity)
      (((m : ℝ) + 1) ^ β) (Real.rpow_pos_of_pos (by positivity) _) 0
    intro q _
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_zero, mul_one,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
      using hb (2 ^ q) (by have := pow_pos (by decide : 0 < (2 : ℕ)) q; omega)
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hp

end Lemmata.TensorRank.Profile
