module

public import Lemmata.ModifiedE8Bell.Reduction

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

/-- Integer dot product in eight coordinates. -/
def dot (x y : Vector) : ℤ := ∑ k, x k * y k

def envelope (q : Vector) : ℤ :=
  (∑ i, max 52 (6 * |dot (root i) q| - 52)) - 3 * dot q q

lemma matrix_row_sum (i : Setting) (b : Signing) :
    (∑ j, sign (b j) * fourMatrix i j) =
      3 * dot (root i) (sumRoot b) - 52 * sign (b i) := by
  simp only [fourMatrix, mul_sub, Finset.sum_sub_distrib]
  have hd : (∑ j, sign (b j) * (if i = j then (52 : ℤ) else 0)) = 52 * sign (b i) := by
    simp [mul_ite, eq_comm, mul_comm]
  rw [hd]
  apply congrArg (fun t : ℤ => t - 52 * sign (b i))
  simp only [dot, sumRoot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma fourBell_rows (a b : Signing) :
    fourBell a b = ∑ i, sign (a i) *
      (3 * dot (root i) (sumRoot b) - 52 * sign (b i)) := by
  unfold fourBell
  apply Finset.sum_congr rfl
  intro i _
  rw [← matrix_row_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma signed_pairing (b : Signing) :
    (∑ i, sign (b i) * dot (root i) (sumRoot b)) = dot (sumRoot b) (sumRoot b) := by
  simp only [dot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ i, sign (b i) * (root i k * sumRoot b k)) =
    (∑ i, sign (b i) * root i k) * sumRoot b k
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma scalar_envelope (a b : Bool) (x : ℤ) :
    sign a * (3*x - 52*sign b) + 3*sign b*x ≤ max 52 (6*|x|-52) := by
  have h₁ : (52 : ℤ) ≤ max 52 (6*|x|-52) := le_max_left _ _
  have h₂ : 6*|x|-52 ≤ max 52 (6*|x|-52) := le_max_right _ _
  have h₃ := le_abs_self x
  have h₄ := neg_le_abs x
  cases a <;> cases b <;> simp only [sign, Bool.false_eq_true, ite_false, ite_true] <;> nlinarith

/-- The one-sign envelope bounds every deterministic Bell value. -/
theorem fourBell_le_envelope (a b : Signing) : fourBell a b ≤ envelope (sumRoot b) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset Setting))
    (fun i _ => scalar_envelope (a i) (b i) (dot (root i) (sumRoot b)))
  rw [Finset.sum_add_distrib, ← fourBell_rows] at h
  have hn : (∑ i, 3 * sign (b i) * dot (root i) (sumRoot b)) =
      3 * dot (sumRoot b) (sumRoot b) := by
    rw [← signed_pairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hn] at h
  unfold envelope
  omega

end Lemmata.ModifiedE8Bell
