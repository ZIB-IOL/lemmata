module

public import Lemmata.ModifiedE8Bell.Data
public import Mathlib.Data.Fintype.Lattice

public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

lemma sign_times (b : Bool) (x : ℤ) : sign b * x = x - 2 * (if b then 0 else x) := by
  cases b <;> simp [sign] <;> ring

lemma sum_sign (a : Signing) (f : Setting → ℤ) (c : ℤ) (h : ∑ i, f i = 2*c) :
    (∑ i, sign (a i) * f i) = 2 * (c - ∑ i, if a i then 0 else f i) := by
  simp_rw [sign_times]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h]
  ring

lemma sum_gap (a : Signing) (k : Coordinate) :
    (∑ i, sign (a i) * rootGap i k) = 2 * gap a k :=
  sum_sign a _ _ (root_gap_total k)

lemma sumRoot_gap (a : Signing) (j : Coordinate) :
    sumRoot a j = 2 * coordinates (gap a) j := by
  calc
    sumRoot a j = ∑ i, sign (a i) * coordinates (rootGap i) j := by
      simp only [sumRoot, root_reconstruction]
    _ = ∑ k, basis j k * (∑ i, sign (a i) * rootGap i k) := by
      simp only [coordinates, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 2 * coordinates (gap a) j := by
      simp_rw [sum_gap]
      simp only [coordinates, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma sign_mul_le_abs (b : Bool) (x : ℤ) : sign b * x ≤ |x| := by
  cases b <;> simp only [sign, Bool.false_eq_true, ite_false, ite_true, neg_mul, one_mul]
  · exact neg_le_abs x
  · exact le_abs_self x

lemma last_coordinate_le (a : Signing) : coordinates (gap a) 7 ≤ 46 := by
  have h : sumRoot a 7 ≤ 92 := by
    calc
      sumRoot a 7 ≤ ∑ i, |root i 7| := Finset.sum_le_sum (fun i _ => sign_mul_le_abs _ _)
      _ = 92 := root_coordinate_bound
  rw [sumRoot_gap] at h
  omega

lemma sign_reflect (k : Coordinate) (a : Signing) (i : Setting) :
    sign (reflect k a i) = reflectionSign k i * sign (a (reflectionIndex k i)) := by
  unfold reflect reflectionSign
  cases h : reflectionFlip k i <;> cases ha : a (reflectionIndex k i) <;> simp [h, ha, sign]

def reflectionEquiv (k : Coordinate) : Equiv.Perm Setting where
  toFun := reflectionIndex k
  invFun := reflectionIndex k
  left_inv := reflection_involution k
  right_inv := reflection_involution k

lemma reflected_sum (k : Coordinate) (a : Signing) (f : Setting → ℤ) :
    (∑ i, sign (reflect k a i) * f i) =
      ∑ i, sign (a i) * (reflectionSign k i * f (reflectionIndex k i)) := by
  apply Fintype.sum_equiv (reflectionEquiv k)
  intro i
  change sign (reflect k a i) * f i =
    sign (a (reflectionIndex k i)) *
      (reflectionSign k (reflectionIndex k i) * f (reflectionIndex k (reflectionIndex k i)))
  rw [sign_reflect, reflection_involution, reflection_flip_involution]
  ring

lemma height_reflect (k : Coordinate) (a : Signing) :
    height (reflect k a) = height a - 2 * wallScale k * gap a k := by
  rw [height, reflected_sum]
  simp_rw [reflection_height, mul_sub]
  rw [Finset.sum_sub_distrib]
  have h : (∑ i, sign (a i) * (wallScale k * rootGap i k)) =
      wallScale k * (∑ i, sign (a i) * rootGap i k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h, sum_gap]
  change height a - wallScale k * (2 * gap a k) = _
  ring

lemma fourBell_reflect (k : Coordinate) (a b : Signing) :
    fourBell (reflect k a) (reflect k b) = fourBell a b := by
  unfold fourBell
  apply Fintype.sum_equiv (reflectionEquiv k)
  intro i
  apply Fintype.sum_equiv (reflectionEquiv k)
  intro j
  change sign (reflect k a i) * sign (reflect k b j) * fourMatrix i j =
    sign (a (reflectionIndex k i)) * sign (b (reflectionIndex k j)) *
      fourMatrix (reflectionIndex k i) (reflectionIndex k j)
  have hm := reflection_matrix k (reflectionIndex k i) (reflectionIndex k j)
  simp only [reflection_involution, reflection_flip_involution] at hm
  rw [sign_reflect, sign_reflect, ← hm]
  ring

/-- Maximize the integer height among all pairs with the original Bell score.
A negative chamber gap would permit a score-preserving height increase. -/
theorem exists_chamber_pair (a b : Signing) :
    ∃ c d : Signing, fourBell c d = fourBell a b ∧ ∀ k, 0 ≤ gap d k := by
  classical
  let T := {cd : Signing × Signing // fourBell cd.1 cd.2 = fourBell a b}
  letI : Nonempty T := ⟨⟨(a,b),rfl⟩⟩
  obtain ⟨⟨⟨c,d⟩,heq⟩,hmax⟩ := Finite.exists_max (fun cd : T => height cd.val.2)
  refine ⟨c,d,heq,?_⟩
  intro k
  have hm : fourBell (reflect k c) (reflect k d) = fourBell a b :=
    (fourBell_reflect k c d).trans heq
  have hi := hmax ⟨(reflect k c, reflect k d),hm⟩
  change height (reflect k d) ≤ height d at hi
  rw [height_reflect] at hi
  have hp : 0 < wallScale k := by unfold wallScale; split <;> norm_num
  nlinarith

end Lemmata.ModifiedE8Bell
