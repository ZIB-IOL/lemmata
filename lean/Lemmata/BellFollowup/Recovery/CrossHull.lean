module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
The symmetric convex hull of the coordinate vectors has the coordinate ℓ¹
unit ball as its underlying set. The nonempty hypothesis allows any unused
convex-combination weight to be placed at the origin.
-/

namespace Lemmata.BellFollowup.Recovery.CrossHull

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate vector supported at a single index, with arbitrary value. -/
def axis (i : ι) (r : ℝ) : ι → ℝ := fun j => if i = j then r else 0

/-- The positive and negative coordinate unit vectors. -/
def signedAxes (ι : Type*) [DecidableEq ι] : Set (ι → ℝ) :=
  {x | ∃ i : ι, x = axis i 1 ∨ x = axis i (-1)}

omit [Fintype ι] in
private theorem axis_mem (i : ι) :
    axis i 1 ∈ convexHull ℝ (signedAxes ι) ∧
    axis i (-1) ∈ convexHull ℝ (signedAxes ι) :=
  ⟨subset_convexHull ℝ _ ⟨i, Or.inl rfl⟩,
   subset_convexHull ℝ _ ⟨i, Or.inr rfl⟩⟩

omit [DecidableEq ι] in
private theorem l1_convex : Convex ℝ {x : ι → ℝ | (∑ i, |x i|) ≤ 1} := by
  intro x hx y hy a b ha hb hab
  change (∑ i, |x i|) ≤ 1 at hx
  change (∑ i, |y i|) ≤ 1 at hy
  change (∑ i, |a * x i + b * y i|) ≤ 1
  calc
    _ ≤ ∑ i, (a * |x i| + b * |y i|) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
        abs_add_le (a * x i) (b * y i)
    _ = a * (∑ i, |x i|) + b * (∑ i, |y i|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by simpa using hab

/-- The closed coordinate ℓ¹ unit ball is the convex hull of the signed axes. -/
theorem convexHull_signedAxes [Nonempty ι] :
    convexHull ℝ (signedAxes ι) = {x : ι → ℝ | (∑ i, |x i|) ≤ 1} := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ l1_convex
    rintro x ⟨i, rfl | rfl⟩ <;>
      change (∑ j, |axis i _ j|) ≤ 1 <;>
      simp [axis, apply_ite abs]
  · intro x hx
    change (∑ i, |x i|) ≤ 1 at hx
    let H := convexHull ℝ (signedAxes ι)
    have hH : Convex ℝ H := convex_convexHull ℝ _
    have hzero : (0 : ι → ℝ) ∈ H := by
      let i : ι := Classical.choice ‹Nonempty ι›
      have hz := hH (axis_mem i).1 (axis_mem i).2
        (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
        (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
      have he : ((1/2 : ℝ) • axis i 1 + (1/2 : ℝ) • axis i (-1)) = 0 := by
        funext j
        by_cases hij : i = j <;> norm_num [axis, hij]
      rwa [he] at hz
    let z : Option ι → ι → ℝ
      | none => 0
      | some i => if 0 ≤ x i then axis i 1 else axis i (-1)
    let w : Option ι → ℝ
      | none => 1 - ∑ i, |x i|
      | some i => |x i|
    let t := Finset.insertNone (Finset.univ : Finset ι)
    have hw : ∀ i ∈ t, 0 ≤ w i := by
      intro i _
      cases i with
      | none => exact sub_nonneg.mpr hx
      | some i => exact abs_nonneg (x i)
    have hsum : ∑ i ∈ t, w i = 1 := by simp [t, w]
    have hz : ∀ i ∈ t, z i ∈ H := by
      intro i _
      cases i with
      | none => exact hzero
      | some i =>
        by_cases hi : 0 ≤ x i
        · simpa [z, hi] using (axis_mem i).1
        · simpa [z, hi] using (axis_mem i).2
    have hc := hH.sum_mem hw hsum hz
    have hterm (i : ι) : w (.some i) • z (.some i) = axis i (x i) := by
      funext j
      by_cases hij : i = j
      · subst j
        by_cases hi : 0 ≤ x i
        · simp [w, z, axis, hi, abs_of_nonneg hi]
        · simp [w, z, axis, hi, abs_of_neg (lt_of_not_ge hi)]
      · by_cases hi : 0 ≤ x i <;> simp [w, z, axis, hi, hij]
    have hdecomp : (∑ i ∈ t, w i • z i) = x := by
      rw [show t = Finset.insertNone (Finset.univ : Finset ι) from rfl,
        Finset.sum_insertNone]
      change w none • (0 : ι → ℝ) + (∑ i, w (some i) • z (some i)) = x
      simp only [smul_zero, zero_add, hterm]
      funext j
      simp [axis, Finset.sum_apply]
    simpa [hdecomp] using hc

end Lemmata.BellFollowup.Recovery.CrossHull
