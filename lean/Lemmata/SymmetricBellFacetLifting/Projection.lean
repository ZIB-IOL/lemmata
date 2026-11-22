module

public import Lemmata.SymmetricBellCrossPolytope.Main

@[expose] public section
noncomputable section
open Set BigOperators
open scoped RealInnerProductSpace
namespace Lemmata.SymmetricBellFacetLifting

open SymmetricBellCrossPolytope

abbrev FourIndex := Fin 3 → Fin 4

private def idx (i : Fin 4) (x : FourIndex) := (gen i x).2

private def wrap (q : ℤ) : ℤ := (-1) ^ (q / 4).natAbs

private def weight (i : Fin 4) (x : FourIndex) : ℤ :=
  ![(1:ℤ),1,∏ n : Fin 3, wrap ((x n : ℤ) + if n.val = 0 then 1 else if n.val = 1 then -1 else 0),
    ∏ n : Fin 3, -(wrap (4-(x n : ℤ)))] i

private theorem wrap_cast (r : ℤ) : (wrap r : ℝ) = (-1 : ℝ) ^ (r / 4) := by
  simp only [wrap, neg_one_pow_eq_ite, neg_one_zpow_eq_ite, Int.natAbs_even]
  split <;> norm_num

private theorem weight_eq (i : Fin 4) (x : FourIndex) :
    (weight i x : ℝ) = (gen i x).1 := by
  fin_cases i
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · simp [weight, gen, gen3, shiftParty, reduceIdx, normIdx, wrap_cast]
  · simp [weight, gen, gen4, reduceIdx, normIdx, wrap_cast]

def rep (s : Fin 4) : FourIndex := ![0,0,s]

private def reverseSteps : Fin 4 → List (Fin 4) :=
  ![[0],[1,1],[2,2,2],[3]]

private def endOf : List (Fin 4) → FourIndex → FourIndex
  | [], x => x
  | i::is, x => endOf is (idx i x)

private theorem undo : ∀ (i : Fin 4) (x : FourIndex),
    endOf (reverseSteps i) (idx i x) = x := by decide +kernel

private theorem inj (i : Fin 4) : Function.Injective (idx i) :=
  (show Function.LeftInverse (endOf (reverseSteps i)) (idx i) from undo i).injective

private theorem actionAt (i : Fin 4) (p : Tensor 3 4) (x : FourIndex) :
    act (gen i) p (idx i x) = (weight i x : ℝ) * p x := by
  classical
  change (∑ z : FourIndex, if idx i z = idx i x then (gen i z).1 * p z else 0) = _
  rw [Finset.sum_eq_single x, ite_eq_left rfl, weight_eq]
  · intro y _ h
    exact ite_eq_right (fun e => h (inj i e))
  · simp

private def wordSign : List (Fin 4) → FourIndex → ℤ
  | [], _ => 1
  | i::is, x => weight i x * wordSign is (idx i x)

private theorem sign_sq : ∀ (i : Fin 4) (x : FourIndex),
    weight i x * weight i x = 1 := by decide +kernel

private theorem along (p : Tensor 3 4) (hp : p ∈ symSub 3 4) (w : List (Fin 4))
    (x : FourIndex) : p x = (wordSign w x : ℝ) * p (endOf w x) := by
  induction w generalizing x with
  | nil => simp [wordSign,endOf]
  | cons i w ih =>
    have h := congrArg (fun q : Tensor 3 4 => q (idx i x)) (hp i)
    change act _ p (idx i x) = p (idx i x) at h
    rw [actionAt] at h
    have hsq : (weight i x : ℝ) * (weight i x : ℝ) = 1 := by exact_mod_cast sign_sq i x
    simp only [wordSign, endOf, Int.cast_mul]
    rw [mul_assoc, ← ih (idx i x), ← h, ← mul_assoc, hsq, one_mul]

/-- Integer orbit weights for the two nonvanishing even antiperiodic classes. -/
def fourCoeff (r : Fin 2) (x : FourIndex) : ℤ :=
  let n := (x 0).val + (x 1).val + (x 2).val
  (-1)^ (n / 4) * (if n % 4 = r.val then 1 else if r = 1 ∧ n % 4 = 3 then -1 else 0)

def fourBasis (r : Fin 2) : Tensor 3 4 :=
  WithLp.toLp 2 (fun x => (fourCoeff r x : ℝ))

private theorem equivariance : ∀ (r : Fin 2) (i : Fin 4) (x : FourIndex),
    weight i x * fourCoeff r x = fourCoeff r (idx i x) := by decide +kernel

theorem fourBasis_fixed (r : Fin 2) : fourBasis r ∈ symSub 3 4 := by
  intro i
  apply PiLp.ext
  intro y
  obtain ⟨x, rfl⟩ := Finite.surjective_of_injective (inj i) y
  rw [actionAt]
  change (weight i x : ℝ) * (fourCoeff r x : ℝ) = (fourCoeff r (idx i x) : ℝ)
  exact_mod_cast equivariance r i x

/-- A generator word taking each tuple to its signed total-index representative. -/
private def toRep (x : FourIndex) : List (Fin 4) :=
  match (x 0).val * 16 + (x 1).val * 4 + (x 2).val with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => [3]
  | 4 => [1]
  | 5 => [3,2,1,2]
  | 6 => [1,1,3,2,1]
  | 7 => [0,1,2]
  | 8 => [1]
  | 9 => [3,2,1,2]
  | 10 => [0,1,2,2]
  | 11 => [2,1,2]
  | 12 => [1,3]
  | 13 => [1,1,2]
  | 14 => [1,1,2,1]
  | 15 => [2,1,2]
  | 16 => [0,1]
  | 17 => [1,2,0,1]
  | 18 => [1,0,3,2,1]
  | 19 => [1,2]
  | 20 => [2,0,1]
  | 21 => [2,1,3,2,1]
  | 22 => [2,1,2,2]
  | 23 => [1,2]
  | 24 => [3,2,1]
  | 25 => [0,2,1,0,2]
  | 26 => [0,1,2,2]
  | 27 => [1,2]
  | 28 => [0,2]
  | 29 => [0,2]
  | 30 => [0,2]
  | 31 => [3,2]
  | 32 => [0,1]
  | 33 => [1,3,2,1]
  | 34 => [1,2,2]
  | 35 => [1,2,1]
  | 36 => [0,3,2,1]
  | 37 => [2,1,0,2]
  | 38 => [1,2,2]
  | 39 => [0,1,2]
  | 40 => [2,2]
  | 41 => [2,2]
  | 42 => [2,2]
  | 43 => [2,2,3]
  | 44 => [0,2,1]
  | 45 => [1,1,2]
  | 46 => [1,2,2,3]
  | 47 => [0,2,0,1,2]
  | 48 => [0,1,3]
  | 49 => [1,0,2]
  | 50 => [1,0,2,1]
  | 51 => [1,2,1]
  | 52 => [2]
  | 53 => [2]
  | 54 => [2]
  | 55 => [2,3]
  | 56 => [2,1]
  | 57 => [1,0,2]
  | 58 => [0,1,2,2,3]
  | 59 => [2,0,1,2]
  | 60 => [2,1]
  | 61 => [1,3,2]
  | 62 => [2,0,1,2,2]
  | 63 => [2,2,1,2]
  | _ => []

private theorem reduceTable : ∀ x : FourIndex,
    (endOf (toRep x) x = rep 0 ∧ fourCoeff 0 x = wordSign (toRep x) x ∧ fourCoeff 1 x = 0) ∨
    (endOf (toRep x) x = rep 1 ∧ fourCoeff 1 x = wordSign (toRep x) x ∧ fourCoeff 0 x = 0) ∨
    (endOf (toRep x) x = rep 2 ∧ fourCoeff 0 x = 0 ∧ fourCoeff 1 x = 0) := by decide +kernel

/-- Two signed sum-orbits span the archive's actual common fixed space. -/
theorem four_fixed_expansion (p : Tensor 3 4) (hp : p ∈ symSub 3 4) :
    p = p (rep 0) • fourBasis 0 + p (rep 1) • fourBasis 1 := by
  have h := along p hp [3] (rep 2)
  have hword : wordSign [3] (rep 2) = -1 ∧ endOf [3] (rep 2) = rep 2 := by decide +kernel
  rw [hword.1, hword.2] at h
  have hzero : p (rep 2) = 0 := by push_cast at h; linarith
  apply PiLp.ext
  intro x
  have hw := along p hp (toRep x) x
  change p x = p (rep 0) * (fourCoeff 0 x : ℝ) + p (rep 1) * (fourCoeff 1 x : ℝ)
  rcases reduceTable x with ⟨he,hs,hz⟩ | ⟨he,hs,hz⟩ | ⟨he,h0,h1⟩
  · rw [he] at hw
    rw [hw, hs, hz]
    simp [mul_comm]
  · rw [he] at hw
    rw [hw, hs, hz]
    simp [mul_comm]
  · rw [he, hzero, mul_zero] at hw
    simp [hw, h0, h1]

/-- The orthogonal projection preserves both signed orbit sums. -/
theorem four_inner_project (r : Fin 2) (p : Tensor 3 4) :
    (inner ℝ (Gamma 3 4 p) (fourBasis r)) = inner ℝ p (fourBasis r) := by
  have h := Submodule.starProjection_inner_eq_zero (K := symSub 3 4) p _ (fourBasis_fixed r)
  change inner ℝ (p - Gamma 3 4 p) (fourBasis r) = 0 at h
  rw [inner_sub_left] at h
  exact (sub_eq_zero.mp h).symm

end Lemmata.SymmetricBellFacetLifting
